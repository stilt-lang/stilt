//! A server of test repositories over HTTPS, as git's smart HTTP protocol serves them: each
//! request answered by `git upload-pack`, as `git http-backend` answers it, over TLS with a
//! certificate that a certificate authority of the test's own signs.

use std::fs;
use std::io::{Read as _, Write as _};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;

use rcgen::{BasicConstraints, CertificateParams, DnType, IsCa, KeyPair};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{ServerConfig, ServerConnection, StreamOwned};

/// A server, listening on `localhost` at `port`, whose certificate authority's certificate is
/// in the file `authority`.
pub(crate) struct Server {
    pub(crate) port: u16,
    pub(crate) authority: PathBuf,
}

/// Serves the repositories under `repos`, each at `/NAME`, writing the authority's certificate
/// in `dir`.
pub(crate) fn serve(repos: &Path, dir: &Path) -> Server {
    let ca_key = KeyPair::generate().expect("a key");
    let mut ca = CertificateParams::new(Vec::<String>::new()).expect("parameters");
    ca.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
    ca.distinguished_name
        .push(DnType::CommonName, "stilt test authority");
    let ca = ca
        .self_signed(&ca_key)
        .expect("the authority's certificate");
    let key = KeyPair::generate().expect("a key");
    let params = CertificateParams::new(vec!["localhost".to_owned()]).expect("parameters");
    let certificate = params
        .signed_by(&key, &ca, &ca_key)
        .expect("the server's certificate");
    let authority = dir.join("authority.pem");
    fs::write(&authority, ca.pem()).expect("the certificate can be written");
    let provider = Arc::new(rustls::crypto::ring::default_provider());
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key.serialize_der()));
    let config = ServerConfig::builder_with_provider(provider)
        .with_safe_default_protocol_versions()
        .expect("versions")
        .with_no_client_auth()
        .with_single_cert(vec![CertificateDer::from(certificate.der().to_vec())], key)
        .expect("a configuration");
    let config = Arc::new(config);
    let listener = TcpListener::bind("127.0.0.1:0").expect("a port");
    let port = listener.local_addr().expect("an address").port();
    let repos = repos.to_path_buf();
    std::thread::spawn(move || {
        for tcp in listener.incoming().flatten() {
            let (config, repos) = (config.clone(), repos.clone());
            std::thread::spawn(move || answer(tcp, config, &repos));
        }
    });
    Server { port, authority }
}

/// Answers one request, as git's smart HTTP protocol does.
fn answer(tcp: TcpStream, config: Arc<ServerConfig>, repos: &Path) {
    let Ok(connection) = ServerConnection::new(config) else {
        return;
    };
    let mut tls = StreamOwned::new(connection, tcp);
    let Some((target, body)) = request(&mut tls) else {
        return;
    };
    let (path, _) = target.split_once('?').unwrap_or((&target, ""));
    let (repo, endpoint) = path
        .trim_start_matches('/')
        .split_once('/')
        .unwrap_or(("", ""));
    let dir = repos.join(repo);
    let (status, kind, chunked, out) = match endpoint {
        _ if repo.is_empty() || !dir.is_dir() => ("404 Not Found", "text/plain", false, Vec::new()),
        "info/refs" => {
            let mut out = b"001e# service=git-upload-pack\n0000".to_vec();
            out.extend(upload_pack(&dir, &["--advertise-refs"], &[]));
            (
                "200 OK",
                "application/x-git-upload-pack-advertisement",
                false,
                out,
            )
        }
        "git-upload-pack" => {
            let out = upload_pack(&dir, &[], &body);
            ("200 OK", "application/x-git-upload-pack-result", true, out)
        }
        _ => ("404 Not Found", "text/plain", false, Vec::new()),
    };
    let mut response =
        format!("HTTP/1.1 {status}\r\nContent-Type: {kind}\r\nConnection: close\r\n");
    if chunked {
        // A pack comes in chunks, as servers send what they make as they make it.
        response.push_str("Transfer-Encoding: chunked\r\n\r\n");
        let mut bytes = response.into_bytes();
        for chunk in out.chunks(4096) {
            bytes.extend(format!("{:x}\r\n", chunk.len()).into_bytes());
            bytes.extend(chunk);
            bytes.extend(b"\r\n");
        }
        bytes.extend(b"0\r\n\r\n");
        let _ = tls.write_all(&bytes);
    } else {
        response = format!("{response}Content-Length: {}\r\n\r\n", out.len());
        let _ = tls
            .write_all(response.as_bytes())
            .and_then(|()| tls.write_all(&out));
    }
    tls.conn.send_close_notify();
    let _ = tls.flush();
}

/// The target and the body of the request on `tls`.
fn request(tls: &mut StreamOwned<ServerConnection, TcpStream>) -> Option<(String, Vec<u8>)> {
    let mut received = Vec::new();
    let mut buffer = [0; 4096];
    let end = loop {
        if let Some(end) = received.windows(4).position(|w| w == b"\r\n\r\n") {
            break end;
        }
        let n = tls.read(&mut buffer).ok().filter(|&n| n > 0)?;
        received.extend_from_slice(&buffer[..n]);
    };
    let head = String::from_utf8_lossy(&received[..end]).into_owned();
    let target = head.lines().next()?.split(' ').nth(1)?.to_owned();
    let length = (head.lines())
        .filter_map(|l| l.split_once(':'))
        .find(|(name, _)| name.eq_ignore_ascii_case("content-length"))
        .and_then(|(_, value)| value.trim().parse().ok())
        .unwrap_or(0);
    let mut body = received[end + 4..].to_vec();
    while body.len() < length {
        let n = tls.read(&mut buffer).ok().filter(|&n| n > 0)?;
        body.extend_from_slice(&buffer[..n]);
    }
    Some((target, body))
}

/// What `git upload-pack --stateless-rpc` writes for the repository `dir`, given `input`.
fn upload_pack(dir: &Path, args: &[&str], input: &[u8]) -> Vec<u8> {
    let mut child = Command::new("git")
        .args(["upload-pack", "--stateless-rpc"])
        .args(args)
        .arg(dir)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("git runs");
    let mut stdin = child.stdin.take().expect("a pipe");
    let input = input.to_vec();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let output = child.wait_with_output().expect("git ends");
    let _ = writer.join();
    output.stdout
}
