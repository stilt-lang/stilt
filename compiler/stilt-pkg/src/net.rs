//! HTTPS for fetching (packages.fetching): a small HTTP/1.1 client over rustls. It trusts Mozilla's
//! roots, built in, so that a clean machine trusts what browsers do; the system's bundle of
//! certificates, where it has one; and the certificates of the file that `SSL_CERT_FILE` names,
//! as company networks need.

use std::fmt::Write as _;
use std::io::{Read as _, Write as _};
use std::net::{TcpStream, ToSocketAddrs as _};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use rustls::pki_types::pem::PemObject as _;
use rustls::pki_types::{CertificateDer, ServerName};
use rustls::{ClientConfig, ClientConnection, RootCertStore, StreamOwned};

mod framing;

/// The bundles of certificates that systems keep, at least one of which most have.
const BUNDLES: [&str; 4] = [
    "/etc/ssl/certs/ca-certificates.crt",
    "/etc/pki/tls/certs/ca-bundle.crt",
    "/etc/ssl/ca-bundle.pem",
    "/etc/ssl/cert.pem",
];

/// How long a connection or a read may wait.
const PATIENCE: Duration = Duration::from_secs(30);

/// The largest answer taken from a server, as large as the largest object a pack may hold.
const MAX_ANSWER: usize = crate::git::MAX_OBJECT;

/// An answer: its status and its body.
#[derive(Debug)]
pub(crate) struct Response {
    pub(crate) status: u16,
    pub(crate) body: Vec<u8>,
}

/// `GET url`, following redirections.
pub(crate) fn get(url: &str) -> Result<Response, String> {
    request(url, None)
}

/// `POST url` with `body` of the type `kind`, following redirections.
pub(crate) fn post(url: &str, kind: &str, body: &[u8]) -> Result<Response, String> {
    request(url, Some((kind, body)))
}

fn request(url: &str, body: Option<(&str, &[u8])>) -> Result<Response, String> {
    let mut url = url.to_owned();
    for _ in 0..5 {
        let response = once(&url, body)?;
        match (response.status, &response.location) {
            (301 | 302 | 303 | 307 | 308, Some(location)) => {
                url = redirected(&url, location);
            }
            _ => {
                return Ok(Response {
                    status: response.status,
                    body: response.body,
                });
            }
        }
    }
    Err("it redirects too often".to_owned())
}

/// Where a redirection to `location` from `url` leads.
fn redirected(url: &str, location: &str) -> String {
    if location.starts_with("https://") {
        return location.to_owned();
    }
    let rest = url.trim_start_matches("https://");
    let host = rest.split('/').next().unwrap_or(rest);
    format!("https://{host}{location}")
}

/// One request, over a connection of its own.
fn once(url: &str, body: Option<(&str, &[u8])>) -> Result<framing::Answer, String> {
    let rest = url
        .strip_prefix("https://")
        .ok_or_else(|| format!("{url} isn't an HTTPS URL"))?;
    let (authority, path) = rest.split_at(rest.find('/').unwrap_or(rest.len()));
    let (host, port) = match authority.split_once(':') {
        Some((host, port)) => (host, port.parse().map_err(|_| "a malformed port")?),
        None => (authority, 443),
    };
    let tcp = connect(host, port)?;
    let name = ServerName::try_from(host.to_owned()).map_err(|e| format!("{host}: {e}"))?;
    let connection = ClientConnection::new(config()?, name).map_err(|e| e.to_string())?;
    let mut stream = StreamOwned::new(connection, tcp);
    let path = if path.is_empty() { "/" } else { path };
    let method = if body.is_some() { "POST" } else { "GET" };
    let mut head = format!(
        "{method} {path} HTTP/1.1\r\nHost: {authority}\r\nUser-Agent: stilt/{}\r\n\
         Accept: */*\r\nConnection: close\r\n",
        env!("CARGO_PKG_VERSION")
    );
    if let Some((kind, bytes)) = body {
        let _ = write!(
            head,
            "Content-Type: {kind}\r\nContent-Length: {}\r\n",
            bytes.len()
        );
    }
    head.push_str("\r\n");
    let sent = stream.write_all(head.as_bytes()).and_then(|()| match body {
        Some((_, bytes)) => stream.write_all(bytes),
        None => Ok(()),
    });
    sent.and_then(|()| stream.flush())
        .map_err(|e| tls_failure(host, &e))?;
    let mut received = Vec::new();
    let limit = u64::try_from(MAX_ANSWER)
        .unwrap_or(u64::MAX)
        .saturating_add(1);
    if let Err(e) = (&mut stream).take(limit).read_to_end(&mut received) {
        // A server may close without TLS's close notification: the framing says whether the
        // answer is whole.
        if e.kind() != std::io::ErrorKind::UnexpectedEof || received.is_empty() {
            return Err(tls_failure(host, &e));
        }
    }
    if received.len() > MAX_ANSWER {
        return Err(format!("{host} answers with more than 1 GiB"));
    }
    framing::answer(&received)
}

fn connect(host: &str, port: u16) -> Result<TcpStream, String> {
    let addresses = (host, port)
        .to_socket_addrs()
        .map_err(|e| format!("{host} can't be found: {e}"))?;
    let mut last = format!("{host} has no address");
    for address in addresses {
        match TcpStream::connect_timeout(&address, PATIENCE) {
            Ok(tcp) => {
                let _ = tcp.set_read_timeout(Some(PATIENCE));
                let _ = tcp.set_write_timeout(Some(PATIENCE));
                return Ok(tcp);
            }
            Err(e) => last = format!("{host}:{port} refuses the connection: {e}"),
        }
    }
    Err(last)
}

fn tls_failure(host: &str, e: &std::io::Error) -> String {
    match e
        .get_ref()
        .and_then(|inner| inner.downcast_ref::<rustls::Error>())
    {
        Some(rustls::Error::InvalidCertificate(why)) => format!(
            "the certificate of {host} doesn't verify ({why:?}): stilt trusts Mozilla's roots, \
             the system's, and those of the file that SSL_CERT_FILE names"
        ),
        _ => format!("the connection to {host} failed: {e}"),
    }
}

/// The configuration of every connection, made once.
fn config() -> Result<Arc<ClientConfig>, String> {
    static CONFIG: OnceLock<Result<Arc<ClientConfig>, String>> = OnceLock::new();
    CONFIG
        .get_or_init(|| {
            let provider = Arc::new(rustls::crypto::ring::default_provider());
            let config = ClientConfig::builder_with_provider(provider)
                .with_safe_default_protocol_versions()
                .map_err(|e| e.to_string())?
                .with_root_certificates(roots())
                .with_no_client_auth();
            Ok(Arc::new(config))
        })
        .clone()
}

/// Mozilla's roots, the system's bundle, and the certificates of `SSL_CERT_FILE`.
fn roots() -> RootCertStore {
    let mut roots = RootCertStore::empty();
    roots.extend(webpki_roots::TLS_SERVER_ROOTS.iter().cloned());
    let extra = std::env::var_os("SSL_CERT_FILE").map(std::path::PathBuf::from);
    let files = BUNDLES.iter().map(std::path::PathBuf::from).chain(extra);
    for file in files.filter(|f| f.is_file()) {
        if let Ok(certificates) = CertificateDer::pem_file_iter(&file) {
            for certificate in certificates.flatten() {
                let _ = roots.add(certificate);
            }
        }
    }
    roots
}
