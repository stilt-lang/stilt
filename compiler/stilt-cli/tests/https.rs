//! Fetching over HTTPS (packages.fetching and packages.dependencies): a repository that `HOST/PATH`
//! names, served by a server of the test's own on `localhost`, whose certificate authority the
//! command trusts through `SSL_CERT_FILE`, so that no test reaches the network. A fetch fills in
//! the highest tag and its hash; content unlike its hash is E0602; and a host that refuses the
//! connection, and a certificate that doesn't verify, are E0601.

mod repos;
mod serve;

use std::fs;
use std::path::Path;

use repos::{Place, codes, content_hash, message};

const CSV_TOML: &str = "[package]\nname = \"csv\"\n";
const ROWS: &str = "pub fn rows() -> i64 { 3 }\n";
const APP: &str = "use csv\n\nfn main() / io { print(\"{csv.rows()} rows\") }\n";

/// A place with a repository `csv`, tagged 1.0.0 and 1.1.0, served over HTTPS, and the files of
/// its 1.1.0.
fn served(name: &str) -> (Place, serve::Server, Vec<(&'static str, &'static str)>) {
    let place = Place::new(name);
    let repo = place.repo("csv");
    let two = vec![
        ("stilt.toml", CSV_TOML),
        (
            "src/main.lt",
            "pub fn rows() -> i64 { 3 }\n\npub fn cols() -> i64 { 2 }\n",
        ),
    ];
    repo.tag("1.0.0", &[("stilt.toml", CSV_TOML), ("src/main.lt", ROWS)]);
    repo.tag("1.1.0", &two);
    let server = serve::serve(&place.dir.join("repos"), &place.dir);
    (place, server, two)
}

fn app(place: &Place, entry: &str) -> std::path::PathBuf {
    let toml = format!("[package]\nname = \"app\"\n\n[dependencies]\n{entry}\n");
    place.program(&[("stilt.toml", &toml), ("src/main.lt", APP)])
}

fn check(place: &Place, app: &Path, roots: Option<&Path>) -> serde_json::Value {
    let output = place.stilt_trusting("home", &["check", "--json"], app, roots);
    serde_json::from_slice(&output.stdout).expect("check writes JSON")
}

#[test]
fn a_fetch_fills_in_the_highest_tag_and_runs() {
    let (place, server, two) = served("https_fetch");
    let from = format!("localhost:{}/csv", server.port);
    let app = app(&place, &format!("csv = {{ from = \"{from}\" }}"));
    let checked = check(&place, &app, Some(&server.authority));
    assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
    let hash = content_hash(&two);
    let written = fs::read_to_string(app.join("stilt.toml")).expect("the manifest");
    let filled = format!("csv = {{ from = \"{from}\", version = \"1.1.0\", hash = \"{hash}\" }}");
    assert!(written.contains(&filled), "{written}");
    let ran = place.stilt_trusting("home", &["run"], &app, Some(&server.authority));
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "3 rows\n", "{ran:?}");
}

#[test]
fn content_unlike_its_hash_over_https_is_e0602() {
    let (place, server, _) = served("https_mismatch");
    let from = format!("localhost:{}/csv", server.port);
    let wrong = content_hash(&[("stilt.toml", CSV_TOML)]);
    let app = app(
        &place,
        &format!("csv = {{ from = \"{from}\", version = \"1.0.0\", hash = \"{wrong}\" }}"),
    );
    let checked = check(&place, &app, Some(&server.authority));
    assert_eq!(codes(&checked), ["E0602"], "{checked}");
    let found = content_hash(&[("stilt.toml", CSV_TOML), ("src/main.lt", ROWS)]);
    let expected = format!(
        "`csv` 1.0.0, as https://{from} serves it, has the hash {found}, not the one pinned here"
    );
    assert_eq!(message(&checked, "E0602"), expected);
}

#[test]
fn a_host_that_refuses_and_a_certificate_that_doesnt_verify_are_e0601() {
    let (place, server, _) = served("https_unreachable");
    let closed = std::net::TcpListener::bind("127.0.0.1:0").expect("a port");
    let port = closed.local_addr().expect("an address").port();
    drop(closed);
    let refused = app(
        &place,
        &format!("csv = {{ from = \"127.0.0.1:{port}/csv\" }}"),
    );
    let checked = check(&place, &refused, Some(&server.authority));
    assert_eq!(codes(&checked), ["E0601"], "{checked}");
    assert!(
        message(&checked, "E0601").contains("refuses the connection"),
        "{checked}"
    );
    let untrusted = app(
        &place,
        &format!("csv = {{ from = \"localhost:{}/csv\" }}", server.port),
    );
    let checked = check(&place, &untrusted, None);
    assert_eq!(codes(&checked), ["E0601"], "{checked}");
    let why = message(&checked, "E0601");
    assert!(
        why.contains("the certificate of localhost doesn't verify"),
        "{why}"
    );
}
