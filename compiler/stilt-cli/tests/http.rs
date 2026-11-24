//! `std.http`'s client and server against a peer of the test's own on 127.0.0.1
//! (std.http-client and std.http-server), which the conformance suite can't give them: a
//! program's meaning is its sequential run, in which a client that waits for its answer and a
//! server that waits for its request can't both run. `http.get` and `http.post` reach a server
//! that the test runs on a thread and read its answer, and `http.serve` answers each request of
//! the test's own client, until the test stops it.

mod common;

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::process::{Command, Stdio};
use std::thread;

use common::{file, stdout};

/// Serves one connection on a thread: reads its request to the blank line and the body that its
/// `Content-Length` announces, answers with `answer`, and gives back the request it read.
fn serve_once(answer: &'static str) -> (u16, thread::JoinHandle<String>) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("a port on 127.0.0.1");
    let port = listener.local_addr().expect("an address").port();
    let server = thread::spawn(move || {
        let (stream, _) = listener.accept().expect("a connection");
        let mut reader = BufReader::new(stream);
        let mut request = String::new();
        let mut length = 0;
        loop {
            let mut line = String::new();
            reader.read_line(&mut line).expect("a line");
            if let Some(n) = line.to_ascii_lowercase().strip_prefix("content-length:") {
                length = n.trim().parse().expect("a length");
            }
            request.push_str(&line);
            if line == "\r\n" {
                break;
            }
        }
        let mut body = vec![0; length];
        reader.read_exact(&mut body).expect("the body");
        request.push_str(&String::from_utf8_lossy(&body));
        reader
            .get_mut()
            .write_all(answer.as_bytes())
            .expect("the answer is written");
        request
    });
    (port, server)
}

#[test]
fn get_and_post_reach_a_server_and_read_its_answer() {
    let (port, server) = serve_once(
        "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nTransfer-Encoding: chunked\r\n\r\n\
         3\r\nhi \r\n5\r\nthere\r\n0\r\n\r\n",
    );
    let source = format!(
        "use std.http\n\nfn main() / {{io, raise<http.Error>}} {{\n  let r = try \
         http.get(\"http://127.0.0.1:{port}/greet?who=you#top\")\n  print(\"{{r.status}} \
         {{r.header(\"content-type\")}} {{r.body}}\")\n}}\n"
    );
    let output = common::stilt(
        &["run", file("http", "get", &source).to_str().unwrap()],
        None,
    );
    assert_eq!(stdout(&output), "200 Some(\"text/plain\") hi there\n");
    let request = server.join().expect("the server ends");
    assert!(
        request.starts_with("GET /greet?who=you HTTP/1.1\r\n"),
        "{request}"
    );
    assert!(
        request.contains(&format!("Host: 127.0.0.1:{port}\r\n")),
        "{request}"
    );
    assert!(request.contains("Connection: close\r\n"), "{request}");

    let (port, server) = serve_once("HTTP/1.1 201 Created\r\nContent-Length: 2\r\n\r\nok");
    // The body, `{"a": 1}`, is written with its brace escaped, which would begin a splice.
    let body = r#""\{\"a\": 1}""#;
    let source = format!(
        "use std.http\n\nfn main() / {{io, raise<http.Error>}} {{\n  let r = try \
         http.post(\"http://127.0.0.1:{port}\", \"application/json\", {body})\n  \
         print(\"{{r.status}} {{r.body}}\")\n}}\n"
    );
    let output = common::stilt(
        &["run", file("http", "post", &source).to_str().unwrap()],
        None,
    );
    assert_eq!(stdout(&output), "201 ok\n");
    let request = server.join().expect("the server ends");
    assert!(request.starts_with("POST / HTTP/1.1\r\n"), "{request}");
    assert!(
        request.contains("Content-Type: application/json\r\n"),
        "{request}"
    );
    assert!(
        request.ends_with("Content-Length: 8\r\n\r\n{\"a\": 1}"),
        "{request}"
    );
}

#[test]
fn serve_answers_each_request_in_turn() {
    let source = "use std.http\nuse std.io\nuse std.net\n\nfn main() / {io, raise<io.IoError>} {\n  \
                  var listener = try net.listen(\"127.0.0.1\", 0)\n  print(\"{listener.port()}\")\n  \
                  http.serve(inout listener, |r| http.Response.new(200, \"{r.method} {r.target} \
                  {r.body}\"))\n}\n";
    let path = file("http", "serve", source);
    let mut child = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["run", path.to_str().unwrap()])
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("stilt runs");
    let mut out = BufReader::new(child.stdout.take().expect("a pipe"));
    let mut port = String::new();
    out.read_line(&mut port).expect("the port");
    let port: u16 = port.trim().parse().expect("a port");
    for (request, answer) in [
        ("GET /a HTTP/1.1\r\nHost: x\r\n\r\n", "GET /a "),
        (
            "PUT /b HTTP/1.1\r\nContent-Length: 3\r\n\r\nabc",
            "PUT /b abc",
        ),
        ("no request line\r\n\r\n", ""),
    ] {
        let mut stream = TcpStream::connect(("127.0.0.1", port)).expect("the server listens");
        stream
            .write_all(request.as_bytes())
            .expect("the request is written");
        let mut response = String::new();
        stream.read_to_string(&mut response).expect("the response");
        let status = if answer.is_empty() {
            "400 Bad Request"
        } else {
            "200 OK"
        };
        assert!(
            response.starts_with(&format!("HTTP/1.1 {status}\r\n")),
            "{response}"
        );
        assert!(response.contains("Connection: close\r\n"), "{response}");
        assert!(
            response.ends_with(&format!("\r\n\r\n{answer}")),
            "{response}"
        );
    }
    let _ = child.kill();
    let _ = child.wait();
}
