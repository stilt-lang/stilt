// json: writes a JSON document of 20000 records, parses it back into a tree with a
// recursive-descent parser, and sums what the tree holds.

indirect enum Json {
    case null
    case bool(Bool)
    case num(Int)
    case text(String)
    case array([Json])
    case object([(String, Json)])
}

func document(_ n: Int) -> String {
    var parts: [String] = []
    for i in 0..<n {
        let active = i % 3 == 0 ? "true" : "false"
        let note = i % 5 == 0 ? "null" : "\"line\\none \\\"\(i)\\\"\""
        parts.append(
            "{\"id\": \(i), \"name\": \"item\(i)\", \"active\": \(active), \"tags\": [\"a\", \"b\(i % 4)\"], \"point\": {\"x\": \(i % 7), \"y\": [1, 2, \(i % 11)]}, \"note\": \(note)}"
        )
    }
    return "[" + parts.joined(separator: ", ") + "]"
}

struct Parser {
    let text: [UInt8]
    var pos = 0

    mutating func skipSpace() {
        while pos < text.count && (text[pos] == 32 || text[pos] == 10) { pos += 1 }
    }

    mutating func string() -> String {
        pos += 1
        var bytes: [UInt8] = []
        var start = pos
        while text[pos] != 34 {
            if text[pos] == 92 {
                bytes.append(contentsOf: text[start..<pos])
                bytes.append(text[pos + 1] == 110 ? 10 : text[pos + 1])
                pos += 2
                start = pos
            } else {
                pos += 1
            }
        }
        bytes.append(contentsOf: text[start..<pos])
        pos += 1
        return String(decoding: bytes, as: UTF8.self)
    }

    mutating func number() -> Int {
        var n = 0
        while pos < text.count && text[pos] >= 48 && text[pos] <= 57 {
            n = n * 10 + Int(text[pos] - 48)
            pos += 1
        }
        return n
    }

    mutating func value() -> Json {
        skipSpace()
        switch text[pos] {
        case 123:
            pos += 1
            var fields: [(String, Json)] = []
            skipSpace()
            while text[pos] != 125 {
                skipSpace()
                let key = string()
                skipSpace()
                pos += 1
                fields.append((key, value()))
                skipSpace()
                if text[pos] == 44 { pos += 1 }
            }
            pos += 1
            return .object(fields)
        case 91:
            pos += 1
            var items: [Json] = []
            skipSpace()
            while text[pos] != 93 {
                items.append(value())
                skipSpace()
                if text[pos] == 44 { pos += 1 }
            }
            pos += 1
            return .array(items)
        case 34: return .text(string())
        case 116: pos += 4; return .bool(true)
        case 102: pos += 5; return .bool(false)
        case 110: pos += 4; return .null
        default: return .num(number())
        }
    }
}

struct Totals {
    var numbers = 0, texts = 0, trues = 0, nulls = 0, nodes = 0

    mutating func add(_ json: Json) {
        nodes += 1
        switch json {
        case .null: nulls += 1
        case let .bool(b): if b { trues += 1 }
        case let .num(n): numbers += n
        case let .text(s): texts += s.utf8.count
        case let .array(items): for item in items { add(item) }
        case let .object(fields):
            for (key, item) in fields {
                texts += key.utf8.count
                add(item)
            }
        }
    }
}

let source = document(20000)
var parser = Parser(text: Array(source.utf8))
var totals = Totals()
totals.add(parser.value())
print("\(source.utf8.count) bytes, \(totals.nodes) nodes")
print("numbers \(totals.numbers), text \(totals.texts), true \(totals.trues), null \(totals.nulls)")
