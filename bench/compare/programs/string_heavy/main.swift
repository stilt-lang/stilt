// string-heavy: builds a text of words, then splits, searches, replaces, changes the case of
// and joins it.

import Foundation

var words: [String] = []
var x = 7
for _ in 0..<200000 {
    x = (x * 1103515245 + 12345) % 2147483648
    words.append("w\(x % 1000)")
}
let text = words.joined(separator: " ")
let parts = text.split(separator: " ", omittingEmptySubsequences: false)
var lengths = 0
var sevens = 0
for p in parts {
    lengths += p.utf8.count
    if p.hasSuffix("7") { sevens += 1 }
}
let replaced = text.replacingOccurrences(of: "w1", with: "one-")
let upper = replaced.uppercased()
let digits = upper.utf8.filter { $0 >= 48 && $0 <= 57 }.count
let found = upper.range(of: "ONE-99 ").map { upper.utf8.distance(from: upper.startIndex, to: $0.lowerBound) } ?? -1
let lines = text.replacingOccurrences(of: " w5", with: "\nw5").split(separator: "\n", omittingEmptySubsequences: false)
let longest = lines.map { $0.utf8.count }.max() ?? 0
print("\(text.utf8.count) bytes, \(parts.count) words, \(lengths) letters, \(sevens) sevens")
print("\(replaced.utf8.count) replaced, \(digits) digits, found at \(found)")
let trimmed = "  \(upper.prefix(20))  ".trimmingCharacters(in: .whitespaces)
print("\(lines.count) lines, longest \(longest), trimmed \(trimmed)")
