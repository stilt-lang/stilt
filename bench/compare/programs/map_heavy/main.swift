// map-heavy: inserts, finds, overwrites and removes integer and string keys in hash maps.

func next(_ x: Int) -> Int { (x * 1103515245 + 12345) % 2147483648 }

let n = 300000
var numbers: [Int: Int] = [:]
var x = 42
for i in 0..<n {
    x = next(x)
    numbers[x % 100000] = i
}
var hits = 0
for _ in 0..<n {
    x = next(x)
    if numbers[x % 200000] != nil { hits += 1 }
}
for k in 0..<50000 { numbers.removeValue(forKey: k * 2) }
var sum = 0
for (k, v) in numbers { sum += k ^ v }
print("\(numbers.count) numbers, \(hits) hits, checksum \(sum)")

var words: [String: Int] = [:]
for _ in 0..<n {
    x = next(x)
    words["w\(x % 5000)", default: 0] += 1
}
var longest = 0
var most = 0
for (w, count) in words {
    longest = max(longest, w.utf8.count)
    most = max(most, count)
}
print("\(words.count) words, longest \(longest), most \(most)")
