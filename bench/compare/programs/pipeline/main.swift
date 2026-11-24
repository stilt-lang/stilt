// pipeline: records through closures: maps, filters, folds and sorts by key, and groups in a
// map.

struct Item {
    var id: Int
    var group: Int
    var score: Int
    var name: String
}

func items(_ n: Int) -> [Item] {
    var out: [Item] = []
    var x = 3
    for i in 0..<n {
        x = (x * 1103515245 + 12345) % 2147483648
        out.append(Item(id: i, group: x % 13, score: x % 1000, name: "n\(x % 97)"))
    }
    return out
}

let all = items(100000)
var total = 0
for round in 0..<10 {
    let boosted = all.map { Item(id: $0.id, group: $0.group, score: $0.score + round, name: $0.name) }
    let kept = boosted.filter { $0.score % 3 != 0 }
    total += kept.reduce(0) { ($0 + $1.score * $1.group) % 1000000007 }
    let sorted = kept.sorted { $0.score > $1.score }
    let best = sorted.prefix(5).map { $0.id }
    total += best.reduce(0, +)
}
var groups: [Int: Int] = [:]
for it in all { groups[it.group, default: 0] += it.score }
let named = all.filter { $0.name.hasSuffix("7") }.count
let top = all.first { $0.score == 999 }?.id ?? -1
print("\(total) \(groups[4] ?? 0) \(named) \(top) \(all.contains { $0.score > 998 })")
