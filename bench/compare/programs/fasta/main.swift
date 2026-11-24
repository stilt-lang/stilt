// fasta: writes random DNA sequences, from cumulative probabilities and a linear congruential
// generator, and a repeated one, as the Benchmarks Game's program does, in lines of 60.

let alu = Array("GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA".utf8)

func random(_ seed: inout Int) -> Double {
    seed = (seed * 3877 + 29573) % 139968
    return Double(seed) / 139968.0
}

func repeatAlu(_ n: Int) {
    var start = 0
    var left = n
    while left > 0 {
        let width = min(left, 60)
        var line: [UInt8] = []
        line.reserveCapacity(width)
        for i in 0..<width { line.append(alu[(start + i) % alu.count]) }
        print(String(decoding: line, as: UTF8.self))
        start = (start + width) % alu.count
        left -= width
    }
}

func randomly(_ symbols: String, _ chances: [Double], _ n: Int, _ seed: inout Int) {
    let symbols = Array(symbols.utf8)
    var cumulative: [Double] = []
    var sum = 0.0
    for c in chances {
        sum += c
        cumulative.append(sum)
    }
    var left = n
    while left > 0 {
        let width = min(left, 60)
        var line: [UInt8] = []
        line.reserveCapacity(width)
        for _ in 0..<width {
            let r = random(&seed)
            var k = 0
            while k < cumulative.count - 1 && r >= cumulative[k] { k += 1 }
            line.append(symbols[k])
        }
        print(String(decoding: line, as: UTF8.self))
        left -= width
    }
}

let n = 100000
var seed = 42
print(">ONE Homo sapiens alu")
repeatAlu(n * 2)
print(">TWO IUB ambiguity codes")
let iubChances = [0.27, 0.12, 0.12, 0.27, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02]
randomly("acgtBDHKMNRSVWY", iubChances, n * 3, &seed)
print(">THREE Homo sapiens frequency")
randomly("acgt", [0.3029549426680, 0.1979883004921, 0.1975473066391, 0.3015094502008], n * 5, &seed)
