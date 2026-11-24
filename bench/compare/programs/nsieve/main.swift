// nsieve: counts the primes below three bounds with the sieve of Eratosthenes, as the
// Benchmarks Game's former program does.

import Foundation

func primes(_ m: Int) -> Int {
    var flags = Array(repeating: true, count: m + 1)
    var count = 0
    for i in 2...m where flags[i] {
        count += 1
        var k = i + i
        while k <= m {
            flags[k] = false
            k += i
        }
    }
    return count
}

for shift in 0..<3 {
    let m = (1 << (22 - shift)) * 10000 / 4096
    print(String(format: "Primes up to %8d %8d", m, primes(m)))
}
