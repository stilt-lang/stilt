// fannkuch-redux: the most pancake flips over the permutations of 1 to n, and a checksum of
// them, as the Benchmarks Game's program counts them, on one thread.

func fannkuch(_ n: Int) -> (checksum: Int, maxFlips: Int) {
    var perm1 = Array(0..<n)
    var count = Array(repeating: 0, count: n)
    var maxFlips = 0
    var checksum = 0
    var permutations = 0
    var r = n
    while true {
        while r != 1 {
            count[r - 1] = r
            r -= 1
        }
        var perm = perm1
        var flips = 0
        var k = perm[0]
        while k != 0 {
            var i = 0
            var j = k
            while i < j {
                perm.swapAt(i, j)
                i += 1
                j -= 1
            }
            flips += 1
            k = perm[0]
        }
        maxFlips = max(maxFlips, flips)
        checksum += permutations % 2 == 0 ? flips : -flips
        while true {
            if r == n { return (checksum, maxFlips) }
            let first = perm1[0]
            for i in 0..<r { perm1[i] = perm1[i + 1] }
            perm1[r] = first
            count[r] -= 1
            if count[r] > 0 { break }
            r += 1
        }
        permutations += 1
    }
}

let n = 10
let (checksum, flips) = fannkuch(n)
print("\(checksum)\nPfannkuchen(\(n)) = \(flips)")
