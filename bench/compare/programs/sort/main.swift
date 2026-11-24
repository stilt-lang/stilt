// sort: sorts a list of integers with the standard library's sort and with a quicksort that
// works in place.

func quicksort(_ xs: inout [Int], _ lo: Int, _ hi: Int) {
    if lo >= hi { return }
    let pivot = xs[(lo + hi) / 2]
    var i = lo
    var j = hi
    while i <= j {
        while xs[i] < pivot { i += 1 }
        while xs[j] > pivot { j -= 1 }
        if i <= j {
            xs.swapAt(i, j)
            i += 1
            j -= 1
        }
    }
    quicksort(&xs, lo, j)
    quicksort(&xs, i, hi)
}

func checksum(_ xs: [Int]) -> Int {
    xs.reduce(0) { ($0 * 31 + $1) % 1000000007 }
}

var xs: [Int] = []
var x = 1
for _ in 0..<400000 {
    x = (x * 1103515245 + 12345) % 2147483648
    xs.append(x % 1000000)
}
let sorted = xs.sorted()
var quick = xs
quicksort(&quick, 0, quick.count - 1)
let byDigit = xs.sorted { $0 % 10 < $1 % 10 }
print("\(checksum(sorted)) \(checksum(quick)) \(checksum(byDigit))")
