// spectral-norm: the spectral norm of an infinite matrix, by the power method, as the
// Benchmarks Game's program computes it.

import Foundation

func a(_ i: Int, _ j: Int) -> Double {
    1.0 / Double((i + j) * (i + j + 1) / 2 + i + 1)
}

func times(_ v: [Double]) -> [Double] {
    (0..<v.count).map { i in
        var sum = 0.0
        for j in 0..<v.count { sum += a(i, j) * v[j] }
        return sum
    }
}

func timesTransposed(_ v: [Double]) -> [Double] {
    (0..<v.count).map { i in
        var sum = 0.0
        for j in 0..<v.count { sum += a(j, i) * v[j] }
        return sum
    }
}

func timesBoth(_ v: [Double]) -> [Double] { timesTransposed(times(v)) }

let n = 1000
var u = Array(repeating: 1.0, count: n)
var v: [Double] = []
for _ in 0..<10 {
    v = timesBoth(u)
    u = timesBoth(v)
}
var vbv = 0.0
var vv = 0.0
for i in 0..<n {
    vbv += u[i] * v[i]
    vv += v[i] * v[i]
}
print(String(format: "%.9f", (vbv / vv).squareRoot()))
