// matmul: multiplies two square matrices of floats, held as lists of rows.

import Foundation

func matrix(_ n: Int, _ seed: Int) -> [[Double]] {
    (0..<n).map { i in (0..<n).map { j in Double((i * j + seed) % 17) / 17.0 } }
}

func multiply(_ a: [[Double]], _ b: [[Double]]) -> [[Double]] {
    let n = a.count
    var c: [[Double]] = []
    for i in 0..<n {
        let ai = a[i]
        var row: [Double] = []
        for j in 0..<n {
            var sum = 0.0
            for k in 0..<n { sum += ai[k] * b[k][j] }
            row.append(sum)
        }
        c.append(row)
    }
    return c
}

let n = 250
let c = multiply(matrix(n, 1), matrix(n, 2))
var trace = 0.0
for i in 0..<n { trace += c[i][i] }
print(String(format: "%.6f %.6f", c[n / 2][n / 3], trace))
