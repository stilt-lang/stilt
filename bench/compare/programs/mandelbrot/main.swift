// mandelbrot: counts the points of a grid that stay in the Mandelbrot set for 50 iterations,
// and the iterations of those that escape.

let size = 600
let scale = Double(size)
var inside = 0
var escapes = 0
for y in 0..<size {
    let ci = 2.0 * Double(y) / scale - 1.0
    for x in 0..<size {
        let cr = 2.0 * Double(x) / scale - 1.5
        var zr = 0.0
        var zi = 0.0
        var i = 0
        var escaped = false
        while i < 50 && !escaped {
            let next = zr * zr - zi * zi + cr
            zi = 2.0 * zr * zi + ci
            zr = next
            if zr * zr + zi * zi > 4.0 { escaped = true }
            i += 1
        }
        if escaped { escapes += i } else { inside += 1 }
    }
}
print("\(inside) points inside, \(escapes) iterations to escape")
