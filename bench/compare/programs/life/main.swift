// life: runs Conway's Game of Life on a grid that wraps around, held as one list of cells.

func step(_ cells: [Bool], _ n: Int) -> [Bool] {
    var next: [Bool] = []
    next.reserveCapacity(n * n)
    for y in 0..<n {
        for x in 0..<n {
            var alive = 0
            for dy in 0..<3 {
                for dx in 0..<3 where dy != 1 || dx != 1 {
                    let yy = (y + dy + n - 1) % n
                    let xx = (x + dx + n - 1) % n
                    if cells[yy * n + xx] { alive += 1 }
                }
            }
            next.append(alive == 3 || cells[y * n + x] && alive == 2)
        }
    }
    return next
}

let n = 256
var cells: [Bool] = []
var x = 11
for _ in 0..<n * n {
    x = (x * 1103515245 + 12345) % 2147483648
    cells.append(x % 3 == 0)
}
for _ in 0..<60 { cells = step(cells, n) }
print("\(cells.filter { $0 }.count) cells alive")
