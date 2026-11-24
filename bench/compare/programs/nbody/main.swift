// n-body: simulates the orbits of the Jovian planets with a symplectic integrator, as the
// Benchmarks Game's program does.

import Foundation

struct Body {
    var x, y, z, vx, vy, vz, mass: Double
}

let solarMass = 4.0 * Double.pi * Double.pi
let daysPerYear = 365.24

func body(_ x: Double, _ y: Double, _ z: Double, _ vx: Double, _ vy: Double, _ vz: Double, _ mass: Double) -> Body {
    Body(x: x, y: y, z: z, vx: vx * daysPerYear, vy: vy * daysPerYear, vz: vz * daysPerYear, mass: mass * solarMass)
}

func system() -> [Body] {
    [
        body(0, 0, 0, 0, 0, 0, 1),
        body(4.84143144246472090, -1.16032004402742839, -0.103622044471123109,
             0.00166007664274403694, 0.00769901118419740425, -0.0000690460016972063023,
             0.000954791938424326609),
        body(8.34336671824457987, 4.12479856412430479, -0.403523417114321381,
             -0.00276742510726862411, 0.00499852801234917238, 0.0000230417297573763929,
             0.000285885980666130812),
        body(12.8943695621391310, -15.1111514016986312, -0.223307578892655734,
             0.00296460137564761618, 0.00237847173959480950, -0.0000296589568540237556,
             0.0000436624404335156298),
        body(15.3796971148509165, -25.9193146099879641, 0.179258772950371181,
             0.00268067772490389322, 0.00162824170038242295, -0.0000951592254519715870,
             0.0000515138902046611451),
    ]
}

func offsetMomentum(_ bodies: inout [Body]) {
    var px = 0.0, py = 0.0, pz = 0.0
    for b in bodies {
        px += b.vx * b.mass
        py += b.vy * b.mass
        pz += b.vz * b.mass
    }
    bodies[0].vx = -px / solarMass
    bodies[0].vy = -py / solarMass
    bodies[0].vz = -pz / solarMass
}

func energy(_ bodies: [Body]) -> Double {
    var e = 0.0
    for i in 0..<bodies.count {
        let b = bodies[i]
        e += 0.5 * b.mass * (b.vx * b.vx + b.vy * b.vy + b.vz * b.vz)
        for c in bodies[(i + 1)...] {
            let dx = b.x - c.x, dy = b.y - c.y, dz = b.z - c.z
            e -= b.mass * c.mass / (dx * dx + dy * dy + dz * dz).squareRoot()
        }
    }
    return e
}

func advance(_ bodies: inout [Body], _ dt: Double) {
    let n = bodies.count
    for i in 0..<n {
        for j in (i + 1)..<n {
            let dx = bodies[i].x - bodies[j].x
            let dy = bodies[i].y - bodies[j].y
            let dz = bodies[i].z - bodies[j].z
            let d2 = dx * dx + dy * dy + dz * dz
            let mag = dt / (d2 * d2.squareRoot())
            let mi = bodies[i].mass * mag
            let mj = bodies[j].mass * mag
            bodies[i].vx -= dx * mj
            bodies[i].vy -= dy * mj
            bodies[i].vz -= dz * mj
            bodies[j].vx += dx * mi
            bodies[j].vy += dy * mi
            bodies[j].vz += dz * mi
        }
    }
    for i in 0..<n {
        bodies[i].x += dt * bodies[i].vx
        bodies[i].y += dt * bodies[i].vy
        bodies[i].z += dt * bodies[i].vz
    }
}

var bodies = system()
offsetMomentum(&bodies)
print(String(format: "%.9f", energy(bodies)))
for _ in 0..<1_000_000 { advance(&bodies, 0.01) }
print(String(format: "%.9f", energy(bodies)))
