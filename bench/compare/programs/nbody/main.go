// n-body: simulates the orbits of the Jovian planets with a symplectic integrator, as the
// Benchmarks Game's program does.
package main

import (
	"fmt"
	"math"
)

type Body struct{ x, y, z, vx, vy, vz, mass float64 }

const (
	solarMass   = 4 * math.Pi * math.Pi
	daysPerYear = 365.24
)

func body(x, y, z, vx, vy, vz, mass float64) Body {
	return Body{x, y, z, vx * daysPerYear, vy * daysPerYear, vz * daysPerYear, mass * solarMass}
}

func system() []Body {
	return []Body{
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
	}
}

func offsetMomentum(bodies []Body) {
	var px, py, pz float64
	for _, b := range bodies {
		px += b.vx * b.mass
		py += b.vy * b.mass
		pz += b.vz * b.mass
	}
	bodies[0].vx = -px / solarMass
	bodies[0].vy = -py / solarMass
	bodies[0].vz = -pz / solarMass
}

func energy(bodies []Body) float64 {
	e := 0.0
	for i, b := range bodies {
		e += 0.5 * b.mass * (b.vx*b.vx + b.vy*b.vy + b.vz*b.vz)
		for _, c := range bodies[i+1:] {
			dx, dy, dz := b.x-c.x, b.y-c.y, b.z-c.z
			e -= b.mass * c.mass / math.Sqrt(dx*dx+dy*dy+dz*dz)
		}
	}
	return e
}

func advance(bodies []Body, dt float64) {
	for i := range bodies {
		bi := &bodies[i]
		for j := i + 1; j < len(bodies); j++ {
			bj := &bodies[j]
			dx, dy, dz := bi.x-bj.x, bi.y-bj.y, bi.z-bj.z
			d2 := dx*dx + dy*dy + dz*dz
			mag := dt / (d2 * math.Sqrt(d2))
			mi, mj := bi.mass*mag, bj.mass*mag
			bi.vx -= dx * mj
			bi.vy -= dy * mj
			bi.vz -= dz * mj
			bj.vx += dx * mi
			bj.vy += dy * mi
			bj.vz += dz * mi
		}
	}
	for i := range bodies {
		b := &bodies[i]
		b.x += dt * b.vx
		b.y += dt * b.vy
		b.z += dt * b.vz
	}
}

func main() {
	bodies := system()
	offsetMomentum(bodies)
	fmt.Printf("%.9f\n", energy(bodies))
	for range 1000000 {
		advance(bodies, 0.01)
	}
	fmt.Printf("%.9f\n", energy(bodies))
}
