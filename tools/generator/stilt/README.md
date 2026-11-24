# Scale generator in Stilt

A port of `stilt-gen scale` to Stilt: from a seed, it writes a directory program of many modules that import one another, at least as many lines long as asked, byte for byte as the OCaml generator writes it. Its modules mirror the OCaml modules that the scale mode reaches, and `pick` reproduces OCaml's `Random.State`, so one seed draws the same choices in both.

Run it from the repository root with `stilt run tools/generator/stilt --seed N --lines N --out DIR` (seed 0 and 50,000 lines by default), or build it with `stilt build tools/generator/stilt -o scale`. `stilt test tools/generator/stilt` runs its examples.
