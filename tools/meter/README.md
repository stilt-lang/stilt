# The meter

`stilt-meter` reads what a process costs, as the processor counts it: the instructions its threads retire, the cycles they run and their CPU time. It reads a running process by its pid, such as an engine, and a child once it has ended, before it is reaped, as [`run`](src/lib.rs) does. The benchmarks ([`bench/`](../../bench/)) and the latency harness ([`latency/`](../latency/)) judge their goals with it ([Goals](../../docs/design/goals.md#how-to-read-the-goals), Timing).

Other processes on the machine change a program's wall time severalfold and its CPU time by half again. They leave the instructions it retires as they are, and change its cycles by what the programs contend for, the caches and the memory, and by where the system runs it: under load it moves a program to the efficiency cores, which take more cycles for the same instructions. On the reference machine, an Apple M4 with 4 performance cores and 6 efficiency cores, under twice as many busy loops as it has cores, the fastest of five runs of a Rust benchmark took:

| Measure | Under load, against an idle machine |
| --- | --- |
| Wall time | 3.1 to 3.8 times |
| CPU time | 1.5 to 1.7 times |
| Cycles | 1.03 to 1.24 times |
| Cycles on the performance cores, scaled to all the instructions | 1.000 to 1.004 times |
| Instructions | 1.000 times |

A goal whose target is a time or a speed is judged on the cycles the work would run on the performance cores, which count what the processor spends waiting on memory as time does: those it ran there, scaled by all the instructions it retired over those it retired there ([`Counts::performance_cycles`](src/lib.rs)), taken as time at the reference machine's clock, 4.0 GHz a performance core. Work spread over several cores counts each core's cycles, so the time is the lesser of that and the wall time: each is at least the time on an idle machine for work that computes rather than waits, the wall time since other programs only slow the work, and the cycles since they count every thread. Under load either errs on the strict side. Instructions are reported beside them, as the steadiest measure of the work.

macOS keeps both counts for every process, and `proc_pid_rusage` reads them for any process of the same user. On Linux they need `perf_event_open`, which most machines allow only to root, so there the meter gives the CPU time alone.
