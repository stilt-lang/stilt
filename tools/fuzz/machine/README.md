# The fuzzing machine

A machine of its own fuzzes `main` around the clock: hosted runners stop after hours, and a
week without a finding needs a week of fuzzing. GitHub is its control panel; the machine serves
nothing but SSH.

| File | What it does |
| --- | --- |
| [`provision.sh`](provision.sh) | Prepares a fresh Ubuntu 24.04: a 4 GB swap file, the packages, Rust stable and nightly with `cargo-fuzz`, opam, uv, unattended security updates, and lingering for the user services |
| [`env.sh`](env.sh) | The settings the other scripts share: the repository, and the directories under `~/fuzz` |
| [`sync.sh`](sync.sh) | Every five minutes: on a new commit of `main`, stops the workers, builds the compiler, the runner, the reference interpreter and the generator, and the fuzz targets, then starts the workers on the new build. The first build takes about an hour on two vCPUs, later ones minutes |
| [`differential.sh`](differential.sh) | Worker 1: generated programs in batches of a thousand from consecutive seeds, from 10,000,001 (CI and the nightly run start at 1), run by the debug back end and their tests compared with the reference interpreter's |
| [`targets.sh`](targets.sh) | Worker 2: the `cargo fuzz` targets of [`../`](../README.md) in turn, an hour each, their corpora kept across builds; the conformance suite and the examples seed `parse`, `format` and `check` |
| [`report.sh`](report.sh) | Every hour: each finding becomes an issue labelled `fuzz`, or a comment on the open issue with its signature (the kind, and where it panicked or what the runner reported first); and it rewrites the issue "Fuzzing status": the commit fuzzed, the programs and executions of the last hour, the corpus, the open findings |
| [`systemd/`](systemd/) | The user units: the two workers, and a timer each for `sync` and `report` |

A finding waits in `~/fuzz/findings/` until it is reported, with its report and what reproduces
it: a seed and the commit for a generated program, the input for a fuzz target.

## Setting it up

From a machine with SSH access to it, as the user `ubuntu`:

```sh
scp tools/fuzz/machine/provision.sh ubuntu@HOST: && ssh ubuntu@HOST ./provision.sh
ssh ubuntu@HOST 'mkdir -p ~/fuzz/bin ~/.config/systemd/user'
rsync -a tools/fuzz/machine/*.sh ubuntu@HOST:fuzz/bin/
rsync -a tools/fuzz/machine/systemd/ ubuntu@HOST:.config/systemd/user/
ssh ubuntu@HOST 'systemctl --user daemon-reload && systemctl --user enable --now stilt-fuzz-sync.timer stilt-fuzz-report.timer'
```

Issues need a fine-grained token that may read and write issues on this repository alone, in
`~/fuzz/token` (mode 600). Without one the machine fuzzes and keeps its findings.

`journalctl --user -u 'stilt-fuzz-*'` shows what it did; `~/fuzz/state/progress` holds a line per
batch and per target run.
