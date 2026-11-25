# Commands for working on Stilt. Run `just` to list them.

set shell := ["bash", "-euo", "pipefail", "-c"]

# OCaml tools run in the repository's local opam switch, or in the one STILT_SWITCH names, such
# as the main checkout's from a git worktree, which has none of its own.
# Dune runs holding a lock, through `_dune` below.
switch := env_var_or_default("STILT_SWITCH", ".")
dune := "just _dune"
ocamlformat := "opam exec --switch=" + switch + " -- ocamlformat"
interpreter := "_build/install/default/bin/stilt-ref"
generator := "_build/install/default/bin/stilt-gen"
runner := "target/bin/stilt-test"
compiler := "target/bin/stilt"
# The conformance directories whose code a release build specializes, each run test of which
# `just run` builds as a release build (builds.specialization, Required tests).
specialized := "conformance/generics conformance/staging conformance/reflection conformance/json conformance/polymorphism conformance/variadics conformance/parameters"
grammar-tool := "target/bin/stilt-grammar"
# A Linux executable is static and loads no library (c.build-targets): a program that links one
# doesn't build there, and a C function no library defines fails the link rather than its first
# call (c.finding-functions). The built and release runs leave those two tests out on Linux;
# `run` and `test` still check them, and compiler/stilt-cli/tests/foreign.rs the static builds.
static-skips := if os() == "linux" { "--skip foreign/zlib --skip foreign/missing.lt" } else { "" }
# The goals of the project's own loop, quick-suite and quick-ci, are the time a developer waits,
# which another program on the machine stretches, so their wall-time budgets are judged only on
# a machine that nothing else shares: set STILT_DEDICATED=1 there, as hosted CI's runners do.
# Elsewhere the times are printed (Goals, Timing).
dedicated := env_var_or_default("STILT_DEDICATED", "")
suite-budget := if dedicated == "1" { "--budget 60" } else { "" }

# List the recipes.
[private]
default:
    @just --list --unsorted

# Prepare a fresh checkout: check the tools a contributor needs, create the opam switch, fetch
# the pinned Rust toolchain and Lean's, and build everything. Nothing is installed outside the
# checkout, rustup's and elan's own directories; a tool that is missing is named with the command
# that installs it, and the recipe stops.
# Set up a fresh checkout so that `just ci` can run.
[group('build')]
setup:
    #!/usr/bin/env bash
    set -euo pipefail
    missing=0
    need() {
        if ! command -v "$1" > /dev/null; then
            echo "missing: $1; $2"
            missing=1
        fi
    }
    need rustup "install it from https://rustup.rs"
    need opam "install opam 2.2 or later: brew install opam, or https://opam.ocaml.org/doc/Install.html"
    need elan "install it from https://github.com/leanprover/elan, for the Lean model"
    need uv "install it from https://docs.astral.sh/uv/, for the grammar checks"
    need cc "install Xcode's command-line tools (xcode-select --install), or gcc"
    if [ "$(uname)" = Darwin ]; then
        need clang "brew install llvm, whose clang release builds link with"
    else
        need clang "install the clang release that compiler/stilt-cli/src/release/compiler.rs pins"
    fi
    if [ "$missing" = 1 ]; then
        echo "ERROR install what is missing, then run just setup again"
        exit 1
    fi
    if ! command -v docker > /dev/null || ! docker info > /dev/null 2>&1; then
        echo "note: Docker isn't running; only just sanitizers, debuggers and cross need it"
    fi
    rustup show active-toolchain > /dev/null 2>&1 || rustup toolchain install
    if [ ! -d "{{ switch }}/_opam" ] && [ "{{ switch }}" = . ]; then
        opam switch create . 5.5.2 --deps-only --with-test --with-dev-setup --yes
    elif [ "{{ switch }}" != . ]; then
        echo "using the opam switch of {{ switch }}"
    fi
    (cd formal && elan toolchain install "$(cat lean-toolchain)")
    just build
    echo "ready: just ci runs everything CI checks, and just lists the other commands"

# Runs dune in the opam switch while holding a lock on target/dune.lock, waiting for it:
# dune refuses to start while another instance holds its build directory, and `just ci` runs
# recipes at once. `flock` takes the lock on Linux, and `lockf` on macOS.
[positional-arguments]
_dune *args:
    #!/usr/bin/env bash
    set -euo pipefail
    mkdir -p "$(readlink target || echo target)"
    # A worktree nested in a checkout would otherwise build the outer checkout's project.
    export DUNE_ROOT="$PWD"
    if command -v flock > /dev/null; then
        exec flock target/dune.lock opam exec --switch={{ switch }} -- dune "$@"
    else
        exec lockf -k target/dune.lock opam exec --switch={{ switch }} -- dune "$@"
    fi

# Everything CI checks. A change merges only when this passes, within ten
# minutes on a dedicated machine (goal quick-ci). The recipes that only pass or fail run two at a
# time, from one queue: `fmt-check` and `lint` first, since they fail in
# seconds where the rest take minutes, then the others, the longest first, by
# the times of the last run, kept in target/ci-times, or in the order below
# when there is none, which is that of their times on a cold run. Each of the
# two takes the next recipe as it finishes one, so they end together however
# the recipes' times change; a third was slower, since the long recipes each
# keep several cores busy. The recipes that time something, `latency` and
# `bench`, then run alone, so that our own recipes don't contend with them for
# the caches and the memory, which their cycles count. Each recipe's output is
# in target/ci/RECIPE.log.
[doc('Run everything CI checks, as one queue on this machine.')]
[group('test')]
ci:
    #!/usr/bin/env bash
    set -uo pipefail
    just build
    cargo build --release --workspace
    cargo test --workspace --no-run
    # From here on no recipe builds, and those that run cargo's tests run one after another, as
    # `tests`, since each cargo command writes the binaries that the others' tests run (see
    # `build`).
    export STILT_BUILT=1
    rm -rf target/ci
    mkdir -p target/ci
    recipes=(differential memory cross-sample tests scale check run debuggers generated grammar \
        parse ports stress mutated conformance guide examples formal coverage site)
    # The recipes in the order of the last run's times, longest first, with any it didn't
    # run first of all, in their order above.
    {
        echo fmt-check
        echo lint
        for recipe in "${recipes[@]}"; do
            echo "$(awk -v r="$recipe" '$1 == r { print $2 }' target/ci-times 2>/dev/null \
                | grep . || echo 1000000) $recipe"
        done | sort -s -k1,1nr | cut -d' ' -f2
    } > target/ci/queue
    # Runs one recipe. When it fails, it stops the queue, the recipes that are running with it
    # included, so that a failure is reported as soon as it happens: the queue runs in a
    # process group of its own, which each recipe's Docker containers leave on its way out,
    # as their traps remove them.
    one() {
        local start=$SECONDS
        local recipes=$1
        if [ "$1" = tests ]; then
            recipes="test formatter facts holes alternatives diagnostics-tokens"
        fi
        # shellcheck disable=SC2086
        if just $recipes > "target/ci/$1.log" 2>&1; then
            echo "$1 $(( SECONDS - start ))" >> target/ci/times
            echo "ci: $1 took $(( SECONDS - start )) s"
        else
            echo "ERROR ci: $1 failed after $(( SECONDS - start )) s; the end of target/ci/$1.log:"
            tail -n 40 "target/ci/$1.log"
            # This shell's parent is the queue's xargs, which leads its group.
            kill -TERM -- "-$(ps -o pgid= "$PPID" | tr -d ' ')"
        fi
    }
    export -f one
    # Job control gives the queue its own process group, which its xargs leads.
    set -m
    xargs -P 2 -n 1 bash -c 'one "$0"' < target/ci/queue &
    wait $!
    failed=$?
    set +m
    # The times of this run, and the last run's for the recipes this one didn't finish.
    cat target/ci/times target/ci-times 2>/dev/null | awk '!seen[$1]++' > target/ci-times.new
    mv target/ci-times.new target/ci-times
    if (( failed )); then
        exit 1
    fi
    for recipe in latency bench; do
        start=$SECONDS
        if ! just "$recipe" > "target/ci/$recipe.log" 2>&1; then
            echo "ERROR ci: $recipe failed after $(( SECONDS - start )) s; the end of target/ci/$recipe.log:"
            tail -n 40 "target/ci/$recipe.log"
            exit 1
        fi
        echo "ci: $recipe took $(( SECONDS - start )) s"
    done
    if [ "{{ dedicated }}" = 1 ] && (( SECONDS > 600 )); then
        echo "ERROR CI took ${SECONDS} s, over its budget of 600 s"
        exit 1
    fi
    if [ "{{ dedicated }}" = 1 ]; then
        echo "ci: all passed in ${SECONDS} s"
    else
        echo "ci: all passed in ${SECONDS} s; quick-ci's budget of 600 s is judged only on a" \
            "dedicated machine (STILT_DEDICATED=1)"
    fi

# Build the reference interpreter and the Rust crates, and the toolchain of `stilt build`. Every cargo build
# and test for the host takes `--workspace`, so that it resolves the features of dependencies as
# this one does: a build of fewer crates would make `target/debug/stilt` or
# `target/release/stilt` again with other features. Builds for another target write elsewhere.
# Recipes run the copies of the binaries in target/bin, which cargo never touches: on macOS every
# cargo command, even one with nothing to build, writes each binary into target/debug again, and
# a lane that ran one at that moment would find no file. Under STILT_BUILT, which `just ci` sets
# once it has built everything, no recipe runs cargo but those that run its tests.
[doc('Build the reference interpreter, the compiler and the toolchain of `stilt build`.')]
[group('build')]
build: _target
    {{ dune }} build
    if [ -z "${STILT_BUILT:-}" ]; then cargo build --workspace && just toolchain _bins; fi

# The copies of the binaries that recipes run, each replaced whole and only when it changed.
_bins:
    #!/usr/bin/env bash
    set -euo pipefail
    mkdir -p target/bin
    for bin in stilt stilt-test stilt-grammar stilt-registry; do
        if ! cmp -s "target/debug/$bin" "target/bin/$bin"; then
            cp -c "target/debug/$bin" "target/bin/.$bin" 2> /dev/null \
                || cp "target/debug/$bin" "target/bin/.$bin"
            mv -f "target/bin/.$bin" "target/bin/$bin"
        fi
    done
    if [ "$(readlink target/bin/stilt-toolchain)" != ../stilt-toolchain ]; then
        ln -sfn ../stilt-toolchain target/bin/stilt-toolchain
    fi

# Keep Spotlight out of the build directory. macOS indexes every file written under target/,
# tens of thousands of generated programs and logs per CI run, and its indexer then takes
# several cores from the lanes that CI times (goal quick-ci). Spotlight skips a directory
# named `*.noindex`, and nothing else keeps it out on current macOS, so target/ is a symbolic
# link to target.noindex/, which every path in this file reaches through the link. Elsewhere
# target/ is a plain directory. An existing target/ is renamed, so no build is lost.
_target:
    #!/usr/bin/env bash
    set -euo pipefail
    [[ "$(uname)" == Darwin && ! -L target ]] || exit 0
    if [[ -d target && ! -e target.noindex ]]; then
        mv target target.noindex
    elif [[ -d target ]]; then
        rm -rf target
    fi
    mkdir -p target.noindex
    ln -s target.noindex target

# Assemble the toolchain of `stilt build` in target/stilt-toolchain, beside each build of
# `stilt`: LLVM's linker, linked from the Rust toolchain that rust-toolchain.toml pins, beside
# the LLVM library it loads, and for each target its runtime library, built optimized by that
# toolchain's rustc, with musl's C library and start files for x86-64 and aarch64 Linux (goal
# cross-compilation). The macOS library leaves out the DWARF of Rust's standard library, which debugging a
# program never reads, and which dsymutil would otherwise gather at every build: 27 ms of the
# 91 that a small program's build takes. The clang of release builds is the build machine's,
# Homebrew's on a Mac, linked as clang/bin/clang, which must be the release that `stilt` pins
# (builds.release-toolchain); a link takes no room on a disk. WebAssembly's builds take wasi-libc's start
# file and library and clang's builtins from wasi-sdk, and binaryen's wasm-opt, which applies
# Asyncify, each from the archive that compiler/stilt-cli/src/release/wasm.txt pins, and its
# runtime library leaves out the DWARF of Rust's standard library too. The
# wasmtime that the file pins, which runs the modules of the tests and of `just cross`, comes
# to target/wasm-tools/wasmtime beside them.
[doc('Assemble the linker, runtime libraries and WebAssembly tools of `stilt build`.')]
[group('build')]
toolchain:
    #!/usr/bin/env bash
    set -euo pipefail
    rustc=$(rustup which rustc 2>/dev/null || command -v rustc)
    sysroot=$("$rustc" --print sysroot)
    host=$("$rustc" -vV | sed -n 's/^host: //p')
    out=target/stilt-toolchain
    fresh() { if [ "$1" -nt "$2" ]; then cp -p "$1" "$2"; fi; }
    # A library without its DWARF, written beside it and moved in whole, with its source's time.
    stripped() {
        if [ "$1" -nt "$2" ]; then
            "$sysroot/lib/rustlib/$host/bin/rust-objcopy" --strip-debug "$1" "$2.new"
            touch -r "$1" "$2.new"
            mv "$2.new" "$2"
        fi
    }
    # A link is made again only when it points elsewhere, since recipes that
    # `just ci` runs at once each assemble the toolchain while others use it.
    link() { if [ "$(readlink "$2")" != "$1" ]; then ln -sfn "$1" "$2"; fi; }
    mkdir -p "$out/bin" target/debug target/release
    link "$sysroot/lib/rustlib/$host/bin/rust-lld" "$out/bin/rust-lld"
    for target in aarch64-macos:aarch64-apple-darwin x86_64-linux:x86_64-unknown-linux-musl \
        aarch64-linux:aarch64-unknown-linux-musl \
        wasm32-wasip1:wasm32-wasip1; do
        name=${target%%:*} triple=${target#*:}
        RUSTC=$rustc cargo build -q --release -p stilt-runtime --target "$triple" \
            --target-dir target/cross
        mkdir -p "$out/$name"
        copy=fresh
        case $name in *-linux) ;; *) copy=stripped ;; esac
        $copy "target/cross/$triple/release/libstilt_runtime.a" "$out/$name/libstilt_runtime.a"
    done
    for arch in x86_64 aarch64; do
        musl=$sysroot/lib/rustlib/$arch-unknown-linux-musl/lib/self-contained
        for file in crt1.o crti.o crtn.o crtbegin.o crtend.o libc.a libunwind.a; do
            fresh "$musl/$file" "$out/$arch-linux/$file"
        done
    done
    tools=target/wasm-tools
    just _wasm-tool wasi-sysroot lib/wasm32-wasip1/crt1-command.o lib/wasm32-wasip1/libc.a
    just _wasm-tool libclang_rt wasm32-unknown-wasip1/libclang_rt.builtins.a
    just _wasm-tool binaryen 'bin/wasm-opt' 'lib/*'
    just _wasm-tool wasmtime wasmtime
    for file in crt1-command.o libc.a; do
        fresh "$tools/wasi-sysroot/lib/wasm32-wasip1/$file" "$out/wasm32-wasip1/$file"
    done
    fresh "$tools/libclang_rt/wasm32-unknown-wasip1/libclang_rt.builtins.a" \
        "$out/wasm32-wasip1/libclang_rt.builtins.a"
    link "$PWD/$tools/binaryen" "$out/binaryen"
    pinned=$(sed -n 's/^pub(crate) const CLANG: &str = "\(.*\)";/\1/p' \
        compiler/stilt-cli/src/release/compiler.rs)
    # STILT_CLANG names the pinned clang where it isn't Homebrew's, as CI unpacks it from the
    # release toolchains' archive.
    clang=${STILT_CLANG:-/opt/homebrew/opt/llvm/bin/clang}
    if [ "$(uname)" != Darwin ] && [ -z "${STILT_CLANG:-}" ]; then
        clang=$(command -v clang || echo clang)
    fi
    if ! "$clang" --version 2> /dev/null | grep -q "clang version $pinned\b"; then
        echo "ERROR release builds need clang $pinned at $clang: \`brew install llvm\` puts it there, or STILT_CLANG names it"
        exit 1
    fi
    mkdir -p "$out/clang/bin"
    link "$(realpath "$clang")" "$out/clang/bin/clang"
    link ../stilt-toolchain target/debug/stilt-toolchain
    link ../stilt-toolchain target/release/stilt-toolchain

# Pack this host's toolchain into target/dist/stilt-HOST.tar.gz, with its SHA-256 digest
# beside it, as install.sh unpacks it: a release build of `stilt`, and beside it the linker
# with LLVM's library, each target's runtime library and WebAssembly's optimizer, with no link
# to anything outside.
# Release builds fetch clang the first time, as an installed toolchain holds none. Then install
# the archive with install.sh into an empty home, and start, check, run, test and build a
# package there with nothing but the installed `stilt`.
[doc("Pack this host's toolchain into an archive, install it into an empty home and try it.")]
[group('release')]
dist: toolchain
    #!/usr/bin/env bash
    set -euo pipefail
    case "$(uname -sm)" in
        "Darwin arm64") host=aarch64-macos ;;
        "Linux x86_64") host=x86_64-linux ;;
        "Linux aarch64") host=aarch64-linux ;;
        *) echo "ERROR no toolchain is packed for $(uname -sm)"; exit 1 ;;
    esac
    version=$(cat VERSION)
    name=stilt-$version-$host
    cargo build -q --release -p stilt-cli
    rm -rf target/dist
    mkdir -p "target/dist/$name/bin"
    cp target/release/stilt "target/dist/$name/bin/stilt"
    mkdir "target/dist/$name/bin/stilt-toolchain"
    for part in target/stilt-toolchain/*; do
        [ "${part##*/}" = clang ] || cp -RL "$part" "target/dist/$name/bin/stilt-toolchain/"
    done
    # The linker loads LLVM's library from ../lib, beside it, where the archive puts it.
    rustc=$(rustup which rustc 2>/dev/null || command -v rustc)
    mkdir -p "target/dist/$name/bin/stilt-toolchain/lib"
    cp -L "$("$rustc" --print sysroot)"/lib/libLLVM* "target/dist/$name/bin/stilt-toolchain/lib/"
    cp LICENSE-MIT LICENSE-APACHE NOTICE "target/dist/$name/"
    # The notices of what the archive holds that Stilt didn't write, and of what the programs
    # it builds link: the crates' and the toolchain's parts', and Rust's for its standard
    # library and musl.
    uv run tools/release/licenses.py "target/dist/$name/THIRD-PARTY-LICENSES"
    mkdir -p "target/dist/$name/rust"
    cp -R "$("$rustc" --print sysroot)/share/doc/rust/licenses" \
        "$("$rustc" --print sysroot)/share/doc/rust/COPYRIGHT-library.html" "target/dist/$name/rust/"
    # The manual pages and the shells' completions, where package managers look for them.
    share="target/dist/$name/share"
    target/release/stilt manual "$share/man/man1"
    mkdir -p "$share/bash-completion/completions" "$share/zsh/site-functions" \
        "$share/fish/vendor_completions.d"
    target/release/stilt completions bash > "$share/bash-completion/completions/stilt"
    target/release/stilt completions zsh > "$share/zsh/site-functions/_stilt"
    target/release/stilt completions fish > "$share/fish/vendor_completions.d/stilt.fish"
    archive=stilt-$host.tar.gz
    tar -czf "target/dist/$archive" -C target/dist "$name"
    sum=sha256sum
    command -v sha256sum > /dev/null || sum="shasum -a 256"
    (cd target/dist && $sum "$archive" > "$archive.sha256" && cp "$archive.sha256" SHA256SUMS)
    rm -rf "target/dist/$name"
    home=$(mktemp -d)
    trap 'rm -rf "$home"' EXIT
    # A key of this run's own signs SHA256SUMS, as the release's key does a release's.
    ssh-keygen -q -t ed25519 -N '' -C stilt-dist -f "$home/key"
    ssh-keygen -Y sign -q -f "$home/key" -n stilt-release target/dist/SHA256SUMS
    export STILT_RELEASE_KEY
    STILT_RELEASE_KEY=$(cut -d ' ' -f 1,2 "$home/key.pub")
    STILT_DIST=$PWD/target/dist STILT_HOME=$home/.stilt sh install.sh 2> "$home/installed"
    stilt=$home/.stilt/bin/stilt
    (
        cd "$home"
        export PATH=/usr/bin:/bin
        "$stilt" new hello > /dev/null
        cd hello
        "$stilt" check > /dev/null
        [ "$("$stilt" run)" = "Hello, hello!" ]
        "$stilt" test > /dev/null
        "$stilt" build . -o hi > /dev/null
        [ "$(./hi)" = "Hello, hello!" ]
    ) || { echo "ERROR the installed toolchain fails"; cat "$home/installed"; exit 1; }
    echo "target/dist/$archive: $(du -h "target/dist/$archive" | cut -f 1), installs and builds"

# Fetch the archive of a tool of WebAssembly that compiler/stilt-cli/src/release/wasm.txt pins
# for this host, once, into target/wasm-tools/NAME, checked against its SHA-256 before anything
# of it is kept, and keep the files that MEMBERS match, below the archive's top directory
# (wasm.same-meaning). The archive goes once they are out, and a fetch that fails keeps nothing.
_wasm-tool name +members:
    #!/usr/bin/env bash
    set -euo pipefail
    case "$(uname -sm)" in
        "Darwin arm64") host=aarch64-macos ;;
        "Linux x86_64") host=x86_64-linux ;;
        "Linux aarch64") host=aarch64-linux ;;
        *) host=none ;;
    esac
    read -r url sha256 < <(awk -v name={{ name }} -v host="$host" \
        '$1 == name && ($2 == host || $2 == "any") { print $3, $4 }' \
        compiler/stilt-cli/src/release/wasm.txt) || true
    if [ -z "${url:-}" ]; then
        echo "ERROR compiler/stilt-cli/src/release/wasm.txt pins no {{ name }} for this host"
        exit 1
    fi
    dest=target/wasm-tools/{{ name }}
    if [ "$(cat "$dest/.sha256" 2> /dev/null)" = "$sha256" ]; then exit 0; fi
    mkdir -p target/wasm-tools
    work=$(mktemp -d target/wasm-tools/.fetch.XXXXXX)
    trap 'rm -rf "$work"' EXIT
    curl -fsSL --retry 3 -o "$work/archive" "$url"
    found=$({ sha256sum "$work/archive" 2> /dev/null || shasum -a 256 "$work/archive"; } \
        | cut -d' ' -f1)
    if [ "$found" != "$sha256" ]; then
        echo "ERROR $url has the SHA-256 $found, not $sha256"
        exit 1
    fi
    set -f
    patterns=({{ members }})
    set +f
    wanted=()
    while IFS= read -r member; do
        below=${member#*/}
        for pattern in "${patterns[@]}"; do
            # shellcheck disable=SC2053
            if [[ -n "$below" && "$member" != */ && "$below" == $pattern ]]; then
                wanted+=("$member")
                break
            fi
        done
    done < <(tar -tf "$work/archive")
    if [ ${#wanted[@]} -eq 0 ]; then
        echo "ERROR $url holds nothing that {{ members }} matches"
        exit 1
    fi
    mkdir -p "$work/out"
    tar -xf "$work/archive" -C "$work/out" "${wanted[@]}"
    rm "$work/archive"
    top=$work/out/${wanted[0]%%/*}
    echo "$sha256" > "$top/.sha256"
    rm -rf "$dest"
    mv "$top" "$dest"

# Format all code in place. The OCaml formatters run on the sources directly,
# because `dune fmt` also accepts the output of failed expect tests, and
# expected output must come from the Reference.
[doc('Format all code in place.')]
[group('build')]
fmt:
    cargo fmt --all
    git ls-files --cached --others --exclude-standard -z -- '*.ml' '*.mli' \
        | xargs -0 {{ ocamlformat }} --inplace
    git ls-files --cached --others --exclude-standard -- dune '*/dune' \
        | while read -r file; do \
            {{ dune }} format-dune-file "$file" > "$file.formatted"; \
            mv "$file.formatted" "$file"; \
        done

# Fail if any code is not formatted.
[group('test')]
fmt-check:
    cargo fmt --all --check
    {{ dune }} build @fmt

# Lint the code: the Rust crates fail on any warning, a Rust function over 60
# lines among them (clippy.toml), and the sources fail on any stub, file over 500
# lines or OCaml definition over 60 lines (CONTRIBUTING.md, Code).
[doc('Lint the code, and fail on stubs, oversized files and functions, and unsafe code outside its crates.')]
[group('test')]
lint:
    #!/usr/bin/env bash
    set -euo pipefail
    cargo clippy --workspace --all-targets -- --deny warnings
    # The dependencies' licences, versions and sources (deny.toml), where cargo-deny is
    # installed, and always on CI, which checks their advisories as well.
    if [ -n "${CI:-}" ] || command -v cargo-deny >/dev/null; then
        cargo deny --log-level error check licenses bans sources
    fi
    # The crates and the VS Code extension are released with the toolchain, under its version.
    # The tree-sitter grammar keeps a version of its own, which its parser stores in three bytes.
    for pair in "Cargo.toml:$(sed -n 's/^version = "\(.*\)"$/\1/p' Cargo.toml)" \
        "editors/vscode/package.json:$(sed -n 's/^  "version": "\(.*\)",$/\1/p' editors/vscode/package.json)"; do
        if [ "${pair#*:}" != "$(cat VERSION)" ]; then
            echo "ERROR ${pair%%:*} is version ${pair#*:}, and VERSION $(cat VERSION)"
            exit 1
        fi
    done
    if git grep -nE 'todo!\(|unimplemented!\(|failwith "TODO"' -- compiler bench tools interpreter; then
        echo "ERROR the sources above hold stubs"
        exit 1
    fi
    # Both size checks run, so that one doesn't hide the other's errors.
    sources() { git ls-files --cached --others --exclude-standard -- "$@"; }
    status=0
    # The Reference is the language's one definition: the tree cites its paragraphs and the
    # goals by name, never the numbered records and requirements they replaced, or the phases
    # the language was built in.
    if git grep --untracked -nIE \
        '(^|[^A-Za-z0-9-])(DR-[0-9]{3}|(CS|RT|SF|FL|ER|TY|IF|MC|AG|TC|CR|SR|PL|US)-[0-9]{1,2})([^0-9]|$)|gate-p[0-9]|[Pp]hase [0-9] (built|builds|gate)|Build[ ]plan|(^|[^A-Za-z])the (language )?lead([^A-Za-z]|$)|decision[ ]records?'
    then
        echo "ERROR the lines above cite numbered records, requirements or build phases"
        status=1
    fi
    sources '*.rs' '*.ml' '*.mli' '*.mly' '*.lean' '*.py' '*.sh' '*.js' '*.mjs' '*.ts' '*.astro' | xargs wc -l \
        | awk '$2 != "total" && $1 > 500 { print "ERROR " $2 ": " $1 " lines, over 500"; bad = 1 }
               END { exit bad }' || status=1
    # A definition runs from a `let` or `and` at column 0 to the next item at
    # column 0, its local helpers included.
    sources '*.ml' | xargs awk '
        function close_definition() {
            if (start && last - start >= 60) {
                print "ERROR " name ":" start ": a definition of " last - start + 1 " lines, over 60"
                bad = 1
            }
            start = 0
        }
        FNR == 1 { close_definition() }
        /^(let|and)[ %]/ { close_definition(); start = FNR; last = FNR; name = FILENAME; next }
        /^[^ \t]/ { close_definition(); next }
        /[^ \t]/ { last = FNR }
        END { close_definition(); exit bad }' || status=1
    # Of the compiler's code, only the runtime and the Cranelift back end may use `unsafe` (goal
    # visible-unsafe): every other crate takes the workspace's lints, which forbid it, and clippy
    # requires a `SAFETY:` comment on each block of the two. The count of blocks is printed for
    # the metrics. Of the tools, the meter reads a process's counts by a C call, with a `SAFETY:`
    # comment on each block too, and the fuzz targets are a workspace of their own, whose
    # `fuzz_target!` exports the function that libFuzzer calls, which the lint counts as unsafe;
    # their own code holds none.
    allowed='compiler/stilt-runtime/Cargo.toml compiler/stilt-codegen-clif/Cargo.toml'
    allowed="$allowed tools/meter/Cargo.toml tools/fuzz/Cargo.toml"
    if sources 'tools/fuzz/*.rs' | xargs grep -nE '\bunsafe\b'; then
        echo "ERROR tools/fuzz: the fuzz targets' own code may not use unsafe"
        status=1
    fi
    for manifest in $(sources 'compiler/*/Cargo.toml' 'tools/*/Cargo.toml'); do
        case " $allowed " in
            *" $manifest "*) continue ;;
        esac
        if ! grep -qzE '\[lints\]\s*workspace = true' "$manifest" || grep -q 'unsafe_code' "$manifest"; then
            echo "ERROR $manifest: a crate other than the runtime, the Cranelift back end and the meter may use unsafe"
            status=1
        fi
    done
    blocks=$(sources 'compiler/stilt-runtime/*.rs' 'compiler/stilt-codegen-clif/*.rs' \
        | xargs grep -oE '\bunsafe \{' | wc -l | tr -d ' ')
    meter=$(sources 'tools/meter/*.rs' | xargs grep -oE '\bunsafe \{' | wc -l | tr -d ' ')
    echo "unsafe blocks: $blocks, in stilt-runtime and stilt-codegen-clif; $meter in stilt-meter"
    exit "$status"

# Run the unit tests of the reference interpreter and the Rust crates. The crates' docs hold no examples, so
# rustdoc isn't run to look for them.
[doc('Run the unit tests of the reference interpreter and the Rust crates.')]
[group('test')]
test: build
    {{ dune }} test
    cargo test --workspace --tests

# Run the conformance suite against the reference interpreter, within a minute on a dedicated
# machine (goal quick-suite). Extra arguments go to the runner.
[doc('Run the conformance suite against the reference interpreter.')]
[group('conformance')]
conformance *args: build
    {{ runner }} --impl {{ interpreter }} {{ suite-budget }} {{ args }}

# Check every Stilt example of the guide and of the error index against the reference
# interpreter. Extra arguments go to the runner.
[doc('Check every Stilt example of the guide and of the error index against the reference interpreter.')]
[group('docs')]
guide *args: build
    {{ runner }} --impl {{ interpreter }} --examples target/guide-examples \
        --logs target/guide-logs {{ args }} docs/guide docs/errors

# Run the example programs of examples/: the tests and doc examples of each, and each of its
# samples, from its directory under the compiler and the reference interpreter, whose output must be the
# sample's and whose status 0. Then the compile-time benchmark of bench/compile-time/ and its
# baseline: the tests of each, and each given the benchmark's log, under the reference interpreter and the
# compiler, whose output must be the log's.
[doc('Run the example programs and the compile-time benchmark under both implementations.')]
[group('docs')]
examples: build
    #!/usr/bin/env bash
    set -euo pipefail
    root=$PWD
    for dir in examples/*/; do
        {{ compiler }} test "$dir" > /dev/null
        for sample in "$dir"samples/*.args; do
            args=()
            while IFS= read -r arg; do args+=("$arg"); done < "$sample"
            for impl in {{ compiler }} {{ interpreter }}; do
                if ! (cd "$dir" && "$root/$impl" run . "${args[@]}") | cmp -s - "${sample%.args}.out"; then
                    echo "ERROR $impl run of $sample doesn't give ${sample%.args}.out"
                    exit 1
                fi
            done
        done
        echo "$dir: tests and samples pass"
    done
    bench=bench/compile-time
    for impl in {{ interpreter }} {{ compiler }}; do
        "$impl" test "$bench/meta" > /dev/null
        "$impl" test "$bench/baseline" > /dev/null
    done
    for run in "{{ interpreter }} meta" "{{ interpreter }} baseline" "{{ compiler }} meta" "{{ compiler }} baseline"; do
        read -r impl version <<< "$run"
        if ! (cd "$bench/$version" && "$root/$impl" run .) < "$bench/log.txt" | cmp -s - "$bench/log.out"; then
            echo "ERROR $impl run of $bench/$version doesn't give $bench/log.out"
            exit 1
        fi
    done
    echo "$bench: tests and runs pass"

# Check `stilt fmt` (syntax.format, syntax.no-options and syntax.formatter-tests): each input of tests/format/ formats to the output
# paired with it, and formatting the conformance suite, the guide's examples and generated
# programs changes nothing the second time and keeps the syntax tree of each.
[doc('Check `stilt fmt` against the pairs of tests/format/ and its idempotence.')]
[group('test')]
formatter: build
    rm -rf target/fmt-generated
    {{ generator }} csmith --seed 5 --count 1000 --out target/fmt-generated
    cargo test --workspace --test formatting -- --include-ignored

# Check that the compiler's parser prints the reference interpreter's syntax trees, and reports each file's
# first syntax error where the reference interpreter does: on the conformance suite, the guide's examples,
# generated programs, and edits of those programs that plant syntax errors (goal compiler-checks-like-interpreter).
[doc('Check that the compiler parses as the reference interpreter does.')]
[group('differential')]
parse: build
    {{ runner }} --impl {{ compiler }} --parse {{ interpreter }} --cache target/interpreter-cache --logs target/parse-logs \
        conformance
    {{ runner }} --impl {{ compiler }} --parse {{ interpreter }} --cache target/interpreter-cache --examples target/parse-examples \
        --logs target/parse-logs docs/guide
    rm -rf target/parse-generated target/parse-broken
    {{ generator }} csmith --seed 1 --count 1000 --out target/parse-generated
    {{ generator }} syntax --seed 1 --count 2000 --from conformance \
        --from target/parse-examples --out target/parse-broken
    {{ runner }} --impl {{ compiler }} --parse {{ interpreter }} --cache target/interpreter-cache --logs target/parse-logs \
        target/parse-generated target/parse-broken

# Check the published grammars (goal published-grammar): that regenerating them from
# reference/03-syntax.md changes nothing, and that each, read by llguidance, keeps every prefix of the
# conformance suite's programs without a syntax error, the guide's examples and generated
# programs viable. GBNF is checked as llguidance's own converter turns it into its Lark form.
# Checks too that the files that restate the words and tokens of reference/02-lexical.md, the
# tables of both lexers and the editors' grammars, and the manifest's schema, are what the
# Reference gives, that the lists the guide and the design documents restate are its, and that the
# tree-sitter grammar of editors/tree-sitter/ parses the same programs, but the guide's, without an
# error, and that its highlighting queries, and the queries of Zed's extension in editors/zed/, compile
# and run over them. Its CLI, pinned, comes from npm into target/tree-sitter; without npm that check is skipped.
[doc('Check that the published grammars and the files generated from the Reference are current, and keep every valid prefix viable.')]
[group('docs')]
grammar: build
    #!/usr/bin/env bash
    set -euo pipefail
    {{ grammar-tool }} generate --check
    {{ grammar-tool }} sources --check
    rm -rf target/grammar target/grammar-generated
    mkdir -p target/grammar
    {{ generator }} csmith --seed 1 --count 1000 --out target/grammar-generated
    uv run tools/grammar/gbnf_to_lark.py reference/grammar/stilt.gbnf target/grammar/stilt.gbnf.lark
    {{ grammar-tool }} check --grammar reference/grammar/stilt.lark --grammar target/grammar/stilt.gbnf.lark \
        --conformance conformance --guide docs/guide target/grammar-generated
    if ! command -v npm > /dev/null; then
        echo "tree-sitter: npm is missing, so the tree-sitter grammar is not checked"
        exit 0
    fi
    root=$PWD
    ts=$root/target/tree-sitter
    cli=$ts/node_modules/.bin/tree-sitter
    [ -x "$cli" ] || npm install --silent --no-audit --no-fund --prefix "$ts" tree-sitter-cli@0.25.10
    {{ grammar-tool }} programs --conformance "$PWD/conformance" "$PWD/target/grammar-generated" > "$ts/programs.txt"
    rm -rf "$ts/stilt"
    cp -R editors/tree-sitter "$ts/stilt"
    cd "$ts/stilt"
    "$cli" generate
    # The generated parser is kept in the repository, since Zed, Helix and nvim-treesitter compile
    # src/parser.c as it stands at a commit; it must be what grammar.js generates.
    for generated in src/parser.c src/grammar.json src/node-types.json src/tree_sitter; do
        if ! diff -r -q "$generated" "$root/editors/tree-sitter/$generated" > /dev/null; then
            echo "ERROR editors/tree-sitter/$generated isn't what grammar.js generates: run \`just grammar-generate\`"
            exit 1
        fi
    done
    TREE_SITTER_LIBDIR="$ts/lib" "$cli" parse --quiet --stat --paths "$ts/programs.txt"
    for query in queries/highlights.scm "$root"/editors/zed/languages/stilt/*.scm; do
        TREE_SITTER_LIBDIR="$ts/lib" "$cli" query "$query" --paths "$ts/programs.txt" > /dev/null
    done

# Write the published grammars, reference/grammar/stilt.gbnf and stilt.lark, from reference/03-syntax.md,
# and the files that restate the words and tokens of reference/02-lexical.md, the tree-sitter grammar
# among them with its generated parser, and the facts of facts.inferred-facts (tools/grammar/README.md).
[doc('Write the published grammars and the files generated from the Reference.')]
[group('docs')]
grammar-generate:
    #!/usr/bin/env bash
    set -euo pipefail
    cargo run -q -p stilt-grammar -- generate
    cargo run -q -p stilt-grammar -- sources
    # The tree-sitter grammar's parser, which editors compile from editors/tree-sitter/src/.
    command -v npm > /dev/null || { echo "tree-sitter: npm is missing, so its parser isn't written"; exit 0; }
    ts=$PWD/target/tree-sitter
    cli=$ts/node_modules/.bin/tree-sitter
    [ -x "$cli" ] || npm install --silent --no-audit --no-fund --prefix "$ts" tree-sitter-cli@0.25.10
    cd editors/tree-sitter && "$cli" generate

# Build the website into target/site from the repository, with Astro (site/README.md): the front
# page, with the example of site/example.lt and what `stilt show` prints for each of its
# functions; the guide, the Reference with an anchor for each paragraph, the error index, the
# goals and the design documents; the standard library's pages, from `stilt doc --std`; the
# playground, from what `_playground` builds; a page for each file of the repository that they
# link to; and the search index. It fails on any link that leads nowhere, in the repository or on
# the site, and on any goal that names nothing that checks it.
[doc('Build the website into target/site, and check every internal link.')]
[group('docs')]
site: build _playground
    #!/usr/bin/env bash
    set -euo pipefail
    command -v node > /dev/null || { echo "ERROR the site builds under Node 22.23.4 or later"; exit 1; }
    cd site
    [ node_modules/.package-lock.json -nt package-lock.json ] || npm ci --silent --no-audit --no-fund
    STILT="{{ compiler }}" npm run --silent build

# Build the playground and test it under Node: one check, one show and one run of its first
# program, through the page's WASI host and engine, must print what `stilt` and `stilt-ref`
# print for it (playground/README.md).
[doc('Build the playground, and test it under Node against the native toolchain.')]
[group('docs')]
playground: _playground
    #!/usr/bin/env bash
    set -euo pipefail
    command -v node > /dev/null || { echo "ERROR the playground's test runs under Node"; exit 1; }
    node playground/test.mjs {{ compiler }} {{ interpreter }} target/playground

# The playground's compiler and interpreter, in target/playground. `compiler.wasm` is the crate
# of playground/compiler built for wasm32-wasip1 by the toolchain that rust-toolchain.toml pins,
# in its own target directory, optimized for size, then by binaryen's wasm-opt, which `just
# toolchain` fetches, with the exports of the runtime's natives and of ring removed, which the
# checker never calls. `interpreter.js` is the reference interpreter's run, built by js_of_ocaml.
_playground: build
    #!/usr/bin/env bash
    set -euo pipefail
    out=target/playground
    mkdir -p "$out"
    # ring's C for WebAssembly needs an LLVM clang with its headers: Apple's has no WebAssembly
    # target, so on a Mac it is Homebrew's, which `just setup` asks for.
    if [ "$(uname)" = Darwin ] && [ -z "${CC_wasm32_wasip1:-}" ]; then
        export CC_wasm32_wasip1="$(brew --prefix llvm 2>/dev/null || echo /opt/homebrew/opt/llvm)/bin/clang"
    fi
    RUSTC=$(rustup which rustc 2>/dev/null || command -v rustc) cargo build -q --profile playground \
        -p stilt-playground --target wasm32-wasip1 --target-dir "$out/cargo"
    built=$out/cargo/wasm32-wasip1/playground/stilt-playground.wasm
    if [ "$built" -nt "$out/compiler.wasm" ]; then
        opt=(target/wasm-tools/binaryen/bin/wasm-opt --enable-bulk-memory --enable-sign-ext \
            --enable-mutable-globals --enable-nontrapping-float-to-int --enable-multivalue \
            --enable-reference-types)
        "${opt[@]}" "$built" --remove-exports '--pass-arg=remove-exports@stilt_*' -o "$out/exports.wasm"
        "${opt[@]}" "$out/exports.wasm" --remove-exports '--pass-arg=remove-exports@ring_*' \
            --strip-debug --strip-producers -Oz -o "$out/.compiler.wasm"
        rm "$out/exports.wasm"
        mv -f "$out/.compiler.wasm" "$out/compiler.wasm"
    fi
    {{ dune }} build playground/interpreter/run.bc.js
    js=_build/default/playground/interpreter/run.bc.js
    if ! cmp -s "$js" "$out/interpreter.js"; then
        install -m 644 "$js" "$out/.interpreter.js"
        mv -f "$out/.interpreter.js" "$out/interpreter.js"
    fi

# Check that the compiler's `check` reports the reference interpreter's diagnostics, of every phase (errors.registry-phases), at the same lines and columns: on the conformance suite, the guide's examples, the error index's examples,
# generated programs, programs whose bodies stress inference, programs with one planted
# mistake, and edits of programs that plant syntax errors (goal compiler-checks-like-interpreter).
[doc("Check that the compiler reports the reference interpreter's diagnostics.")]
[group('differential')]
check: build
    {{ runner }} --impl {{ compiler }} --check {{ interpreter }} --cache target/interpreter-cache --logs target/check-logs \
        conformance
    {{ runner }} --impl {{ compiler }} --check {{ interpreter }} --cache target/interpreter-cache --examples target/check-examples \
        --logs target/check-logs docs/guide
    {{ runner }} --impl {{ compiler }} --check {{ interpreter }} --cache target/interpreter-cache --examples target/check-errors \
        --logs target/check-logs docs/errors
    rm -rf target/check-generated target/check-stress target/check-mutated target/check-broken
    {{ generator }} csmith --seed 2 --count 1000 --out target/check-generated
    {{ generator }} stress --seed 2 --count 200 --out target/check-stress
    {{ generator }} mutation --seed 2 --count 900 --out target/check-mutated
    {{ generator }} syntax --seed 2 --count 2000 --from conformance \
        --from target/check-examples --out target/check-broken
    {{ runner }} --impl {{ compiler }} --check {{ interpreter }} --cache target/interpreter-cache --logs target/check-logs \
        target/check-generated target/check-stress target/check-mutated target/check-broken

# Run the conformance suite's run, check and test-block tests, and the guide's examples, under
# the compiler's debug backend, which must give the expected output of each (goal
# debug-runs-like-interpreter): with `stilt run` and `stilt test`, then the run and check tests as executables that
# `stilt build` writes, then a deterministic sample of about one run test in ten as release
# builds, which `stilt build --release` writes (builds.same-meaning; release-runs-like-debug), their objects kept in
# target/stilt-home, a sample of its own beside the one `just cross-sample` builds for Linux,
# since each release build spends a tenth of a second in clang; the nightly run builds them all.
# Every run test of the directories whose code a release build specializes is built as a release
# build too (builds.specialization, Required tests). Then run programs with one planted mistake and edits of
# programs that plant syntax errors, which the compiler must run as the reference interpreter does (program.programs-with-errors). Extra arguments go to the runner's runs of the suite.
[doc('Check that the compiler runs, tests and builds programs as the reference interpreter does.')]
[group('differential')]
run *args: build
    {{ runner }} --impl {{ compiler }} --kinds run,check,test {{ suite-budget }} --logs target/run-logs \
        {{ args }}
    {{ runner }} --impl {{ compiler }} --kinds run,check,test --examples target/run-examples \
        --logs target/run-logs docs/guide
    {{ runner }} --impl tools/runner/built.sh --kinds run,check {{ static-skips }} --logs target/run-logs \
        {{ args }}
    {{ runner }} --impl tools/runner/release.sh --kinds run --fast --sample-key release \
        {{ static-skips }} --logs target/run-logs {{ args }}
    {{ runner }} --impl tools/runner/release.sh --kinds run --logs target/run-logs \
        {{ specialized }}
    rm -rf target/run-mutated target/run-broken
    {{ generator }} mutation --seed 3 --count 300 --out target/run-mutated
    {{ generator }} syntax --seed 3 --count 300 --from conformance \
        --from target/run-examples --out target/run-broken
    {{ runner }} --impl {{ compiler }} --runs {{ interpreter }} --cache target/interpreter-cache --logs target/run-logs \
        target/run-mutated target/run-broken

# Check the facts suite (goal shown-facts): `stilt show --json` must give each function of
# each program in tests/facts/ exactly the facts that its annotations derive from the Reference,
# at their lines, and each module the tier its header expects.
[doc('Check the facts that `stilt show` reports for the programs of tests/facts/.')]
[group('test')]
facts:
    cargo test --workspace --test facts

# Check the holes suite (goal hole-context): `stilt show --json` must give each hole of each
# program in tests/holes/ the context that its annotations derive from the rules of its README.
[doc('Check the context that `stilt show` reports for the holes of tests/holes/.')]
[group('test')]
holes:
    cargo test --workspace --test holes

# Check the alternatives suite (goal admissible-alternatives): `stilt check --json` must give each
# diagnostic of each program in tests/alternatives/ the admissible alternatives that its
# annotations derive from the rules of its README.
[doc('Check the alternatives that `stilt check --json` reports for tests/alternatives/.')]
[group('test')]
alternatives:
    cargo test --workspace --test alternatives

# Run the conformance suite, the guide's examples and generated programs with `check`, `build`,
# `run` and `test` answered by engines, each started for its test's program and stopped after
# it (goal one-engine): each check must report what the compiler alone reports, each run
# test, built by an engine and run, and run by `stilt run` with the code an engine gives it,
# and each test-block test give its expected output, and each generated program, run with the
# code an engine gives it, give the run that the compiler alone gives, errors and all
# (`tools/runner/engine.sh`).
[doc('Check that commands answered by engines give what the compiler alone gives.')]
[group('differential')]
engine: build
    {{ runner }} --impl tools/runner/engine.sh --check {{ compiler }} --logs target/engine-logs \
        conformance
    {{ runner }} --impl tools/runner/engine.sh --check {{ compiler }} \
        --examples target/engine-examples --logs target/engine-logs docs/guide
    # Its runs are built executables, which on Linux can't load the C libraries of two tests.
    {{ runner }} --impl tools/runner/engine.sh --kinds run,check,test {{ static-skips }} \
        --logs target/engine-logs conformance
    {{ runner }} --impl tools/runner/engine-run.sh --kinds run,check --logs target/engine-logs \
        conformance
    rm -rf target/engine-generated target/engine-mutated
    {{ generator }} csmith --seed 4 --count 300 --out target/engine-generated
    {{ generator }} mutation --seed 4 --count 300 --out target/engine-mutated
    {{ runner }} --impl tools/runner/engine.sh --check {{ compiler }} --logs target/engine-logs \
        target/engine-generated target/engine-mutated
    {{ runner }} --impl tools/runner/engine-run.sh --runs {{ compiler }} --logs target/engine-logs \
        target/engine-generated target/engine-mutated

# Run the conformance suite across the matrix of hosts and targets (goals targets and cross-compilation)
# on an aarch64 Mac, with Docker emulating the x86-64 Linux host and target: the Mac builds for
# Linux, debug builds and release builds (builds.release-builds), and Linux, running the compiler built
# for it, builds debug builds for itself and for the Mac: its container holds no clang, and fetches
# none. The clang archive of each host, which a release build fetches, is checked on its own.
# The Mac builds debug builds for aarch64 Linux too, which run natively on the Linux machine of
# its own architecture. Each executable runs on its target. The Mac building for itself is `just run`'s, and so are
# the tests of the systems tier, whose C libraries and C types are the host's (c.build-targets), which the matrix leaves out. The Mac also builds release builds for wasm32-wasip1,
# which run under the wasmtime that compiler/stilt-cli/src/release/wasm.txt pins, with the
# stack, directories and environment of wasm.conformance-runs and without the tests of the
# programs and sockets that WASI preview 1 lacks, a cell that needs no Docker, and
# `just cross wasm` runs it alone. With STILT_CROSS_SAMPLE set, Linux builds, the Mac's
# release builds for Linux and its builds for aarch64 Linux run, only the deterministic sample of `--fast`, its builds for
# WebAssembly about one test in 20, and the Linux host is the Linux machine of the Mac's own
# architecture, natively, running the compiler that `just debuggers` builds for it, since
# building the compiler again for x86-64 Linux, and running it emulated, take most of the time
# CI could give the matrix; `just cross` and `just nightly` run the x86-64 Linux host.
[doc('Run the conformance suite across the matrix of hosts and targets.')]
[group('differential')]
cross *args: build
    #!/usr/bin/env bash
    set -euo pipefail
    # The container mounts the checkout at its real path, which the runner's paths are, even in
    # a worktree that a link reaches.
    cd "$(pwd -P)"
    if [ "$(uname -sm)" != "Darwin arm64" ]; then
        echo "ERROR just cross runs on an aarch64 Mac, which can run both targets"
        exit 1
    fi
    set -- {{ args }}
    docker_cells=1
    if [ "${1:-}" = wasm ]; then
        docker_cells=
        shift
    fi
    mkdir -p target/cross-run
    status=0
    if [ -n "$docker_cells" ]; then
        channel=$(sed -n 's/^channel = "\(.*\)"/\1/p' rust-toolchain.toml)
        linux_rust=${RUSTUP_HOME:-$HOME/.rustup}/toolchains/$channel-x86_64-unknown-linux-gnu
        rustup toolchain install "$channel-x86_64-unknown-linux-gnu" --profile minimal \
            --force-non-host > /dev/null 2>&1
        if ! docker info > /dev/null 2>&1; then
            echo "ERROR just cross needs Docker, which isn't running"
            exit 1
        fi
        container=stilt-cross-$$
        build=$(cd target && pwd -P)
        docker run -d --rm --name "$container" --platform linux/amd64 -v "$PWD:$PWD" \
            -v "$build:$build" -v "$linux_rust:/rust:ro" debian:stable-slim sleep infinity > /dev/null
        machine=$(tools/linux/machine.sh)
        trap 'docker rm -f "$container" $machine > /dev/null' EXIT
        export STILT_ARM_MACHINE=$machine
        if [ -n "${STILT_CROSS_SAMPLE:-}" ]; then
            triple=$(uname -m | sed 's/^arm64$/aarch64/')-unknown-linux-musl
            tools/linux/musl.sh "$triple" build -q -p stilt-cli --target-dir target/linux-musl
            dir=target/linux-musl/$triple/debug
            lld=$(docker exec "$machine" sh -c 'echo "$(rustc --print sysroot)/lib/rustlib/$(rustc -vV \
                | sed -n "s/^host: //p")/bin/rust-lld"')
            export STILT_CROSS_HOST=$machine STILT_CROSS_COMPILER=$PWD/$dir/stilt
        else
            tools/linux/musl.sh x86_64-unknown-linux-musl build -q -p stilt-cli --target-dir target/cross
            dir=target/cross/x86_64-unknown-linux-musl/debug
            lld=/rust/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld
        fi
        toolchain=$dir/stilt-toolchain
        mkdir -p "$toolchain/bin"
        ln -sfn "$lld" "$toolchain/bin/rust-lld"
        for target in aarch64-macos x86_64-linux aarch64-linux; do
            ln -sfn "../../../../stilt-toolchain/$target" "$toolchain/$target"
        done
        docker_host=$(docker context inspect --format '{{{{.Endpoints.docker.Host}}')
        # The copies the runner writes, such as a program with its staging annotations erased
        # (staging-erases), go where the container sees them too.
        export TMPDIR=$PWD/target/cross-run/tmp
        mkdir -p "$TMPDIR"
        for cell in macos:x86_64-linux:debug macos:x86_64-linux:release macos:aarch64-linux:debug \
            linux:x86_64-linux:debug linux:aarch64-macos:debug; do
            IFS=: read -r host target build <<< "$cell"
            wrapper=$PWD/target/cross-run/$host-$target-$build.sh
            printf '#!/usr/bin/env bash\nexport DOCKER_HOST=%q STILT_CROSS_HOST=%q STILT_CROSS_COMPILER=%q STILT_ARM_MACHINE=%q\nexec %q %s %s %s %s "$@"\n' \
                "$docker_host" "${STILT_CROSS_HOST:-$container}" "${STILT_CROSS_COMPILER:-$PWD/$dir/stilt}" "$machine" \
                "$PWD/tools/runner/cross.sh" "$container" "$host" "$target" "$build" > "$wrapper"
            chmod +x "$wrapper"
            sample=
            if { [ "$host" = linux ] || [ "$build" = release ] || [ "$target" = aarch64-linux ]; } \
                && [ -n "${STILT_CROSS_SAMPLE:-}" ]; then
                sample=--fast
            fi
            if [ "$host" = linux ] && [ -n "${STILT_CROSS_SAMPLE:-}" ]; then
                echo "the $(uname -m) linux host building $build builds for $target:"
            else
                echo "the $host host building $build builds for $target:"
            fi
            {{ runner }} --impl "$wrapper" --kinds run --tier meta --time-limit 60 $sample \
                --logs "target/cross-logs/$host-$target-$build" "$@" || status=1
        done
    fi
    wrapper=$PWD/target/cross-run/macos-wasm32-wasip1-release.sh
    printf '#!/usr/bin/env bash\nexport STILT_WASMTIME=%q\nexec %q none macos wasm32-wasip1 release "$@"\n' \
        "$PWD/target/wasm-tools/wasmtime/wasmtime" "$PWD/tools/runner/cross.sh" > "$wrapper"
    chmod +x "$wrapper"
    sample=
    if [ -n "${STILT_CROSS_SAMPLE:-}" ]; then sample="--fast --one-in 20"; fi
    echo "the macos host building release builds for wasm32-wasip1:"
    {{ runner }} --impl "$wrapper" --kinds run --tier meta --time-limit 60 $sample \
        --skip conformance/process/ --skip conformance/net/ --skip conformance/http/ \
        --logs target/cross-logs/macos-wasm32-wasip1-release "$@" || status=1
    exit $status

# The matrix as CI runs it: every run test that the Mac builds for Linux as a debug build, the
# sample of about one in ten of those that it builds as a release build, and that Linux, on the
# Mac's own architecture, builds for both targets, and the sample of about one in 20 that it
# builds for WebAssembly.
[doc('Run the sample of the host and target matrix that CI runs.')]
[group('differential')]
cross-sample:
    STILT_CROSS_SAMPLE=1 just cross

# Time Stilt's debug builds and release builds of the benchmark suite against their Rust baselines,
# and check the budgets of bench/budgets.toml: release-speed, no-outliers, debug-speed, free-success, small-runtime and inline-values
# (Goals, Workloads). The compiler is built optimized, as `just latency` builds it for
# clean-debug-build.
[doc('Time the benchmark suite against its Rust baselines and check its budgets.')]
[group('performance')]
bench *args: build
    [ -n "${STILT_BUILT:-}" ] || cargo build --release --workspace
    target/release/stilt-bench --rustc "$(rustup which rustc 2>/dev/null || command -v rustc)" {{ args }}

# Run the conformance suite's run tests under the compiler built with AddressSanitizer and
# LeakSanitizer, which instrument its runtime, on Linux in Docker (goal no-memory-errors). With
# paths, run the programs under them instead, such as the nightly generated programs, each
# compared with a plain build's run. Docker runs Linux for the host's architecture, natively.
# With STILT_SANITIZER=thread, ThreadSanitizer instruments the runtime and the standard
# library it is built on, and the run tests of tasks, threads, `std.par` and shared values run
# under it, or the programs of the paths given; the first race ends a run with its report. It
# needs x86-64 Linux, where the nightly runs it: on aarch64, the TSan runtime's own start calls
# the outline atomics of the instrumented standard library and crashes before any program runs.
[doc("Run the compiler's runs under AddressSanitizer and LeakSanitizer, or ThreadSanitizer, on Linux in Docker.")]
[group('test')]
sanitizers *paths: build
    #!/usr/bin/env bash
    set -euo pipefail
    container=$(tools/linux/machine.sh)
    trap 'docker rm -f "$container" > /dev/null' EXIT
    triple=$(docker exec "$container" rustc -vV | sed -n 's/^host: //p')
    if [ "${STILT_SANITIZER:-address}" = thread ]; then
        if [ "${triple%%-*}" != x86_64 ]; then
            echo "ERROR ThreadSanitizer runs on x86-64 Linux only, and this machine's Linux is $triple"
            exit 1
        fi
        flags="-Zsanitizer=thread --cfg stilt_tsan"
        std=-Zbuild-std
        out=target/sanitize-thread
        suite="conformance/tasks conformance/threads conformance/par conformance/shared"
    else
        flags="-Zsanitizer=address --cfg stilt_sanitizers"
        std=
        out=target/sanitize
        suite=
    fi
    docker exec -e RUSTFLAGS="$flags" "$container" \
        cargo +nightly-2026-10-29 build -q $std -p stilt-cli --target "$triple" --target-dir "$out"
    docker exec "$container" cargo build -q -p stilt-cli -p stilt-test --target-dir target/linux
    sanitized=$out/$triple/debug/stilt
    if [ -z "{{ paths }}" ]; then
        docker exec "$container" target/linux/debug/stilt-test --impl "$sanitized" --kinds run \
            --time-limit 60 --logs target/sanitize-logs $suite
    else
        docker exec "$container" target/linux/debug/stilt-test --impl "$sanitized" \
            --diff target/linux/debug/stilt --time-limit 60 --logs target/sanitize-logs \
            {{ paths }}
    fi

# Run the debugger tests on Linux in Docker (goal debuggable-builds): gdb shows the lines and
# locals of a program the compiler built for Linux runs in memory, and, under QEMU's
# emulation, of one it built for x86-64 Linux, with the linker of the Linux machine and the
# runtime libraries of `just toolchain`. This machine builds the compiler and the tests for the
# Linux of its own architecture, static with musl, and the Linux machine only runs them: a build
# in Docker would read every source through the mount of the repository, which takes minutes
# where this takes one. `just test` runs the tests with lldb on macOS.
[doc('Run the debugger tests with gdb on Linux in Docker.')]
[group('test')]
debuggers: build
    #!/usr/bin/env bash
    set -euo pipefail
    triple=$(uname -m | sed 's/^arm64$/aarch64/')-unknown-linux-musl
    tests=$(tools/linux/musl.sh "$triple" test -q --no-run -p stilt-cli --test debugger \
        --target-dir target/linux-musl --message-format=json \
        | sed -n 's/.*"executable":"\([^"]*\/deps\/debugger-[^"]*\)".*/\1/p')
    toolchain=target/linux-musl/$triple/debug/stilt-toolchain
    mkdir -p "$toolchain/bin"
    ln -sfn ../../../../debug/stilt-toolchain/x86_64-linux "$toolchain/x86_64-linux"
    container=$(tools/linux/machine.sh)
    trap 'docker rm -f "$container" > /dev/null' EXIT
    docker exec "$container" sh -c 'ln -sfn "$(rustc --print sysroot)/lib/rustlib/$(rustc -vV \
        | sed -n "s/^host: //p")/bin/rust-lld" "$1/bin/rust-lld"' sh "$toolchain"
    docker exec "$container" "$tests"
    docker exec "$container" "$tests" --ignored x86_64

# The nightly run (goals debug-runs-like-interpreter, release-runs-like-debug, no-memory-errors and debuggable-builds): a million generated programs under
# the debug back end and the reference interpreter, a tenth of them under the release back end too, every run
# test of the conformance suite as a release build, commands answered by engines, the whole
# matrix of hosts and targets, the conformance suite and the generated programs under the
# sanitizers, and the debuggers on Linux.
[doc('Run the long checks: a million generated programs, the matrix, sanitizers and debuggers.')]
[group('differential')]
nightly count="1000000":
    just differential {{ count }} 1 10
    {{ runner }} --impl tools/runner/release.sh --kinds run --logs target/run-logs
    just engine
    just cross
    just sanitizers
    STILT_SANITIZER=thread just sanitizers
    just sanitizers target/differential
    just debuggers

# Generate programs from consecutive seeds, and check that the debug backend runs each, and
# its tests, as the reference interpreter does (goal debug-runs-like-interpreter), and that the release builds of one bundle
# in `release` run as the reference interpreter does too (release-runs-like-debug; builds.same-meaning). CI runs 5000 programs, and
# releases one bundle in 25; the nightly run, a million, and one bundle in ten. The compiler
# itself is built optimized, and the programs come in bundles of ten, each a directory program
# whose modules are the programs and whose `main` runs each one's in turn, so that what every
# program costs alike, starting the processes of each command, the compiler's engine, and both
# implementations' checks of the standard library, is paid once a bundle: a program's output,
# tests, doc examples and properties are compared as they would be alone, and a failure's log
# names the program, whose output follows its name. A bundle's release build compiles some
# 4 MB of C, about 4 s of clang's time across the machine's cores, which counts in the time of
# its run, so a run's limit is 60 s.
[doc('Generate programs and check that the compiler runs each as the reference interpreter does.')]
[group('differential')]
differential count="5000" seed="1" release="25": build
    #!/usr/bin/env bash
    set -euo pipefail
    [ -n "${STILT_BUILT:-}" ] || cargo build --release --workspace
    rm -rf target/differential
    {{ generator }} csmith --seed {{ seed }} --count {{ count }} --bundle 10 \
        --out target/differential
    {{ runner }} --impl target/release/stilt --diff {{ interpreter }} --tests \
        --cache target/interpreter-cache --logs target/differential-logs target/differential
    # The release builds, by the optimized compiler, with the reference interpreter's runs from the cache.
    wrapper=target/differential-release.sh
    printf '#!/usr/bin/env bash\nexec %q --stilt %q "$@"\n' "$PWD/tools/runner/release.sh" \
        "$PWD/target/release/stilt" > "$wrapper"
    chmod +x "$wrapper"
    find target/differential -mindepth 1 -maxdepth 1 -type d | sort \
        | awk -v n={{ release }} '(NR - 1) % n == 0' > target/differential-released
    xargs {{ runner }} --impl "$wrapper" --diff {{ interpreter }} --cache target/interpreter-cache \
        --time-limit 60 --logs target/differential-logs < target/differential-released

# Generate programs from consecutive seeds and check that the reference interpreter accepts each
# one, and that two runs of it print the same thing (goal deterministic-interpreter). They
# come in bundles of ten, as `differential` runs them, so the reference interpreter starts once for ten
# programs.
[doc('Generate programs and check that the reference interpreter accepts them deterministically.')]
[group('differential')]
generated count="1000" seed="1": build
    rm -rf target/generated
    {{ generator }} csmith --seed {{ seed }} --count {{ count }} --bundle 10 --out target/generated
    {{ runner }} --impl {{ interpreter }} --diff {{ interpreter }} --logs target/generated-logs \
        target/generated

# Plant mistakes in runs of generated programs, and check that exactly the diagnostic the
# Reference requires for each is reported, on its line: one mistake in each program, with the
# reference interpreter (goal root-causes), and five in each, each in a different body, with the reference interpreter and
# the compiler (goal total-recovery). The kinds take turns, so that each of the 18 is planted
# about as often as the others, and in the three programs in ten that use procedural macros, the
# first mistake is one of the 8 in them, in a use or in the module of macros (macros.procedural-uses): 180
# programs hold some 770 mistakes, as some have fewer than five functions.
[doc('Plant mistakes in generated programs and check the diagnostic reported for each.')]
[group('differential')]
mutated count="900" five="180" seed="1": build
    rm -rf target/mutated target/mutated-five
    {{ generator }} mutation --seed {{ seed }} --count {{ count }} --out target/mutated
    {{ runner }} --impl {{ interpreter }} --logs target/mutated-logs target/mutated
    {{ generator }} mutation --mistakes 5 --seed {{ seed }} --count {{ five }} --out target/mutated-five
    {{ runner }} --impl {{ interpreter }} --logs target/mutated-logs target/mutated-five
    {{ runner }} --impl {{ compiler }} --logs target/mutated-logs target/mutated-five

# Generate the stress suite, whose bodies stress inference, and check that the
# reference interpreter accepts each program, and that two runs of it print the same thing
# (Goals, Workloads). The four kinds of body take turns, so 200 programs
# hold 50 of each.
[doc('Generate bodies that stress inference and check that the reference interpreter accepts them.')]
[group('differential')]
stress count="200" seed="1": build
    rm -rf target/stress
    {{ generator }} stress --seed {{ seed }} --count {{ count }} --out target/stress
    {{ runner }} --impl {{ interpreter }} --diff {{ interpreter }} --logs target/stress-logs \
        target/stress

# Generate the scale projects, of 50K and 100K lines, from their pinned seeds,
# and check that the reference interpreter accepts each one, and that two runs of it exit with
# status 0 and print the same thing (Goals, Workloads). They are workloads
# rather than conformance tests, so each command gets a minute instead of ten
# seconds.
[doc('Generate the 50K- and 100K-line projects and check that the reference interpreter runs them.')]
[group('differential')]
scale: build
    rm -rf target/scale
    {{ generator }} scale --seed 1 --lines 50000 --out target/scale/lines_50k
    {{ generator }} scale --seed 2 --lines 100000 --out target/scale/lines_100k
    {{ runner }} --impl {{ interpreter }} --diff {{ interpreter }} --succeed --time-limit 60 \
        --logs target/scale-logs target/scale

# Check the programs ported to Stilt against their Rust originals (goal shipped-programs): built by
# `stilt build`, the grammar generator writes both published forms as stilt-grammar does, and
# the scale mode writes the projects of ten seeds at 2,000 lines, and the 50K- and 100K-line
# projects of `just scale`, as stilt-gen does, byte for byte.
[doc('Check the programs rewritten in Stilt against what their Rust originals write.')]
[group('differential')]
ports: build
    #!/usr/bin/env bash
    set -euo pipefail
    out=target/ports
    rm -rf "$out"
    mkdir -p "$out"
    {{ compiler }} build tools/grammar/stilt -o "$out/grammar"
    {{ compiler }} build tools/generator/stilt -o "$out/scale"
    {{ grammar-tool }} generate --out "$out/grammar-rust"
    "$out/grammar" --out "$out/grammar-stilt"
    diff -r "$out/grammar-rust" "$out/grammar-stilt"
    echo "grammar: both forms equal"
    for run in "0 2000" "1 2000" "2 2000" "3 2000" "4 2000" "5 2000" "6 2000" "7 2000" \
        "8 2000" "9 2000" "1 50000" "2 100000"; do
        read -r seed lines <<< "$run"
        {{ generator }} scale --seed "$seed" --lines "$lines" --out "$out/scale-ocaml-$seed-$lines"
        "$out/scale" --seed "$seed" --lines "$lines" --out "$out/scale-stilt-$seed-$lines"
        diff -r "$out/scale-ocaml-$seed-$lines" "$out/scale-stilt-$seed-$lines"
    done
    echo "scale: 12 projects equal"

# Replay the edit script on the 50K-line project against a warm query database, 100 edits of each
# kind, directly and through the language server: time each edit, under 25 ms at the 95th
# percentile for body and signature edits through the language server and 50 ms directly, 100 ms
# for type edits, none over 250 ms, and count
# the bodies it checks again (goals edit-to-diagnostics, body-edits-recheck-one-body and
# no-slow-edit). Replay a
# shorter script comparing each step with a clean check (incremental-equals-clean), whose clean
# checks cost more than the edits. Then time every body of the stress suite (bounded-checking), and replay
# the edit script on the 100K-line project held in an image, 100 edits of each kind, timing each
# edit until its new code is live, under 250 ms at the 95th percentile and 100 ms for body edits
# (edit-to-running-program), and checking after each that the image holds the code that walking and
# counting the program afresh gives each function it reaches (incremental-equals-clean). Each replay splits its
# updates' time into validation, analysis, code generation and patching. Then time each answer
# of a session of the REPL on the 100K-line project, under 50 ms (interactive-evaluation), a clean check of it,
# under 1 s (clean-check), and a clean debug build of it, under 2 s (clean-debug-build). Last, replay the edit
# script of the compile-time benchmark on the benchmark and its baseline, each held by an engine,
# timing each edit until the debug executable is built again: the benchmark within 1.2 times its
# baseline's time (compile-time-code-rebuilds). The timings are of a release build.
[doc('Time edit-to-diagnostics and the other interactive operations on the large projects.')]
[group('performance')]
latency: build
    #!/usr/bin/env bash
    set -euo pipefail
    [ -n "${STILT_BUILT:-}" ] || cargo build --release --workspace
    rm -rf target/latency
    {{ generator }} scale --seed 1 --lines 50000 --out target/latency/lines_50k
    {{ generator }} scale --seed 2 --lines 100000 --out target/latency/lines_100k
    {{ generator }} stress --seed 2 --count 200 --out target/latency/stress
    target/release/stilt-latency edits target/latency/lines_50k
    target/release/stilt-latency edits --edits 24 --compare target/latency/lines_50k
    target/release/stilt-latency lsp --stilt target/release/stilt target/latency/lines_50k
    target/release/stilt-latency bodies target/latency/stress
    target/release/stilt-latency hot target/latency/lines_100k
    target/release/stilt-latency repl --stilt target/release/stilt target/latency/lines_100k
    TIMEFORMAT=%R
    seconds=$( { time target/release/stilt check target/latency/lines_100k > /dev/null; } 2>&1 )
    target/release/stilt engine --stop target/latency/lines_100k
    echo "a clean check of the 100K-line project takes $seconds s"
    if (( $(echo "$seconds >= 1" | bc) )); then
        echo "ERROR clean-check: a clean check takes $seconds s, over 1 s"
        exit 1
    fi
    seconds=$( { time target/release/stilt build -o target/latency/lines_100k.exe \
        target/latency/lines_100k > /dev/null; } 2>&1 )
    target/release/stilt engine --stop target/latency/lines_100k
    echo "a clean debug build of the 100K-line project takes $seconds s"
    if (( $(echo "$seconds >= 2" | bc) )); then
        echo "ERROR clean-debug-build: a clean debug build takes $seconds s, over 2 s"
        exit 1
    fi
    target/release/stilt-latency compile-time --stilt target/release/stilt --out target/latency/compile-time bench/compile-time

# Build the 100K-line project by way of an engine and replay the edit script on it ten times:
# the engine's cache stays under 500 MB and its footprint under 1 GB, and the cache doesn't grow
# from one replay to the next (bounded-cache).
# It measures memory, not time, so `just ci` runs it beside other recipes.
[doc("Check that an engine's cache stays bounded across replays of the edit script.")]
[group('performance')]
memory: build
    [ -n "${STILT_BUILT:-}" ] || cargo build --release --workspace
    rm -rf target/memory
    {{ generator }} scale --seed 2 --lines 100000 --out target/memory/lines_100k
    target/release/stilt-latency memory --stilt target/release/stilt target/memory/lines_100k

# Time Stilt's release builds against other languages, against no budget (bench/compare/): the
# Perceus paper's programs in Stilt, Rust, Koka, OCaml, Haskell, Swift and Java, and the benchmark
# suite's in Stilt, Rust, Go, Swift and OCaml, each built with its language's release flags, and
# checked to print what the Rust version prints. Go and Koka come from their release archives,
# which bench/compare/toolchains.sh downloads into target/toolchains/; the others are the
# machine's, and a language whose toolchain is missing is left out. It writes
# target/compare/results.md and results.json, then times the edit loop of the same 50K-line
# project in Stilt, Rust, Go, OCaml and Swift (bench/compare/README.md, The edit loop) into
# target/shootout/results.md. It times programs, so `just ci` doesn't run it.
[doc('Time the benchmark programs against their versions in other languages.')]
[group('performance')]
compare *args: build
    #!/usr/bin/env bash
    set -euo pipefail
    [ -n "${STILT_BUILT:-}" ] || cargo build --release --workspace
    toolchains=$(bench/compare/toolchains.sh)
    ocamlopt=$(opam exec --switch={{ switch }} -- which ocamlopt 2>/dev/null || echo ocamlopt)
    ghc=$(command -v ghc || echo "$HOME/.ghcup/bin/ghc")
    rustc=$(rustup which rustc 2>/dev/null || command -v rustc)
    cargo=$(rustup which cargo 2>/dev/null || command -v cargo)
    # shellcheck disable=SC2086
    target/release/stilt-bench compare --rustc "$rustc" --cargo "$cargo" --ocamlopt "$ocamlopt" \
        --ghc "$ghc" $toolchains {{ args }}
    dune=$(opam exec --switch={{ switch }} -- which dune 2>/dev/null || echo dune)
    go=$(echo "$toolchains" | sed -n 's/.*--go \([^ ]*\).*/\1/p')
    target/release/stilt-bench shootout --cargo "$cargo" --dune "$dune" --go "${go:-go}"

# Report which paragraphs of the Reference the conformance tests of every tier
# cite, and which codes of the registry they expect, failing when a paragraph's `Tests:` line
# doesn't link a test that cites it (conformance.rule-citations), after checking that what the
# registry generates, the list of codes expected among it, is current.
# Pass conformance/_pending to count the drafts too.
[doc('Report which paragraphs of the Reference the conformance tests cite.')]
[group('conformance')]
coverage *paths: build
    target/bin/stilt-registry --check
    {{ runner }} --coverage reference {{ paths }}

# Measure which lines of the toolchain's crates the tests run, under a build that
# `cargo llvm-cov` instruments in target/covered: the workspace's tests, the conformance suite
# and the guide's examples through the compiler, and the release lane's tests built with
# `stilt build --release`. Each engine they start writes its profile once it idles out, which
# the recipe waits for. It writes target/covered/README.md, the lines and functions run of each
# crate, which goes with each release (RELEASING.md), and target/covered/html, then removes the
# profiles, which take about 10 GB. It needs cargo-llvm-cov and the LLVM tools of rustc's LLVM,
# rustup's llvm-tools or LLVM_COV and LLVM_PROFDATA, and rebuilds the workspace, so `just ci`
# doesn't run it.
[doc('Measure which lines of the toolchain the tests run.')]
[group('test')]
covered: build
    #!/usr/bin/env bash
    set -euo pipefail
    out=$PWD/target/covered
    export CARGO_TARGET_DIR=$out CARGO_LLVM_COV_TARGET_DIR=$out CARGO_LLVM_COV_BUILD_DIR=$out
    eval "$(cargo llvm-cov show-env --sh)"
    export LLVM_PROFILE_FILE=$out/stilt-%p-%10m.profraw
    cargo llvm-cov clean --workspace
    cargo build -q --workspace
    ln -sfn ../../stilt-toolchain "$out/debug/stilt-toolchain"
    cargo test -q --workspace
    runner=$out/debug/stilt-test
    $runner --impl tools/runner/covered.sh --kinds run,check,test
    $runner --impl tools/runner/covered.sh --kinds run,check,test --examples "$out/examples" \
        docs/guide
    $runner --impl tools/runner/covered-release.sh --kinds run --fast --sample-key release
    $runner --impl tools/runner/covered-release.sh --kinds run {{ specialized }}
    for _ in $(seq 150); do
        pgrep -f "$out/debug/stilt engine" > /dev/null || break
        sleep 1
    done
    cargo llvm-cov report --json --summary-only --output-path "$out/summary.json"
    cargo llvm-cov report --html --output-dir "$out/html" > /dev/null
    uv run tools/release/covered.py "$out/summary.json" > "$out/README.md"
    rm -f "$out"/*.profraw "$out"/*.profdata
    cat "$out/README.md"

# Build the Lean model of the core calculus, failing on any warning, which is
# how Lean reports a `sorry`, and on any axiom of its own (goal sound-typing),
# then run its executable semantics over the conformance suite's run tests: each
# program it doesn't decline must give what its test expects, and it may decline only the
# tests that tools/runner/model-declines.txt lists (formal/README.md, Executable semantics).
[doc('Build the Lean model, and run the conformance suite in it.')]
[group('test')]
formal: build
    cd formal && lake build --wfail Stilt stilt-model
    if git grep -nwE 'axiom' -- 'formal/*.lean'; then \
        echo "ERROR the model above declares an axiom"; exit 1; \
    fi
    # The soundness theorem rests on Lean's three standard axioms and on nothing else, which
    # `native_decide` or a declaration of an axiom's type through a macro would add.
    printf 'import Stilt\n#print axioms Stilt.soundness\n' > target/axioms.lean
    axioms=$(cd formal && lake env lean ../target/axioms.lean); \
    if [ "$axioms" != "'Stilt.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]" ]; then \
        echo "ERROR $axioms"; exit 1; \
    fi
    {{ runner }} --impl tools/runner/model.sh --declines 77 --locations absent --time-limit 90 \
        --known-declines tools/runner/model-declines.txt --kinds run --logs target/model-logs
    just proof-map --check

# Map the Lean model (tools/proof-map/README.md) into target/proof-map/map.json, which
# the site's proof map shows: every declaration with what its statement and proof use,
# what the soundness theorem reaches, and which paragraphs of the Reference it covers.
# Fails on a citation of no paragraph, and on anything resting on `sorry` or on an axiom
# beyond Lean's three. Writes the Modules and Theorems tables of formal/README.md from the map,
# or with `--check`, fails when they differ from what it would write.
[doc('Map the Lean model against the Reference, for the site.')]
[group('test')]
proof-map *check:
    mkdir -p target/proof-map
    cd tools/proof-map && lake build proof-map && lake exe proof-map ../.. ../../target/proof-map/map.json
    python3 tools/proof-map/tables.py target/proof-map/map.json formal/README.md {{ check }}

# Approve the drafts under the paths that cite only paragraphs of the Reference, moving
# each out of `_pending/`.
[doc('Move the drafts that cite paragraphs of the Reference out of `_pending/`.')]
[group('conformance')]
approve *paths="conformance/_pending":
    cargo build --workspace
    {{ runner }} --approve reference {{ paths }}

# Run a deterministic sample of the conformance suite, chosen by a key.
[group('conformance')]
conformance-fast key="local": build
    {{ runner }} --impl {{ interpreter }} --fast --sample-key {{ key }}

# Check that what the registry of codes generates is current, that each diagnostics program
# renders as its snapshot, and that every code checked so far has one (goals
# one-diagnostic-shape and reviewed-messages).
[doc('Check that what the registry generates is current, and that each diagnostics program renders as its snapshot.')]
[group('test')]
diagnostics:
    cargo run -q -p stilt-registry -- --check
    cargo test --workspace --test snapshots

# Draft the snapshot of each program in tests/diagnostics/_pending/: the rendering that
# `stilt check` gives it, to be reviewed (goal reviewed-messages). A program with an
# `edits` file beside it is checked with those edits, an address and a text on alternate lines
# (edits.refusals), and one with a `repos` fixture beside it with the repositories built from
# it (packages.versions, packages.fetching and versions.selection).
[doc('Draft the snapshot of each program in tests/diagnostics/_pending/.')]
[group('test')]
snapshots-draft: build
    cargo test --workspace --test snapshots -- --ignored --exact draft

# Accept the reviewed snapshots, moving each program and snapshot out of
# tests/diagnostics/_pending/ in place of any older one (goal reviewed-messages), and write
# their renderings into the error index.
[doc('Accept the reviewed snapshots of tests/diagnostics/_pending/, and write them into the error index.')]
[group('test')]
snapshots-accept:
    #!/usr/bin/env bash
    set -euo pipefail
    # Each accepted snapshot is named: its diff in the pull request is the record of its review.
    shopt -s nullglob
    for draft in tests/diagnostics/_pending/*; do
        name="$(basename "$draft")"
        [[ -n "$name" ]] && rm -rf -- "tests/diagnostics/$name"
        mv -- "$draft" "tests/diagnostics/$name"
        echo "accepted tests/diagnostics/$name"
    done
    cargo run -q -p stilt-registry

# Check that every diagnostic of the snapshot programs is under 40 tokens (goal short-messages):
# its message and labels, counted by each tokenizer of tests/diagnostics/tokens.py.
[doc("Check that the message and labels of each snapshot program's diagnostic make fewer than 40 tokens.")]
[group('test')]
diagnostics-tokens: build
    uv run tests/diagnostics/tokens.py {{ compiler }}

# Check the token-cost programs and recount their tokens.
[group('performance')]
token-cost:
    uv run tools/measurements/token-cost/measure.py --check
