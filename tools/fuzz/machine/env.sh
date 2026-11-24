# Shared settings of the fuzzing machine's scripts.
export REPO_URL=https://github.com/stilt-lang/stilt.git
export REPO=stilt-lang/stilt
export FUZZ=$HOME/fuzz
export SRC=$FUZZ/stilt            # the checkout of main that the workers run
export STATE=$FUZZ/state          # seeds, the commit built, what was reported
export FINDINGS=$FUZZ/findings    # one directory per failure, until it is reported
export CORPUS=$FUZZ/corpus        # cargo fuzz's corpora, kept across builds
export PATH=$HOME/.cargo/bin:$HOME/.local/bin:/usr/local/bin:$PATH
mkdir -p "$STATE" "$FINDINGS" "$CORPUS"
