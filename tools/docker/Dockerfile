# syntax=docker/dockerfile:1
# An image of a release: Debian with `stilt` installed by install.sh, which checks the release's
# signature as it does on any machine, for the architecture Docker builds for, x86-64 or aarch64.
# `docker build -t stilt tools/docker`, with install.sh copied in, builds it, and
# `docker run --rm -v "$PWD:/work" stilt run` runs the program in the working directory.
# STILT_DIST and STILT_RELEASE_KEY, as install.sh reads them, build it from archives elsewhere,
# as a test of the image does.
FROM debian:stable-slim

ARG VERSION=latest
ARG STILT_DIST=https://github.com/stilt-lang/stilt/releases
ARG STILT_RELEASE_KEY=

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl openssh-client \
    && rm -rf /var/lib/apt/lists/*

# The build context's `dist/`, empty for a release, holds the archives of a local test; it is
# mounted for the install alone, so the image keeps none of it.
RUN --mount=type=bind,source=install.sh,target=/tmp/install.sh \
    --mount=type=bind,source=dist,target=/tmp/dist \
    if [ -n "$STILT_RELEASE_KEY" ]; then export STILT_RELEASE_KEY; fi \
    && STILT_DIST=$STILT_DIST STILT_HOME=/opt/stilt sh /tmp/install.sh --version "$VERSION"

ENV PATH=/opt/stilt/bin:$PATH
WORKDIR /work
ENTRYPOINT ["stilt"]
CMD ["--help"]
