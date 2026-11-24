# The Docker image

[`Dockerfile`](Dockerfile) builds an image of a release: Debian with `stilt` installed by [`install.sh`](../../install.sh), which checks the release's signature as it does on any machine, for x86-64 or aarch64 Linux, whichever Docker builds for. The build context is this directory with `install.sh` copied in and a `dist/` directory, empty to install a published release, the latest unless `--build-arg VERSION=…` names one:

```sh
cp install.sh tools/docker/ && mkdir -p tools/docker/dist
docker build -t stilt tools/docker
docker run --rm -v "$PWD:/work" stilt run .
```

To build the image from archives of your own, put them, their `SHA256SUMS` and its signature in `dist/`, and pass `--build-arg STILT_DIST=/tmp/dist --build-arg STILT_RELEASE_KEY="ssh-ed25519 …"`, the public key that signed them. The archives are mounted for the install alone, so the image keeps none of them. Most of its size is the LLVM library that the linker loads.
