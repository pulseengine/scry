#!/usr/bin/env bash
# Install a prebuilt pulseengine binary from a GitHub release into
# $RUNNER_TEMP/bin and put it on PATH. Used by the jobs that run on the
# self-hosted `light` runners, which must not compile tools from source.
#
# Usage: tools/ci/install-release-bin.sh <repo> <binary> <tag>
#   e.g. tools/ci/install-release-bin.sh rivet rivet v0.42.2
set -euo pipefail

repo=$1 bin=$2 tag=$3
asset="$bin-$tag-x86_64-unknown-linux-gnu.tar.gz"
dest="${RUNNER_TEMP:?}/bin"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

mkdir -p "$dest"
curl -fsSL --retry 3 -o "$work/$asset" \
  "https://github.com/pulseengine/$repo/releases/download/$tag/$asset"
tar xzf "$work/$asset" -C "$work"
found=$(find "$work" -type f -name "$bin" -perm -u+x | head -1)
test -n "$found" || { echo "no '$bin' binary in $asset" >&2; exit 1; }
install -m 0755 "$found" "$dest/$bin"
echo "$dest" >> "$GITHUB_PATH"
"$dest/$bin" --version
