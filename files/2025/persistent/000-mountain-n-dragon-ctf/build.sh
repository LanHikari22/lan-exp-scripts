#!/bin/bash

SCRIPT_DIR=$(dirname "$(readlink -f "$0")")

build() {
    basename="$1"

    npx esbuild "$basename.ts" --bundle --format=iife --outfile=build/$basename.js
    cat build/$basename.js | python3 -c "import sys; lines = sys.stdin.read().split('\n'); print('\n'.join(lines[1:-2]))" > build/tmp
    cat build/tmp > build/$basename.js
    rm build/tmp
}

pushd $SCRIPT_DIR

build mountdrag

popd
