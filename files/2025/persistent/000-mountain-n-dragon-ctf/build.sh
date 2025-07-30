#!/bin/bash

SCRIPT_DIR=$(dirname "$(readlink -f "$0")")

build() {
    basename="$1"

    npx esbuild "$basename.ts" --bundle --format=iife --outfile=build/$basename.js
}

pushd $SCRIPT_DIR

build mountdrag.re

popd
