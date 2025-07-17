build() {
    basename="$1"

    npx esbuild "$basename.ts" --bundle --format=iife --outfile=build/$basename.body.js
    awk '/\/\/ ==\/UserScript==/ { print; exit } { print }' $basename.ts > build/$basename.js
    echo >> build/$basename.js
    cat build/$basename.body.js >> build/$basename.js
    rm build/$basename.body.js
}

build text-match-clicker