#!/bin/bash

script_dir=$(dirname "$(realpath "$0")")
project_dir="$script_dir"

pushd $project_dir

python3 -m unittest

popd