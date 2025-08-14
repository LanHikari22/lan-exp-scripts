#!/bin/bash

app_name="TODO app name"

script_dir=$(dirname "$(realpath "$0")")
project_dir="$script_dir"

script -q -c "cd $project_dir; mypy --strict -m $app_name.main" /dev/null | tac
