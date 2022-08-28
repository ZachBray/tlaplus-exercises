#!/bin/bash

set -euf -o pipefail

script_path=$(readlink -f -- "$0")
bin_dir=$(dirname -- $script_path)
java -XX:+UseParallelGC -cp "$bin_dir/*" tlc2.TLC "$@"

