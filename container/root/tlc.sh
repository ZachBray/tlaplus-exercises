#!/bin/bash

script_path=$(readlink -f -- "$0")
bin_dir=$(dirname -- $script_path)
java -XX:+UseParallelGC -cp $bin_dir/tla2tools.jar tlc2.TLC "$@"

