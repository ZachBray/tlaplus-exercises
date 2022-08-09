#!/bin/bash

script_path=$(readlink -f -- "$0")
bin_dir=$(dirname -- $script_path)
java -cp $bin_dir/tla2tools.jar tla2sany.SANY "$@"

