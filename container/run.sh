#!/bin/bash

script_path=$(readlink -f -- "$0")
dir=$(dirname -- $script_path)

docker build $dir -t tla
docker run -it -v $dir/../src:/root/src tla

