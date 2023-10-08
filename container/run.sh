#!/bin/bash

set -euf -o pipefail

script_path=$(readlink -f -- "$0")
dir=$(dirname -- $script_path)

docker build $dir -t tla \
       --build-arg UID=$(id -u) \
       --build-arg GID=$(id -g)
docker run -it \
       -v $dir/../src:/home/tlauser/src \
       tla

