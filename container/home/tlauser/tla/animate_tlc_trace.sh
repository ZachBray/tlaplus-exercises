#!/bin/bash

set -euf -o pipefail

spec=$1

shopt -s expand_aliases
source /home/tlauser/tla/aliases.sh

mkdir -p /tmp/tla/$spec

tlc -simulate -view $spec | tee /tmp/tla/$spec/trace.txt || true
grep "<g>" /tmp/tla/$spec/trace.txt | sed -E 's/^"//' | sed -E 's/"$//' > /tmp/tla/$spec/frames.txt

animfile="$spec.html"
grep -B 10000 "@SVG_TEXT@" /home/tlauser/tla/template.html > $animfile
cat /tmp/tla/$spec/frames.txt >> $animfile
grep -A 10000 "@SVG_TEXT@" /home/tlauser/tla/template.html >> $animfile

