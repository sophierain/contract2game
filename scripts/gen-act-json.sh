#!/usr/bin/env bash

root=$(git rev-parse --show-toplevel)
find "$root/act_examples" -name '*.act' -exec sh -c 'i="$1"; echo "$i" && act type --file "$i" | jq . > $i.typed.json' shell {} \;
