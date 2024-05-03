#!/bin/bash

params=()

if [[ -n "$CI" ]]; then
    params=("--wait_for_results")
fi

certoraRun certora/conf/RecoveryModule.conf \
    "${params[@]}" \
    "$@"
