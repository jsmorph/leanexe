#!/usr/bin/env bash
set -euo pipefail

project=/mnt/vq/leanexe-riemann-20260911-blocks-script
runner=/mnt/vq/leanrunner-release-20260911-297b46c-leanexe
installed=/mnt/vq/leanexe-riemann-20260911-stream/build/tools
node=$installed/node-v24.13.0-linux-x64/bin/node
remote=false
if [[ ${1:-} == --remote ]]; then remote=true; shift; fi
[[ $# == 2 ]] || { printf '%s\n' 'Usage: euler-riemann-dev.sh start|status|log|result benchmark|run' >&2; exit 2; }
action=$1
phase=$2
case $phase in
    benchmark) job=leanexe-riemann-blocks-192-20260911-1; duration=1800 ;;
    run) job=leanexe-riemann-blocks-800-20260911-1; duration=21600 ;;
    *) printf '%s\n' 'Expected benchmark or run' >&2; exit 2 ;;
esac
case $action in start|status|log|result|execute) ;; *) exit 2 ;; esac

if [[ $remote == false ]]; then
    [[ $action != execute ]] || exit 2
    exec /home/somebody/src/vq/tools/dev-ssh dev "bash $project/tools/euler-riemann-dev.sh --remote $action $phase"
fi

case $action in
    status|log|result) exec "$runner/leanrun-job" "$action" "$job" ;;
    start)
        active=$(systemctl --user list-units 'leanrun-job-*.service' --type=service --state=active,activating,deactivating --no-legend)
        [[ -z $active ]] || { printf '%s\n' "$active" >&2; exit 2; }
        if [[ $phase == run ]]; then
            "$runner/leanrun-job" result leanexe-riemann-blocks-192-20260911-1
        fi
        export LEANRUN_WORKDIR=$project
        export LEANRUN_TOOLCHAIN=/mnt/vq/elan/toolchains/leanprover--lean4---v4.34.0-rc2
        export LEANRUN_TIMEOUT=$duration LEANRUN_JOB_ID=$job
        export LEANRUN_MEMORY_HIGH=16G LEANRUN_MEMORY_MAX=20G LEANRUN_SWAP_MAX=0
        export LEANRUN_CPU_QUOTA=2400% LEANRUN_TASKS_MAX=1024
        exec "$runner/leanrun-dev-submit" bash "$project/tools/euler-riemann-dev.sh" --remote execute "$phase"
        ;;
    execute)
        cd "$project"
        export WASMTIME_C_API=$installed/wasmtime/wasmtime-v44.0.0-x86_64-linux-c-api
        if [[ $phase == benchmark ]]; then
            "$node" tools/euler-block-run.mjs run 192 tmp/riemann-blocks-192
            cmp tmp/riemann-blocks-192/run.ndjson /mnt/vq/leanexe-riemann-20260911-libm/tmp/euler-2d-run-5lFzER/run.ndjson
            printf '%s\n' 'Complete 192-grid record matches serial benchmark'
        else
            "$node" tools/euler-block-run.mjs run 800 tmp/riemann-blocks-800
            "$node" tools/euler-riemann-large.mjs write tmp/riemann-blocks-800/run.ndjson data/euler-riemann-800-v1
            "$node" tools/euler-riemann-large.mjs check data/euler-riemann-800-v1
        fi
        ;;
esac
