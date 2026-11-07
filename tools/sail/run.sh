#!/bin/sh
# Usage: run.sh LOG MEMORY CPUS SECONDS COMMAND [ARGS]
# Runs COMMAND in a new session under a user scope with MemoryMax=MEMORY, CPUQuota=CPUS*100%, and
# a timeout, through GNU time -v.  Writes the session ID to LOG.pid and the output to LOG.out,
# followed by the elapsed seconds and "exit STATUS".
set -eu
if [ "$#" -lt 5 ]; then
  echo "usage: run.sh LOG MEMORY CPUS SECONDS COMMAND [ARGS]" >&2
  exit 2
fi
log=$1
mem=$2
cpus=$3
secs=$4
shift 4
rm -f "$log.pid" "$log.out"
setsid sh -c '
  log=$1 mem=$2 cpus=$3 secs=$4
  shift 4
  echo $$ >"$log.pid"
  start=$(date +%s)
  unit="f7-$$"
  status=0
  systemd-run --user --scope --unit="$unit" -p MemoryMax="$mem" -p MemorySwapMax=0 \
    -p CPUQuota="$((cpus * 100))%" \
    timeout "$secs" /usr/bin/time -v "$@" >"$log.out" 2>&1 || status=$?
  echo "elapsed $(( $(date +%s) - start )) s" >>"$log.out"
  echo "exit $status" >>"$log.out"
' sh "$log" "$mem" "$cpus" "$secs" "$@" </dev/null >/dev/null 2>&1 &
i=0
while [ ! -s "$log.pid" ]; do
  i=$((i + 1))
  if [ "$i" -gt 100 ]; then
    echo "run.sh: no session ID for $log" >&2
    exit 1
  fi
  sleep 0.1
done
echo "session $(cat "$log.pid")"
