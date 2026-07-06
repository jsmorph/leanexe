#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case order_book \
  --module LeanExe.Examples.OrderBook \
  --entry LeanExe.Examples.OrderBook.matchBook \
  --spec Project.OrderBook.Spec \
  --program Project/OrderBook/Program.lean \
  "$@"
