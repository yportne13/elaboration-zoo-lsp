#!/bin/bash
cd "F:/projects/hermes/elaboration-zoo-lsp"
for i in $(seq 1 10); do
  echo "=== Push attempt $i ==="
  if git push; then
    echo "=== Push succeeded! ==="
    exit 0
  fi
  echo "Attempt $i failed, waiting 10s..."
  sleep 10
done
echo "=== All 10 attempts failed ==="
exit 1
