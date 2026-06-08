#!/bin/bash
cd /f/projects/hermes/elaboration-zoo-lsp
for i in $(seq 1 10); do
    echo "=== Attempt $i/10 ==="
    if git push origin master 2>&1; then
        echo "=== PUSH SUCCESSFUL ==="
        exit 0
    fi
    echo "Failed, waiting 30s..."
    sleep 30
done
echo "=== ALL ATTEMPTS FAILED ==="
exit 1
