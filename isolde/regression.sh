#!/bin/bash

# Iterate i from 0 to 10
for i in {0..10}; do
  echo "Running test with IMEM_LATENCY=$i"
  make -C tca_system IMEM_LATENCY=$i PE=redmule TEST=redmule_complex_32b   verilate test-build veri-run
  make -C tca_system IMEM_LATENCY=$i PE=redmule TEST=redmule_complex_128b  verilate test-build veri-run

  # Check if the command succeeded
  if [ $? -ne 0 ]; then
    echo "Error: make failed for IMEM_LATENCY=$i"
    exit 1
  fi
done

echo "All runs completed successfully!"
