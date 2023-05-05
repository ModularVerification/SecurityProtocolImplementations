#!/bin/bash

# exit when any command fails
set -e

VERIFAST_BIN="$PWD/../verifast-21.04/bin"

verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c crypto_lib.c 
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c definitions.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c encryption.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c event_lemmas.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c ghost_trace.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c inv_finder.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c io.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c secrecy.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c terms.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c trace_helpers.c
verifast -disable_overflow_check -allow_dead_code -shared -allow_assume -c trace_manager.c
# note that `protocol_specific_lemmas.c` is not verify as it must be shown by each protocol
# as the proof relies on protocol-specific definitions.
