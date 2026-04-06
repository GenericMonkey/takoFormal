#!/bin/bash

failed_files=()
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
DAFNY_DIR=$SCRIPT_DIR/../consistency_proof

run_dafny() {
  # --log-format text
  # --progress Batch
  # --performance-stats=1
  $DAFNY_DIR/dafny/dafny verify "$@"
}

check_error() {
  "$@"
  if [ $? -ne 0 ]; then
    echo "Error: $@ failed."
    failed_files+=("$2")
  fi
}

# Verify the Tako State Machine

echo "Verifying Tako State Machine Models..."
check_error run_dafny $DAFNY_DIR/model/tako.i.dfy
check_error run_dafny $DAFNY_DIR/model/tako_spec.i.dfy

# Verify the Relations Library
echo "Verifying Relations Library..."
check_error run_dafny $DAFNY_DIR/model/relations_library.i.dfy

# Axiom Spec Consistency Proofs
for file in $DAFNY_DIR/proof/soundness/spec_*; do 
  if [ -f "$file" ]; then
    echo "Verifying $file ..."
    check_error run_dafny "$file"
  fi 
done

# Refinement Proofs
while IFS= read -r file; do
  echo "Verifying $file ..."
  check_error run_dafny "$file"
done < <(find $DAFNY_DIR/proof/refinement -type f)

if [ ${#failed_files[@]} -ne 0 ]; then
  echo "The following files failed verification:"
  for f in "${failed_files[@]}"; do
    echo "  $f"
  done
  exit 1
fi