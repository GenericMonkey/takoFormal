# TakoFormal

This repository houses the artifact for the ISCA '26 paper "täkōFormal: Enabling Robust Software for Programmable Memory Hierarchies". The 2 main components are:

1) A Dafny end-to-end machine checked proof of axiomatic consistency for a state machine representation of the täkō hardware ($\S$ VII), which can be explicitly verified.
1) An Alloy encoding of the axioms (Figure 6) along with the täkō litmus tests presented in the paper, which can be run to confirm the results presented in the paper are consistent with our axioms.

## Project Layout

This artifact has 2 main directories.

### `consistency_proof/`

This houses the Dafny proof of soundness for the axioms described in the paper.

#### `model/`

This directory houses the implementation of the state machine representation of the täkō hardware (`tako.i.dfy`) as well as the intermediate state machine model described in the paper (`tako_spec.i.dfy`).

The list of axioms verified is contained in `execution.i.dfy`, which correspond to those presented in Figure 6 in the paper.

#### `proof/`

As described in the $\S$ VII, the proof of soundness is decomposed into two proofs.

##### `refinement/`

This directory contains the proof that the full state machine (`tako.i.dfy`) refines the intermediate state machine (`tako_spec.i.dfy`). The root file of the theorem statement is contained in `refinement.i.dfy`, and is segmented into proofs for each type of action that can be taken. `refinement_defns.i.dfy` houses all the additional invariants that were required to prove this theorem, and proofs of those invariants that were not assumed axiomatically (coherence properties as discussed in $\S$ VII-E). Proofs of the invariants holding are housed in the `invproofs/` subdirectory.

##### `soundness/`

The axioms in Figure 6 are each verified independently in a separate proof file, while relying on a shared `invariants.i.dfy` housing additional invariants required to complete each proof.

### `mcm/`

This directory houses the Alloy model presenting the same axioms, as well as the täkō litmus tests presented in the paper. The `tako.als` contains the axioms and the base model, and each additional `.als` file corresponds to a litmus test presented in the paper.

## Installation

The following instructions have been tested on an 12th Gen Intel(R) Core(TM) i7-1280P Windows Laptop (32 GB RAM) running Windows 11 Enterprise 23H2. Libraries and installation for other OS may differ. Also, Dafny is known to have brittleness issues across architectures. Please contact if some proof is timing out or throwing an internal error.

### Dependencies

#### Dafny 4.11.0

[Full Dafny Installation Details](https://dafny.org/latest/Installation#install-the-binaries-from-the-github-releases) can be found in the linked document. Ensure that [Dafny 4.11.0](https://github.com/dafny-lang/dafny/releases/tag/v4.11.0) is installed as opposed to latest. The Dafny Compiler is not necessary to verify the implementation.

The scripts to run verification assume that Dafny has been installed in the `consistency_proof/` directory. That is, the directory should look like:

```txt
consistency_proof/
|__ model/
|__ proof/
|__ dafny/
    |__ dafny executable
```

This can be accomplished by extracting the appropriate `.zip` installation into the `consistency_proof/` folder.

#### Alloy 6.2.0

1. Alloy depends on an installation of Java (Java 17 or later according to [Alloy Requirements](https://github.com/AlloyTools/org.alloytools.alloy?tab=readme-ov-file#requirements)) to run. The scripts for verifying the alloy tests were run using java version: `java 24.0.1 2025-04-15`.

2. Install [Alloy 6.2.0](https://github.com/AlloyTools/org.alloytools.alloy/releases/tag/v6.2.0). The full installation is not necessary, just [`org.alloytools.alloy.dist.jar`](https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar). It is a self-contained `.jar` file, which should be stored in the `mcm/` directory for the verification script to run correctly.

## Verifying Results

### Alloy Litmus Tests

The verification of the claims made about the litmus tests in the paper and the mapping to specific files in this directory is presented in the following table.

|Paper Figure|Claimed Result|Corresponding File|
|---|---|---|
|Figure 4a|`r1 = 2, r2 = 0` forbidden|`test_paper_ex.als`|
|Figure 5a|`r1 = 1, r2 = 0` *allowed* (see $\S$ V-A)|`test_mp.als`|
|Figure 5a (with RMW [b])|`r1 = 1, r2 = 0` forbidden (see $\S$ V-A)|`test_mp_rmw.als`|
|Figure 9a (w/o i2)|is racy|`test_wbrace.als`|
|Figure 9a (w i2)|a) no race, b) `r1 = 0` forbidden|`test_wbflush.als`|
|Figure 10a (w/o i9)|is racy|`test_hatsr.als`|
|Figure 9a (w i9)|a) no race, b) `r1 != r2` forbidden|`test_hatsnr.als`|

#### Running Verification (Alloy Litmus Tests)

The above results can all be run using the following bash script, included in the run/ directory. From the root of the directory, run

```bash
./run/run_alloy_tests.sh
```

The output of this corresponds to the above table. As Alloy uses SAT solving to verify if outcomes are possible or not, the translation is given as part of the script output. For example, the expected output of the Figure 4a test should look like the following, as UNSAT corresponds to the the result that the result `r1 = 2, r2 = 0` is forbidden.

```txt
Running test_paper_ex.als...
00. run   forbidden                0       UNSAT
Expected Output: UNSAT (outcome impossible)
```

Conversely, SAT is expected when searching for racy executions and allowed outcomes.

The entire script should complete within 10 minutes (5m 5s when ran locally), with `test_hatsnr.als` taking the longest time to run.

### Soundness Proof

The following describes the details of running the machine checked proof of axiomatic consistency described in $\S$ VII.

#### Soundness of Axioms (on Intermediate State Machine)

Figure 6 contains a list of the axioms that are verified for the intermediate state machine discussed in $\S$ VII-B. The mapping is included in the table below.

|Paper Axiom Name|Corresponding File|Paper Axiom Name|Corresponding File|
|---|---|---|---|
|RfWf1|`spec_rfwf_mowf.i.dfy`|CboM|`spec_cbowf2_1.i.dfy`|
|RfWf2|`spec_rfwf_mowf.i.dfy`|CboE|`spec_cbowf2_2.i.dfy`|
|MoWf1|`spec_rfwf_mowf.i.dfy`|EvDirty|`spec_cbowf6.i.dfy`|
|MoWf2|`spec_rfwf_mowf.i.dfy`|WbDirty|`spec_cbowf6.i.dfy`|
|CboWf1|`spec_cbowf1.i.dfy`|OEInt|`spec_cbowf3_1.i.dfy`|
|CboWf2|`spec_cbowf1.i.dfy`|OMInt|`spec_cbowf3_2.i.dfy`|
|CboVal|`spec_cbowf5_1.i.dfy`, `spec_cbowf5_2.i.dfy`|OMThd|`spec_cbowf10_1.i.dfy`|
|ThdM|`spec_cbowf7.i.dfy`|OEThd|`spec_cbowf10_2.i.dfy`|
|ThdE|`spec_cbowf7.i.dfy`|MeInt|`spec_cbowf3_3.i.dfy`|
|DirtyWf|`spec_cbowf8.i.dfy`|EeInt|`spec_cbowf3_4.i.dfy`|
|Hb|`spec_hb.i.dfy`|VfWf|`spec_cbowf4_1.i.dfy`|
|Vis|`spec_Coh.i.dfy`|EfWf|`spec_cbowf4_2.i.dfy`|
|RMW|`spec_RMW.i.dfy`|EbWf|`spec_cbowf9.i.dfy`|
|VisCb|`spec_CbCoh.i.dfy`|||

#### Refinement Proof

The file `refinement.i.dfy` contains the overall proof obligation ensuring that every step of the model in `tako.i.dfy` can be thought of as a step of the intermediate state machine in `tako_spec.i.dfy`. This completes the end-to-end proof depicted in Figure 15. All other files in this directory are subobligations that connect to this proof.

#### Running Verification (Soundness Proof)

The above results can all be run using the following bash script, included in the run/ directory. From the root of the directory, run

```bash
./run/run_dafny_verification.sh
```

The output prints the verification status of each individual file as it iterates through all of them. Each individual file should have output listing how many lemmas or definitions were verified in the file. Any failed verification will result in an error being listed (in the case of brittleness, likely a timeout or internal error). An example of good output for a file looks like this:

```txt
Dafny program verifier finished with 58 verified, 0 errors
```

After completing all verification, the script will summarize by printing all files that failed verification. This should be empty (when ran with the Windows build).

The entire script should complete within 1.5 hours (~65 min when ran locally).
