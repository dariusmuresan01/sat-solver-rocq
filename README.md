# Verified SAT Solver in Rocq

Built by **Darius Mureșan** and **Rui Xavier** for the *Formal Software Verification* course at Aarhus University (taught by Bas Spitters).

A naive, truth-table based Boolean satisfiability (SAT) solver written and **machine-checked** in the Rocq (Coq) proof assistant. The goal is not speed but certainty: the solver is proven both **sound** and **complete** with respect to the logical definition of satisfiability, and every formula transformation built on top of it is proven to preserve semantics.

## Table of Contents

- [Overview](#overview)
- [Repository Structure](#repository-structure)
- [Environment Setup](#environment-setup)
- [Building & Checking the Proofs](#building--checking-the-proofs)
- [Main Results](#main-results)
- [Extensions](#extensions)
- [Documentation](#documentation)

## Overview

| Component | What it is | Where |
|---|---|---|
| **Syntax** | Inductive type `form` of Boolean formulas (variables, ⊤, ⊥, ¬, ∧, ∨, →) | `sat_solver.v` |
| **Semantics** | Valuations `id -> bool` and the evaluator `interp` | `sat_solver.v` |
| **Specification** | `satisfiable p := exists V, interp V p = true` (a `Prop`, not executable) | `sat_solver.v` |
| **Implementation** | `solver : form -> bool`, an exhaustive search over the `2^n` valuations of the variables in `p` | `sat_solver.v` |
| **Verification** | `solver_sound` and `solver_complete`: `solver p = true <-> satisfiable p` | `sat_solver.v` |

The key insight is that `satisfiable` quantifies over an *infinite* space of valuations, while `solver` must terminate. The search is made finite by collecting the variables that actually occur in `p` (`vars`, `remove_dups`) and generating every assignment to just those variables (`all_valuations`).

## Repository Structure

```
.
├── docs/
│   └── report.pdf        # Full project report
├── project_lib.v         # Course library (identifiers, helper tactics; based on SfLib)
├── sat_solver.v          # Formulas, semantics, solver, proofs and extensions
├── Makefile
└── README.md
```

## Environment Setup

You need Rocq/Coq (tested with **Coq 8.18**; any recent 8.x or Rocq 9 should work). The development only uses the standard library.

**macOS (Homebrew)**
```bash
brew install coq
```

**Ubuntu / Debian**
```bash
sudo apt install coq
```

**Any platform (opam)**
```bash
opam install coq
```

For interactive proof stepping, use the VsRocq / VsCoq extension for VS Code, or CoqIDE.

## Building & Checking the Proofs

```bash
make          # compiles project_lib.v, then sat_solver.v
make clean    # removes build artefacts
```

A successful build means every lemma has been checked by the kernel. To confirm the main theorems rely on no axioms or `Admitted` proofs:

```coq
Require Import sat_solver.
Print Assumptions solver_sound.     (* Closed under the global context *)
Print Assumptions solver_complete.  (* Closed under the global context *)
```

You can also run the solver directly:

```coq
Compute solver ex1.                        (* = true  *)
Compute solver (FConj (var x) (FNeg (var x))).  (* = false *)
```

## Main Results

### Soundness

```coq
Lemma solver_sound : forall p, solver p = true -> satisfiable p.
```

If the solver says "satisfiable", the valuation it found is a witness for the existential. Proved via `find_sat_sound`: any valuation returned by the search makes the formula true.

### Completeness

```coq
Lemma solver_complete : forall p, satisfiable p -> solver p = true.
```

The harder direction. The hypothesis gives an arbitrary, global valuation `V`; the solver only inspects a finite list. The proof bridges the two with:

- **`interp_agreement`** – two valuations that agree on `vars p` give the same result on `p`.
- **`all_valuations_covers`** – for any list of variables `l` and any `V`, some `V'` in `all_valuations l` agrees with `V` on `l`.
- **`in_remove_dups`**, **`mem_id_iff`** – removing duplicates does not lose any variable.
- **`find_sat_exists`** – if a satisfying valuation is in the list, the search returns `Some _`.

## Extensions

| Extension | Definitions | Correctness result |
|---|---|---|
| **Three-valued logic** (True / False / Unknown) | `tri`, `interp3`, `satisfiable3` | `three_valued_consistency`: the 3-valued semantics agrees with the Boolean one on Boolean valuations |
| **Constant-folding optimizer** | `optimize`, `solver_opt` | `optimize_correct`, `solver_opt_sound` |
| **Negation Normal Form** | mutually recursive `to_nnf` / `neg_nnf`, `solver_nnf` | `nnf_equiv_mutual` (mutual induction), `nnf_correct`, `solver_nnf_sound` |
| **Conjunctive Normal Form** | `distribute`, `to_cnf`, `solver_cnf` | `distribute_correct`, `cnf_correct`, `solver_cnf_sound` |

Since each transformation is proven to preserve `interp`, soundness of the transformed solvers follows directly from `solver_sound`.

## Documentation

The full write-up, covering design decisions, proof strategies and our experience with Rocq, is in [`docs/report.pdf`](docs/report.pdf).

### References

- B. C. Pierce et al., *Software Foundations, Vol. 1: Logical Foundations*. `project_lib.v` is adapted from its `SfLib.v`.
- The Rocq Prover reference manual: https://rocq-prover.org/doc
