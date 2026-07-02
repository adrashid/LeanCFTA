# LeanCFTA
LeanCFTA: Formalization of Coherent Fault Trees in Lean 4

LeanCFTA is a machine-checked formalization of coherent fault trees in the Lean 4 theorem prover.

The project provides a formally verified framework for

- coherent fault-tree syntax
- qualitative structural analysis
- Boolean cut-set semantics
- cut-set generation
- soundness proofs
- minimal cut-set generation
- an autonomous emergency braking case study

All definitions and proofs are fully machine checked in Lean 4.

----------------------------------------------------------------------------------------

Motivation

Fault Tree Analysis (FTA) is one of the most widely used safety analysis techniques for dependable and safety-critical systems.

Although numerous algorithms exist for qualitative fault-tree analysis, they are usually implemented using conventional software and therefore rely on testing for correctness.

LeanCFTA develops a machine-checked formalization of coherent fault trees in Lean 4, providing mathematically verified algorithms for structural analysis and cut-set generation together with machine-checked correctness proofs.
