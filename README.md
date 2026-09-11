# LeanCFTA

LeanCFTA is a machine-checked Lean 4 framework for the formal
modeling and verified analysis of coherent fault trees.

The framework provides:

- coherent fault-tree syntax using basic events, AND gates, and OR gates;
- executable Boolean semantics;
- qualitative structural analysis;
- recursive cut-set generation;
- machine-checked soundness and coverage proofs;
- verified semantic minimal cut-set computation;
- a counterexample-oriented validation suite; and
- an Autonomous Emergency Braking case study.

## Verified Guarantees

LeanCFTA establishes the following generic results for coherent
fault trees.

### Soundness

Every set produced by `cutSets` is a semantic cut set:

```lean
theorem cutSets_sound
