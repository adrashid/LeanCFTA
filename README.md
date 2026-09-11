# LeanCFTA

LeanCFTA is a machine-checked Lean 4 framework for the formal modeling and verified analysis of coherent fault trees.

The framework provides:

* coherent fault-tree syntax using basic events, AND gates, and OR gates;
* executable Boolean semantics;
* qualitative structural analysis;
* recursive cut-set generation;
* machine-checked soundness and coverage proofs;
* verified semantic minimal cut-set computation;
* a counterexample-oriented validation suite; and
* an Autonomous Emergency Braking case study.

## Verified Guarantees

LeanCFTA establishes the following generic results for coherent fault trees.

### Soundness

Every set produced by `cutSets` is a semantic cut set:

```lean
theorem cutSets_sound
```

Formally:

```text
C ∈ cutSets t → IsCutSet C t
```

### Coverage

Every semantic cut set contains a recursively generated cut set:

```lean
theorem cutSets_cover
```

Formally:

```text
IsCutSet C t →
  ∃ D, D ∈ cutSets t ∧ D ⊆ C
```

### Global Semantic Minimality

Every set returned by `minimalCutSets` satisfies the global semantic definition of a minimal cut set:

```lean
theorem minimalCutSets_globally_minimal
```

Formally:

```text
C ∈ minimalCutSets t → MinimalCutSet C t
```

### Semantic Completeness of Minimal Cut Sets

Every semantically minimal cut set is returned by `minimalCutSets`:

```lean
theorem minimalCutSets_complete_semantic
```

Formally:

```text
MinimalCutSet C t → C ∈ minimalCutSets t
```

The final semantic characterization is established by:

```lean
theorem mem_minimalCutSets_iff_semantic
```

which proves:

```text
C ∈ minimalCutSets t ↔ MinimalCutSet C t
```

Thus, the sets returned by `minimalCutSets` are exactly the semantic minimal cut sets.

## Counterexample-Oriented Validation

`FaultTree/CoherentValidation.lean` contains executable, machine-checked validation cases covering:

* nested AND and OR gates;
* repeated basic events;
* duplicate child subtrees; and
* the absorption expression `A ∨ (A ∧ B)`.

For the absorption case, the raw generator produces both `{A}` and `{A, B}`, while `minimalCutSets` correctly removes the absorbed superset and returns only `{A}`.

The validation file also proves that `{A, B}` remains a semantic cut set of `A ∨ (A ∧ B)` but is not a minimal cut set, whereas `{A}` satisfies the global semantic definition of minimality.

## Autonomous Emergency Braking Case Study

`FaultTree/CoherentCaseStudy.lean` formalizes an Autonomous Emergency Braking fault tree containing perception, decision, and actuation subsystems.

The executable analysis produces the following seven minimal cut sets:

* `{CameraFailure}`
* `{RadarFailure}`
* `{SensorFusionFailure}`
* `{ControllerFailure, SafetyMonitorFailure}`
* `{BrakeActuatorFailure}`
* `{HydraulicFailure}`
* `{PowerFailure}`

The case study includes executable computations and machine-checked theorems connecting the generated results with the formal fault-tree semantics.

## Project Structure

```text
LeanCFTA/
├── FaultTree/
│   ├── CoherentSyntax.lean
│   ├── CoherentQualitative.lean
│   ├── CoherentSemantics.lean
│   ├── CoherentCutSets.lean
│   ├── CoherentCaseStudy.lean
│   └── CoherentValidation.lean
├── FaultTree.lean
├── Main.lean
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── LICENSE
└── README.md
```

## Requirements

The project is configured and verified using:

```text
Lean 4.33.1
mathlib 4.33.1
```

Lean should be installed through `elan`.

## Installation

Clone the repository:

```bash
git clone https://github.com/adrashid/LeanCFTA.git
cd LeanCFTA
```

Download the dependencies:

```bash
lake update
```

Download the precompiled mathlib cache:

```bash
lake exe cache get
```

## Building the Project

Build and machine check the complete formalization:

```bash
lake build
```

A successful build checks:

* the coherent fault-tree syntax;
* the executable semantics;
* the qualitative structural results;
* cut-set soundness and coverage;
* global semantic minimality;
* semantic completeness of minimal cut-set computation;
* the counterexample-oriented validation suite; and
* the AEB case study.

## Using LeanCFTA

Import the complete library:

```lean
import FaultTree
```

Alternatively, import individual modules:

```lean
import FaultTree.CoherentSyntax
import FaultTree.CoherentQualitative
import FaultTree.CoherentSemantics
import FaultTree.CoherentCutSets
import FaultTree.CoherentCaseStudy
import FaultTree.CoherentValidation
```

## Opening the Project in Visual Studio Code

From the project directory, run:

```bash
code .
```

Open any `.lean` file to inspect its definitions, theorem statements, proof states, and executable evaluations using the Lean 4 extension.

To verify the entire project from the integrated terminal, run:

```bash
lake build
```

## Source Repository

The source code is available at:

https://github.com/adrashid/LeanCFTA
