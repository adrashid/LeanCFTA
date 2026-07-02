import Mathlib

/-
  Syntax of coherent fault trees.

  This file defines the core language of coherent fault trees:
  basic events, AND gates, OR gates, smart constructors, and well-formedness.
-/

/--
`CGate` represents the gate types supported by coherent fault trees.

* `andGate` means all children must occur.
* `orGate` means at least one child must occur.
-/
inductive CGate where
  | andGate : CGate
  | orGate  : CGate
deriving Repr, DecidableEq

/--
`CFTree Event` is the type of coherent fault trees whose basic events
have type `Event`.

A coherent fault tree is either:
* `basic e`, representing a basic event `e`;
* `gate g ts`, representing an AND/OR gate `g` applied to child trees.
-/
inductive CFTree (Event : Type) where
  | basic : Event → CFTree Event
  | gate  : CGate → List (CFTree Event) → CFTree Event
deriving Repr

namespace CFTree

variable {Event : Type}

/-- Construct a basic event node. -/
def BE (e : Event) : CFTree Event :=
  basic e

/-- Construct an AND gate. -/
def AND (ts : List (CFTree Event)) : CFTree Event :=
  gate CGate.andGate ts

/-- Construct an OR gate. -/
def OR (ts : List (CFTree Event)) : CFTree Event :=
  gate CGate.orGate ts

/-- `isBasic t` is true exactly when `t` is a basic event node. -/
def isBasic : CFTree Event → Prop
  | basic _ => True
  | gate _ _ => False

/-- `isGate t` is true exactly when `t` is a gate node. -/
def isGate : CFTree Event → Prop
  | basic _ => False
  | gate _ _ => True

/-- Return the immediate children of a coherent fault tree. -/
def children : CFTree Event → List (CFTree Event)
  | basic _ => []
  | gate _ ts => ts

/-- Return the gate label of a coherent fault tree, if one exists. -/
def gateOf : CFTree Event → Option CGate
  | basic _ => none
  | gate g _ => some g

/--
`WellFormed t` states that a coherent fault tree satisfies
the arity rules of its gates.

Basic events are well formed, while AND and OR gates must have at least
one child, and all children must themselves be well formed.
-/
def WellFormed : CFTree Event → Prop
  | basic _ => True
  | gate CGate.andGate ts =>
      ts ≠ [] ∧ ∀ t ∈ ts, WellFormed t
  | gate CGate.orGate ts =>
      ts ≠ [] ∧ ∀ t ∈ ts, WellFormed t

end CFTree
