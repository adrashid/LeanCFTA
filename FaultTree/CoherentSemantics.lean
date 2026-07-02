import FaultTree.CoherentQualitative

namespace CFTree

variable {Event : Type}

/-
===========================================================
1. Executable Semantics
===========================================================
-/

/-- A cut set is a finite set of basic events. -/
abbrev CutSet (Event : Type) := Finset Event

mutual

/-- Evaluate a coherent fault tree under an active cut set `C`. -/
def eval [DecidableEq Event] (C : CutSet Event) : CFTree Event → Bool
  | basic e => decide (e ∈ C)
  | gate CGate.andGate ts => evalAll C ts
  | gate CGate.orGate ts => evalAny C ts

/-- Evaluate whether all trees in a list are true. -/
def evalAll [DecidableEq Event] (C : CutSet Event) :
    List (CFTree Event) → Bool
  | [] => true
  | t :: ts => eval C t && evalAll C ts

/-- Evaluate whether at least one tree in a list is true. -/
def evalAny [DecidableEq Event] (C : CutSet Event) :
    List (CFTree Event) → Bool
  | [] => false
  | t :: ts => eval C t || evalAny C ts

end

/-
===========================================================
2. IsCutSet
===========================================================
-/

/--
A cut set is sufficient for a coherent fault tree if activating its events
makes the top event evaluate to true.
-/
def IsCutSet [DecidableEq Event] (C : CutSet Event) (t : CFTree Event) : Prop :=
  eval C t = true

/-
===========================================================
3. Simplification Lemmas
===========================================================
-/

/-- A basic event evaluates to true exactly when it belongs to the active event set. -/
@[simp]
theorem eval_basic [DecidableEq Event]
    (C : CutSet Event) (e : Event) :
    eval C (basic e) = decide (e ∈ C) := by
  simp [eval]

/-- An AND gate evaluates using `evalAll` on its child list. -/
@[simp]
theorem eval_andGate [DecidableEq Event]
    (C : CutSet Event) (ts : List (CFTree Event)) :
    eval C (gate CGate.andGate ts) = evalAll C ts := by
  simp [eval]

/-- An OR gate evaluates using `evalAny` on its child list. -/
@[simp]
theorem eval_orGate [DecidableEq Event]
    (C : CutSet Event) (ts : List (CFTree Event)) :
    eval C (gate CGate.orGate ts) = evalAny C ts := by
  simp [eval]

/-- An AND smart constructor evaluates using `evalAll`. -/
@[simp]
theorem eval_AND [DecidableEq Event]
    (C : CutSet Event) (ts : List (CFTree Event)) :
    eval C (AND ts) = evalAll C ts := by
  simp [AND]

/-- An OR smart constructor evaluates using `evalAny`. -/
@[simp]
theorem eval_OR [DecidableEq Event]
    (C : CutSet Event) (ts : List (CFTree Event)) :
    eval C (OR ts) = evalAny C ts := by
  simp [OR]

/-
===========================================================
4. Semantic Lemmas
===========================================================
-/

/-- A singleton cut set satisfies its own basic-event tree. -/
theorem singleton_is_cutset_basic [DecidableEq Event] (e : Event) :
    IsCutSet ({e} : CutSet Event) (basic e) := by
  simp [IsCutSet, eval]

/-- For a basic event, a cut set is sufficient exactly when the event belongs to it. -/
theorem isCutSet_basic_iff [DecidableEq Event]
    (C : CutSet Event) (e : Event) :
    IsCutSet C (basic e) ↔ e ∈ C := by
  simp [IsCutSet, eval]

/--
If the head child and all remaining children of an AND gate are satisfied by `C`,
then the whole AND gate is satisfied.
-/
theorem isCutSet_and_cons [DecidableEq Event]
    (C : CutSet Event) (t : CFTree Event) (ts : List (CFTree Event))
    (h₁ : IsCutSet C t)
    (h₂ : evalAll C ts = true) :
    IsCutSet C (AND (t :: ts)) := by
  unfold IsCutSet at h₁
  unfold IsCutSet AND
  simp [eval, evalAll, h₁, h₂]

/-- If the first child of an OR gate is satisfied by `C`, then the OR gate is satisfied. -/
theorem isCutSet_or_head [DecidableEq Event]
    (C : CutSet Event) (t : CFTree Event) (ts : List (CFTree Event))
    (h : IsCutSet C t) :
    IsCutSet C (OR (t :: ts)) := by
  unfold IsCutSet at h
  unfold IsCutSet OR
  simp [eval, evalAny, h]

end CFTree
