import FaultTree.CoherentSyntax

/-
  Qualitative analysis of coherent fault trees.

  This file defines structural analysis functions and occurrence predicates
  for coherent fault trees.
-/

namespace CFTree

variable {Event : Type}

/-
===========================================================
1. Definitions
===========================================================
-/

/--
Return all basic events appearing in a coherent fault tree.

The result is a list, so repeated events may appear multiple times.
-/
def basicEvents : CFTree Event → List Event
  | basic e => [e]
  | gate _ ts => ts.flatMap basicEvents

/--
`size t` is the total number of nodes in the coherent fault tree.

Both basic events and gates are counted as nodes.
-/
def size : CFTree Event → Nat
  | basic _ => 1
  | gate _ ts => 1 + (ts.map size).sum

/-- Count the number of basic event leaves. -/
def basicEventCount : CFTree Event → Nat
  | basic _ => 1
  | gate _ ts => (ts.map basicEventCount).sum

/-- Count the number of gate nodes. -/
def gateCount : CFTree Event → Nat
  | basic _ => 0
  | gate _ ts => 1 + (ts.map gateCount).sum

/--
Height of a coherent fault tree.

A basic event has height `1`. A gate has height `1 +` the maximum
height of its children. For an empty gate list, the maximum height is
taken as `0`, making the definition total for all syntactic trees.
-/
def height : CFTree Event → Nat
  | basic _ => 1
  | gate _ ts => 1 + (ts.map height).foldl Nat.max 0

/-- Count the number of leaves. Leaves are exactly basic event nodes. -/
def leafCount : CFTree Event → Nat
  | basic _ => 1
  | gate _ ts => (ts.map leafCount).sum

/--
Return the number of immediate children of a coherent fault tree.

A basic event has no children.
-/
def degree : CFTree Event → Nat
  | basic _ => 0
  | gate _ ts => ts.length

/-- `isLeaf t` is true exactly when `t` is a basic event node. -/
def isLeaf : CFTree Event → Prop
  | basic _ => True
  | gate _ _ => False

/-- `isInternal t` is true exactly when `t` is a gate node. -/
abbrev isInternal : CFTree Event → Prop :=
  isGate

/-- Check whether a tree node is an AND gate. -/
def isAND : CFTree Event → Prop
  | gate CGate.andGate _ => True
  | _ => False

/-- Check whether a tree node is an OR gate. -/
def isOR : CFTree Event → Prop
  | gate CGate.orGate _ => True
  | _ => False

/-- Return all immediate subtrees of a coherent fault tree. -/
abbrev subtrees : CFTree Event → List (CFTree Event) :=
  children

/-- Return the root gate of a coherent fault tree, if one exists. -/
abbrev rootGate : CFTree Event → Option CGate :=
  gateOf

/-
===========================================================
2. Basic Simp Lemmas
===========================================================
-/

@[simp]
theorem size_basic (e : Event) :
    size (basic e) = 1 := by
  simp [size]

@[simp]
theorem size_gate (g : CGate) (ts : List (CFTree Event)) :
    size (gate g ts) = 1 + (ts.map size).sum := by
  simp [size]

@[simp]
theorem basicEventCount_basic (e : Event) :
    basicEventCount (basic e) = 1 := by
  simp [basicEventCount]

@[simp]
theorem basicEventCount_gate (g : CGate) (ts : List (CFTree Event)) :
    basicEventCount (gate g ts) = (ts.map basicEventCount).sum := by
  simp [basicEventCount]

@[simp]
theorem gateCount_basic (e : Event) :
    gateCount (basic e) = 0 := by
  simp [gateCount]

@[simp]
theorem gateCount_gate (g : CGate) (ts : List (CFTree Event)) :
    gateCount (gate g ts) = 1 + (ts.map gateCount).sum := by
  simp [gateCount]

@[simp]
theorem isLeaf_basic (e : Event) :
    isLeaf (basic e) := by
  simp [isLeaf]

@[simp]
theorem isLeaf_gate (g : CGate) (ts : List (CFTree Event)) :
    ¬ isLeaf (gate g ts) := by
  simp [isLeaf]

@[simp]
theorem isInternal_basic (e : Event) :
    ¬ isInternal (basic e) := by
  simp [isInternal, isGate]

@[simp]
theorem isInternal_gate (g : CGate) (ts : List (CFTree Event)) :
    isInternal (gate g ts) := by
  simp [isInternal, isGate]

@[simp]
theorem degree_basic (e : Event) :
    degree (basic e) = 0 := by
  simp [degree]

@[simp]
theorem degree_gate (g : CGate) (ts : List (CFTree Event)) :
    degree (gate g ts) = ts.length := by
  simp [degree]

@[simp]
theorem rootGate_basic (e : Event) :
    rootGate (basic e) = none := by
  simp [rootGate, gateOf]

@[simp]
theorem rootGate_gate (g : CGate) (ts : List (CFTree Event)) :
    rootGate (gate g ts) = some g := by
  simp [rootGate, gateOf]

@[simp]
theorem basicEvents_basic (e : Event) :
    basicEvents (basic e) = [e] := by
  simp [basicEvents]

@[simp]
theorem basicEvents_gate (g : CGate) (ts : List (CFTree Event)) :
    basicEvents (gate g ts) = ts.flatMap basicEvents := by
  simp [basicEvents]

@[simp]
theorem height_basic (e : Event) :
    height (basic e) = 1 := by
  simp [height]

@[simp]
theorem height_gate (g : CGate) (ts : List (CFTree Event)) :
    height (gate g ts) =
      1 + (ts.map height).foldl Nat.max 0 := by
  simp [height]

@[simp]
theorem leafCount_basic (e : Event) :
    leafCount (basic e) = 1 := by
  simp [leafCount]

@[simp]
theorem leafCount_gate (g : CGate) (ts : List (CFTree Event)) :
    leafCount (gate g ts) = (ts.map leafCount).sum := by
  simp [leafCount]

@[simp]
theorem subtrees_basic (e : Event) :
    subtrees (basic e) = [] := by
  simp [subtrees, children]

@[simp]
theorem subtrees_gate (g : CGate) (ts : List (CFTree Event)) :
    subtrees (gate g ts) = ts := by
  simp [subtrees, children]

/-
===========================================================
3. Structural Lemmas
===========================================================
-/

/-- Every coherent fault tree has positive size. -/
theorem size_pos (t : CFTree Event) :
    0 < size t := by
  cases t <;> simp

/-- Every coherent fault tree has positive height. -/
theorem height_pos (t : CFTree Event) :
    0 < height t := by
  cases t <;> simp

/-- For any gate, the total size is at least one. -/
theorem size_gate_pos (g : CGate) (ts : List (CFTree Event)) :
    0 < size (gate g ts) := by
  simp

/-- For any basic event, the number of basic events is at most the size. -/
theorem basicEventCount_basic_le_size (e : Event) :
    basicEventCount (basic e) ≤ size (basic e) := by
  simp

/-- For any basic event, the gate count is at most the size. -/
theorem gateCount_basic_le_size (e : Event) :
    gateCount (basic e) ≤ size (basic e) := by
  simp

/-
===========================================================
4. Occurrence
===========================================================
-/

/--
`Occurs e t` means that the basic event `e` occurs somewhere in the
coherent fault tree `t`.
-/
inductive Occurs (e : Event) : CFTree Event → Prop where
  | basic :
      Occurs e (basic e)
  | child {g : CGate} {ts : List (CFTree Event)} {t : CFTree Event} :
      Occurs e t →
      t ∈ ts →
      Occurs e (gate g ts)

/-- Every basic event occurs in its own basic-event node. -/
theorem occurs_basic_self (e : Event) :
    Occurs e (basic e) := by
  exact Occurs.basic

/-- Occurrence in a basic node is equivalent to equality with its label. -/
@[simp]
theorem occurs_basic_iff (e x : Event) :
    Occurs e (basic x) ↔ e = x := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact Occurs.basic

/-- If an event occurs in a child subtree, then it occurs in the parent gate. -/
theorem occurs_gate_of_child
    (e : Event) (g : CGate) (ts : List (CFTree Event)) (t : CFTree Event)
    (hOccurs : Occurs e t)
    (hMem : t ∈ ts) :
    Occurs e (gate g ts) := by
  exact Occurs.child hOccurs hMem

/-- Occurrence in a gate is equivalent to occurrence in one of its children. -/
theorem occurs_gate_iff
    (e : Event) (g : CGate) (ts : List (CFTree Event)) :
    Occurs e (gate g ts) ↔
      ∃ t ∈ ts, Occurs e t := by
  constructor
  · intro h
    cases h with
    | child hOcc hMem =>
        exact ⟨_, hMem, hOcc⟩
  · intro h
    rcases h with ⟨t, hMem, hOcc⟩
    exact Occurs.child hOcc hMem

/-- If an event occurs in the left child of a binary AND gate, it occurs in the gate. -/
theorem occurs_and_left
    (e : Event) (t₁ t₂ : CFTree Event)
    (h : Occurs e t₁) :
    Occurs e (AND [t₁, t₂]) := by
  unfold AND
  exact Occurs.child h (by simp)

/-- If an event occurs in the right child of a binary AND gate, it occurs in the gate. -/
theorem occurs_and_right
    (e : Event) (t₁ t₂ : CFTree Event)
    (h : Occurs e t₂) :
    Occurs e (AND [t₁, t₂]) := by
  unfold AND
  exact Occurs.child h (by simp)

end CFTree
