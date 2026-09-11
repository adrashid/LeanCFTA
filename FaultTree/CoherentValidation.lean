import FaultTree.CoherentCutSets

namespace CFTree.Validation

abbrev TestEvent := String

private def A : CFTree TestEvent := BE "A"
private def B : CFTree TestEvent := BE "B"
private def C : CFTree TestEvent := BE "C"
private def D : CFTree TestEvent := BE "D"

/-
===========================================================
1. Nested Gates
===========================================================
-/

/--
A nested combination of AND and OR gates:

    (A ∧ B) ∨ (C ∨ D)
-/
def nestedTree : CFTree TestEvent :=
  OR [
    AND [A, B],
    OR [C, D]
  ]

theorem nestedTree_cutSets :
    cutSets nestedTree =
      {
        ({"A", "B"} : CutSet TestEvent),
        ({"C"} : CutSet TestEvent),
        ({"D"} : CutSet TestEvent)
      } := by
  native_decide

theorem nestedTree_minimalCutSets :
    minimalCutSets nestedTree =
      {
        ({"A", "B"} : CutSet TestEvent),
        ({"C"} : CutSet TestEvent),
        ({"D"} : CutSet TestEvent)
      } := by
  native_decide

/-
===========================================================
2. Repeated Events
===========================================================
-/

/--
The repeated-event expression A ∧ A must produce only {A}.
-/
def repeatedEventTree : CFTree TestEvent :=
  AND [A, A]

theorem repeatedEventTree_cutSets :
    cutSets repeatedEventTree =
      {
        ({"A"} : CutSet TestEvent)
      } := by
  native_decide

theorem repeatedEventTree_minimalCutSets :
    minimalCutSets repeatedEventTree =
      {
        ({"A"} : CutSet TestEvent)
      } := by
  native_decide

/-
===========================================================
3. Duplicate Child Subtrees
===========================================================
-/

def duplicateSubtree : CFTree TestEvent :=
  AND [A, B]

/--
Duplicating the subtree A ∧ B under an OR gate must not
duplicate the resulting cut set.
-/
def duplicateChildTree : CFTree TestEvent :=
  OR [duplicateSubtree, duplicateSubtree]

theorem duplicateChildTree_cutSets :
    cutSets duplicateChildTree =
      {
        ({"A", "B"} : CutSet TestEvent)
      } := by
  native_decide

theorem duplicateChildTree_minimalCutSets :
    minimalCutSets duplicateChildTree =
      {
        ({"A", "B"} : CutSet TestEvent)
      } := by
  native_decide

/-
===========================================================
4. Absorption
===========================================================
-/

/--
The expression A ∨ (A ∧ B) exercises Boolean absorption.
The raw generator produces {A} and {A,B}.
-/
def absorptionTree : CFTree TestEvent :=
  OR [
    A,
    AND [A, B]
  ]

theorem absorptionTree_cutSets :
    cutSets absorptionTree =
      {
        ({"A"} : CutSet TestEvent),
        ({"A", "B"} : CutSet TestEvent)
      } := by
  native_decide

/--
Minimization removes the absorbed superset {A,B}.
-/
theorem absorptionTree_minimalCutSets :
    minimalCutSets absorptionTree =
      {
        ({"A"} : CutSet TestEvent)
      } := by
  native_decide

/--
The absorbed superset remains a semantic cut set.
-/
theorem absorption_superset_is_cutSet :
    IsCutSet
      ({"A", "B"} : CutSet TestEvent)
      absorptionTree := by
  unfold IsCutSet
  native_decide

/--
The absorbed superset is not returned as a minimal cut set.
-/
theorem absorption_superset_not_minimal :
    ({"A", "B"} : CutSet TestEvent) ∉
      minimalCutSets absorptionTree := by
  native_decide

/--
The returned singleton satisfies the global semantic
definition of a minimal cut set.
-/
theorem absorption_singleton_globally_minimal :
    MinimalCutSet
      ({"A"} : CutSet TestEvent)
      absorptionTree := by
  apply minimalCutSets_globally_minimal
  native_decide

end CFTree.Validation
