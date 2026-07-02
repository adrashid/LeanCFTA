import FaultTree.CoherentSemantics

/-
  Cut-set infrastructure for coherent fault trees.

  This file develops cut-set occurrence, monotonicity, cut-set generation,
  soundness, and minimal cut-set generation for coherent fault trees.
-/

namespace CFTree

variable {Event : Type}

/-
===========================================================
1. Cut-set Objects
===========================================================
-/

/--
A cut set `C` occurs in a coherent fault tree `t` if every event in `C`
appears somewhere in `t`.
-/
def CutSetOccurs [DecidableEq Event]
    (C : CutSet Event) (t : CFTree Event) : Prop :=
  ∀ e ∈ C, Occurs e t

/-- The empty cut set occurs in every coherent fault tree. -/
theorem empty_cutset_occurs [DecidableEq Event]
    (t : CFTree Event) :
    CutSetOccurs (∅ : CutSet Event) t := by
  intro e h
  simp at h

/-- A singleton cut set `{e}` occurs in `t` if `e` occurs in `t`. -/
theorem singleton_cutset_occurs [DecidableEq Event]
    (e : Event) (t : CFTree Event)
    (h : Occurs e t) :
    CutSetOccurs ({e} : CutSet Event) t := by
  intro x hx
  simp at hx
  subst hx
  exact h

/-- If a cut set occurs in a child subtree, then it occurs in the parent gate. -/
theorem cutset_occurs_gate_of_child [DecidableEq Event]
    (C : CutSet Event) (g : CGate) (ts : List (CFTree Event))
    (t : CFTree Event)
    (hC : CutSetOccurs C t)
    (hMem : t ∈ ts) :
    CutSetOccurs C (gate g ts) := by
  intro e he
  exact Occurs.child (hC e he) hMem

/-
===========================================================
2. Monotonicity
===========================================================
-/

/--
A coherent fault tree is monotone if activating additional basic events
cannot change the top event from true to false.
-/
def Monotone [DecidableEq Event] (t : CFTree Event) : Prop :=
  ∀ C D : CutSet Event, C ⊆ D → IsCutSet C t → IsCutSet D t

/-- Every basic-event tree is monotone. -/
theorem monotone_basic [DecidableEq Event] (e : Event) :
    Monotone (basic e) := by
  intro C D hSub hCut
  unfold IsCutSet at hCut ⊢
  simp [eval] at hCut ⊢
  exact hSub hCut

/--
If every child evaluates to true under `C`, then every child also evaluates
to true under any superset `D`, provided all children are monotone.
-/
theorem evalAll_monotone
    [DecidableEq Event]
    (C D : CutSet Event)
    (hSub : C ⊆ D)
    (ts : List (CFTree Event))
    (hMono : ∀ t ∈ ts, Monotone t)
    (hEval : evalAll C ts = true) :
    evalAll D ts = true := by
  induction ts with
  | nil =>
      simp [evalAll]
  | cons t ts ih =>
      simp [evalAll] at hEval ⊢
      rcases hEval with ⟨ht, hts⟩

      have hMono_t : Monotone t := by
        exact hMono t (by simp)

      have hMono_ts :
          ∀ s ∈ ts, Monotone s := by
        intro s hs
        exact hMono s (by simp [hs])

      have ht' : eval D t = true := by
        exact hMono_t C D hSub ht

      have hts' : evalAll D ts = true := by
        exact ih hMono_ts hts

      simp [ht', hts']

/--
If some child evaluates to true under `C`, then some child also evaluates
to true under any superset `D`, provided all children are monotone.
-/
theorem evalAny_monotone
    [DecidableEq Event]
    (C D : CutSet Event)
    (hSub : C ⊆ D)
    (ts : List (CFTree Event))
    (hMono : ∀ t ∈ ts, Monotone t)
    (hEval : evalAny C ts = true) :
    evalAny D ts = true := by
  induction ts with
  | nil =>
      simp [evalAny] at hEval
  | cons t ts ih =>
      simp [evalAny] at hEval ⊢
      cases h : eval C t with
      | false =>
          have hMonoTs :
              ∀ s ∈ ts, Monotone s := by
            intro s hs
            exact hMono s (by simp [hs])

          have hTail : evalAny C ts = true := by
            simpa [h] using hEval

          right
          exact ih hMonoTs hTail

      | true =>
          have hMonoT : Monotone t := by
            exact hMono t (by simp)

          have hDt : eval D t = true := by
            exact hMonoT C D hSub h

          simp [hDt]

/-- If every child of an AND gate is monotone, then the AND gate is monotone. -/
theorem monotone_AND [DecidableEq Event]
    (ts : List (CFTree Event))
    (hMono : ∀ t ∈ ts, Monotone t) :
    Monotone (AND ts) := by
  intro C D hSub hCut
  unfold IsCutSet AND at hCut ⊢
  simp [eval] at hCut ⊢
  exact evalAll_monotone C D hSub ts hMono hCut

/-- If every child of an OR gate is monotone, then the OR gate is monotone. -/
theorem monotone_OR [DecidableEq Event]
    (ts : List (CFTree Event))
    (hMono : ∀ t ∈ ts, Monotone t) :
    Monotone (OR ts) := by
  intro C D hSub hCut
  unfold IsCutSet OR at hCut ⊢
  simp [eval] at hCut ⊢
  exact evalAny_monotone C D hSub ts hMono hCut

/-- Every child of a gate has strictly smaller size than the gate itself. -/
theorem size_lt_gate_of_mem
    (g : CGate) (ts : List (CFTree Event)) {t : CFTree Event}
    (hMem : t ∈ ts) :
    size t < size (gate g ts) := by
  simp
  have hIn : size t ∈ ts.map size := by
    exact List.mem_map.mpr ⟨t, hMem, rfl⟩
  have hLe : size t ≤ (ts.map size).sum := by
    exact List.le_sum_of_mem hIn
  omega

/-- Every coherent fault tree is monotone. -/
theorem coherent_monotone
    [DecidableEq Event] :
    ∀ t : CFTree Event, Monotone t
  | basic e => by
      exact monotone_basic e
  | gate CGate.andGate ts => by
      apply monotone_AND
      intro t ht
      exact coherent_monotone t
  | gate CGate.orGate ts => by
      apply monotone_OR
      intro t ht
      exact coherent_monotone t
termination_by t => size t
decreasing_by
  all_goals
    exact size_lt_gate_of_mem _ _ ‹_ ∈ _›

/-
===========================================================
3. Cut-set Generation
===========================================================
-/

/-- Combine one cut set with a collection of cut sets by taking unions. -/
def combineWith [DecidableEq Event]
    (C : CutSet Event) (Cs : Finset (CutSet Event)) :
    Finset (CutSet Event) :=
  Cs.image (fun D => C ∪ D)

/-- Take all pairwise unions of cut sets from two collections. -/
def combineCutSets [DecidableEq Event]
    (Cs Ds : Finset (CutSet Event)) :
    Finset (CutSet Event) :=
  Cs.biUnion (fun C => combineWith C Ds)

/--
Combine cut-set collections for an AND-list.

For an empty list, the neutral element is `{∅}`.
-/
def andCombine [DecidableEq Event] :
    List (Finset (CutSet Event)) → Finset (CutSet Event)
  | [] => {∅}
  | Cs :: rest => combineCutSets Cs (andCombine rest)

/--
Combine cut-set collections for an OR-list.

For an empty list, the neutral element is `∅`.
-/
def orCombine [DecidableEq Event] :
    List (Finset (CutSet Event)) → Finset (CutSet Event)
  | [] => ∅
  | Cs :: rest => Cs ∪ orCombine rest

/-- Generate candidate cut sets for a coherent fault tree. -/
def cutSets [DecidableEq Event] : CFTree Event → Finset (CutSet Event)
  | basic e => {{e}}
  | gate CGate.andGate ts => andCombine (ts.map cutSets)
  | gate CGate.orGate ts => orCombine (ts.map cutSets)

/-- Generate cut sets for an AND-list of child trees. -/
def andCutSetsList [DecidableEq Event]
    (ts : List (CFTree Event)) :
    Finset (CutSet Event) :=
  andCombine (ts.map cutSets)

/-- Generate cut sets for an OR-list of child trees. -/
def orCutSetsList [DecidableEq Event]
    (ts : List (CFTree Event)) :
    Finset (CutSet Event) :=
  orCombine (ts.map cutSets)

/-- A basic event generates the singleton cut set containing that event. -/
@[simp]
theorem cutSets_basic [DecidableEq Event] (e : Event) :
    cutSets (basic e) = {{e}} := by
  simp [cutSets]

/-- An AND gate generates combined cut sets of its children. -/
@[simp]
theorem cutSets_andGate [DecidableEq Event]
    (ts : List (CFTree Event)) :
    cutSets (gate CGate.andGate ts) = andCutSetsList ts := by
  simp [cutSets, andCutSetsList]

/-- An OR gate generates the union of the cut sets of its children. -/
@[simp]
theorem cutSets_orGate [DecidableEq Event]
    (ts : List (CFTree Event)) :
    cutSets (gate CGate.orGate ts) = orCutSetsList ts := by
  simp [cutSets, orCutSetsList]

/-
===========================================================
4. Membership Lemmas
===========================================================
-/

/-- Membership characterization for `combineWith`. -/
theorem mem_combineWith_iff [DecidableEq Event]
    (X C : CutSet Event) (Ds : Finset (CutSet Event)) :
    X ∈ combineWith C Ds ↔
      ∃ D ∈ Ds, X = C ∪ D := by
  unfold combineWith
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨D, hD, rfl⟩
    exact ⟨D, hD, rfl⟩
  · intro h
    rcases h with ⟨D, hD, rfl⟩
    exact Finset.mem_image.mpr ⟨D, hD, rfl⟩

/-- Membership characterization for `combineCutSets`. -/
theorem mem_combineCutSets_iff [DecidableEq Event]
    (X : CutSet Event)
    (Cs Ds : Finset (CutSet Event)) :
    X ∈ combineCutSets Cs Ds ↔
      ∃ C ∈ Cs, ∃ D ∈ Ds, X = C ∪ D := by
  unfold combineCutSets
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨C, hC, hX⟩
    rw [mem_combineWith_iff] at hX
    rcases hX with ⟨D, hD, hEq⟩
    exact ⟨C, hC, D, hD, hEq⟩
  · intro h
    rcases h with ⟨C, hC, D, hD, hEq⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨C, hC, ?_⟩
    rw [mem_combineWith_iff]
    exact ⟨D, hD, hEq⟩

/-- The only cut set generated by an empty AND-list is the empty cut set. -/
@[simp]
theorem mem_andCutSetsList_nil [DecidableEq Event]
    (X : CutSet Event) :
    X ∈ andCutSetsList ([] : List (CFTree Event)) ↔
      X = ∅ := by
  simp [andCutSetsList, andCombine]

/-- Membership characterization for a nonempty AND-list generator. -/
theorem mem_andCutSetsList_cons [DecidableEq Event]
    (X : CutSet Event) (t : CFTree Event) (ts : List (CFTree Event)) :
    X ∈ andCutSetsList (t :: ts) ↔
      ∃ C ∈ cutSets t,
      ∃ D ∈ andCutSetsList ts,
        X = C ∪ D := by
  simp [andCutSetsList, andCombine, mem_combineCutSets_iff]

/-- Membership characterization for the OR-list generator. -/
theorem mem_orCutSetsList [DecidableEq Event]
    (X : CutSet Event) (ts : List (CFTree Event)) :
    X ∈ orCutSetsList ts ↔
      ∃ t ∈ ts, X ∈ cutSets t := by
  induction ts with
  | nil =>
      simp [orCutSetsList, orCombine]

  | cons t ts ih =>
      change X ∈ (cutSets t ∪ orCutSetsList ts) ↔
        ∃ t_1 ∈ t :: ts, X ∈ cutSets t_1
      constructor
      · intro h
        rcases Finset.mem_union.mp h with hHead | hTail
        · exact ⟨t, by simp, hHead⟩
        · rcases ih.mp hTail with ⟨s, hsMem, hsCut⟩
          exact ⟨s, by simp [hsMem], hsCut⟩
      · intro h
        rcases h with ⟨s, hsMem, hsCut⟩
        simp at hsMem
        rcases hsMem with hsEq | hsTail
        · subst hsEq
          exact Finset.mem_union.mpr (Or.inl hsCut)
        · exact Finset.mem_union.mpr
            (Or.inr (ih.mpr ⟨s, hsTail, hsCut⟩))

/-
===========================================================
5. Soundness
===========================================================
-/

/--
`Sound t` means that every cut set generated by `cutSets t`
is a semantically valid cut set for `t`.
-/
def Sound [DecidableEq Event] (t : CFTree Event) : Prop :=
  ∀ C, C ∈ cutSets t → IsCutSet C t

/-- The cut-set generator is sound for basic-event trees. -/
theorem sound_basic [DecidableEq Event] (e : Event) :
    Sound (basic e) := by
  intro C hC
  simp [IsCutSet, eval] at hC ⊢
  subst hC
  simp

/--
Monotonicity preserves semantic cut sets under supersets.
-/
theorem isCutSet_of_subset_of_monotone [DecidableEq Event]
    (t : CFTree Event)
    (C D : CutSet Event)
    (hMono : Monotone t)
    (hSub : C ⊆ D)
    (hCut : IsCutSet C t) :
    IsCutSet D t := by
  exact hMono C D hSub hCut

/--
Extending a generated cut set with additional events
preserves satisfaction.
-/
theorem cutset_union_left_sound [DecidableEq Event]
    (t : CFTree Event)
    (C D : CutSet Event)
    (hSound : Sound t)
    (hC : C ∈ cutSets t) :
    IsCutSet (C ∪ D) t := by
  have hCut : IsCutSet C t := hSound C hC
  exact coherent_monotone t C (C ∪ D)
    (by intro x hx; simp [hx])
    hCut

/--
Extending a generated cut set on the right preserves satisfaction.
-/
theorem cutset_union_right_sound [DecidableEq Event]
    (t : CFTree Event)
    (C D : CutSet Event)
    (hSound : Sound t)
    (hD : D ∈ cutSets t) :
    IsCutSet (C ∪ D) t := by
  have hCut : IsCutSet D t := hSound D hD
  exact coherent_monotone t D (C ∪ D)
    (by intro x hx; simp [hx])
    hCut

/--
If the head child and the remaining children of an AND gate
are satisfied, then their union satisfies the whole gate.
-/
theorem and_union_sound [DecidableEq Event]
    (t : CFTree Event)
    (ts : List (CFTree Event))
    (C D : CutSet Event)
    (hHead : IsCutSet C t)
    (hTail : IsCutSet D (AND ts)) :
    IsCutSet (C ∪ D) (AND (t :: ts)) := by
  unfold IsCutSet at hHead hTail ⊢

  have hHead' :
      eval (C ∪ D) t = true := by
    exact coherent_monotone t C (C ∪ D)
      (by intro x hx; simp [hx])
      hHead

  have hTail' :
      eval (C ∪ D) (AND ts) = true := by
    exact coherent_monotone (AND ts) D (C ∪ D)
      (by intro x hx; simp [hx])
      hTail

  have hEvalAll :
      evalAll (C ∪ D) ts = true := by
    simpa [eval_AND] using hTail'

  simp [eval_AND, evalAll, hHead', hEvalAll]

/--
If one child of an OR gate is satisfied,
then the entire OR gate is satisfied.
-/
theorem isCutSet_or_of_mem [DecidableEq Event]
    (C : CutSet Event)
    (ts : List (CFTree Event))
    (t : CFTree Event)
    (hMem : t ∈ ts)
    (hCut : IsCutSet C t) :
    IsCutSet C (OR ts) := by
  unfold IsCutSet at hCut ⊢
  induction ts with
  | nil =>
      simp at hMem
  | cons x xs ih =>
      simp at hMem
      simp [eval_OR, evalAny]
      cases hMem with
      | inl hx =>
          subst hx
          left
          exact hCut
      | inr hx =>
          right
          exact ih hx

/-
===========================================================
6. Recursive Soundness Proof
===========================================================
-/

mutual

/--
Every cut set generated by `cutSets`
is a semantic cut set.
-/
theorem cutSets_sound [DecidableEq Event]
    (t : CFTree Event)
    (C : CutSet Event)
    (h : C ∈ cutSets t) :
    IsCutSet C t := by
  cases t with
  | basic e =>
      simp [IsCutSet, eval] at h ⊢
      subst h
      simp

  | gate g ts =>
      cases g with
      | andGate =>
          have h' :
              C ∈ andCutSetsList ts := by
            simpa [cutSets, andCutSetsList] using h
          exact andCutSetsList_sound ts C h'

      | orGate =>
          have h' :
              C ∈ orCutSetsList ts := by
            simpa [cutSets, orCutSetsList] using h
          exact orCutSetsList_sound ts C h'

/--
Every cut set generated for an AND-list
satisfies the corresponding AND gate.
-/
theorem andCutSetsList_sound [DecidableEq Event]
    (ts : List (CFTree Event))
    (C : CutSet Event)
    (h : C ∈ andCutSetsList ts) :
    IsCutSet C (AND ts) := by
  cases ts with
  | nil =>
      simp [andCutSetsList, andCombine] at h
      subst h
      unfold IsCutSet
      simp [eval_AND, evalAll]

  | cons t ts =>
      rw [mem_andCutSetsList_cons] at h
      rcases h with
        ⟨C₁, hC₁, C₂, hC₂, hEq⟩
      subst hEq

      have hHead :
          IsCutSet C₁ t := by
        exact cutSets_sound t C₁ hC₁

      have hTail :
          IsCutSet C₂ (AND ts) := by
        exact andCutSetsList_sound ts C₂ hC₂

      exact and_union_sound
        t ts C₁ C₂ hHead hTail

/--
Every cut set generated for an OR-list
satisfies the corresponding OR gate.
-/
theorem orCutSetsList_sound [DecidableEq Event]
    (ts : List (CFTree Event))
    (C : CutSet Event)
    (h : C ∈ orCutSetsList ts) :
    IsCutSet C (OR ts) := by
  rw [mem_orCutSetsList] at h
  rcases h with ⟨t, hMem, hCut⟩

  have hChild :
      IsCutSet C t := by
    exact cutSets_sound t C hCut

  exact isCutSet_or_of_mem
    C ts t hMem hChild

end

/-
===========================================================
7. Minimal Cut Sets
===========================================================
-/

/--
`MinimalCutSet C t` means that `C` is a semantic cut set for `t`
and no proper subset of `C` is also a semantic cut set for `t`.
-/
def MinimalCutSet [DecidableEq Event]
    (C : CutSet Event) (t : CFTree Event) : Prop :=
  IsCutSet C t ∧
  ∀ D : CutSet Event, D ⊂ C → ¬ IsCutSet D t

/-- Every minimal cut set is a semantic cut set. -/
theorem MinimalCutSet.isCutSet [DecidableEq Event]
    {C : CutSet Event} {t : CFTree Event}
    (h : MinimalCutSet C t) :
    IsCutSet C t := by
  exact h.1

/-- No proper subset of a minimal cut set is itself a semantic cut set. -/
theorem MinimalCutSet.no_smaller [DecidableEq Event]
    {C D : CutSet Event} {t : CFTree Event}
    (h : MinimalCutSet C t)
    (hSub : D ⊂ C) :
    ¬ IsCutSet D t := by
  exact h.2 D hSub

/-- For a basic-event tree, the singleton set containing that event is minimal. -/
theorem singleton_minimal_basic [DecidableEq Event]
    (e : Event) :
    MinimalCutSet ({e} : CutSet Event) (basic e) := by
  constructor
  · exact singleton_is_cutset_basic e
  · intro D hSub hCut
    rw [isCutSet_basic_iff] at hCut
    have hSingleton : D = ({e} : CutSet Event) := by
      apply Finset.Subset.antisymm
      · exact hSub.1
      · intro x hx
        simp at hx
        subst hx
        exact hCut
    have hReverse : ({e} : CutSet Event) ⊆ D := by
      rw [hSingleton]
    exact hSub.2 hReverse

/-- For a basic-event tree, the only minimal cut set is its singleton event. -/
theorem minimal_basic_iff [DecidableEq Event]
    (C : CutSet Event) (e : Event) :
    MinimalCutSet C (basic e) ↔
      C = ({e} : CutSet Event) := by
  constructor
  · intro hMin
    have hCut : IsCutSet C (basic e) :=
      MinimalCutSet.isCutSet hMin

    rw [isCutSet_basic_iff] at hCut

    apply Finset.Subset.antisymm
    · intro x hx
      by_contra hxne

      have hProper : ({e} : CutSet Event) ⊂ C := by
        constructor
        · intro y hy
          simp at hy
          subst hy
          exact hCut
        · intro hSubset
          have this : x = e := by
            simpa using hSubset hx
          exact hxne (by simp [this])

      have hSmallCut :
          IsCutSet ({e} : CutSet Event) (basic e) :=
        singleton_is_cutset_basic e

      exact (MinimalCutSet.no_smaller hMin hProper) hSmallCut

    · intro x hx
      simp at hx
      subst hx
      exact hCut

  · intro hEq
    subst hEq
    exact singleton_minimal_basic e

/-- Every minimal cut set is, in particular, a semantic cut set. -/
theorem minimal_implies_cutset [DecidableEq Event]
    {C : CutSet Event} {t : CFTree Event}
    (h : MinimalCutSet C t) :
    IsCutSet C t := by
  exact MinimalCutSet.isCutSet h

/-- No proper subset of a minimal cut set is itself a semantic cut set. -/
theorem minimal_no_subset [DecidableEq Event]
    {C D : CutSet Event} {t : CFTree Event}
    (h : MinimalCutSet C t)
    (hSub : D ⊂ C) :
    ¬ IsCutSet D t := by
  exact MinimalCutSet.no_smaller h hSub

/-
===========================================================
8. Minimal Cut-set Generation
===========================================================
-/

/-- Remove every cut set that has a strictly smaller cut set in the same collection. -/
def minimizeCutSets [DecidableEq Event]
    (Cs : Finset (CutSet Event)) :
    Finset (CutSet Event) :=
  Cs.filter (fun C => ∀ D ∈ Cs, ¬ D ⊂ C)

/-- Membership characterization for `minimizeCutSets`. -/
theorem mem_minimizeCutSets_iff [DecidableEq Event]
    (C : CutSet Event) (Cs : Finset (CutSet Event)) :
    C ∈ minimizeCutSets Cs ↔
      C ∈ Cs ∧ ∀ D ∈ Cs, ¬ D ⊂ C := by
  simp [minimizeCutSets]

/-- Generate minimal cut sets by filtering the generated cut-set collection. -/
def minimalCutSets [DecidableEq Event]
    (t : CFTree Event) :
    Finset (CutSet Event) :=
  minimizeCutSets (cutSets t)

/-- Every generated minimal cut set is semantically valid. -/
theorem minimalCutSets_sound [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event)
    (h : C ∈ minimalCutSets t) :
    IsCutSet C t := by
  unfold minimalCutSets at h
  rw [mem_minimizeCutSets_iff] at h
  exact cutSets_sound t C h.1

/-- Every generated minimal cut set has no smaller generated cut set below it. -/
theorem minimalCutSets_generated_minimal [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event)
    (h : C ∈ minimalCutSets t) :
    ∀ D, D ∈ cutSets t → ¬ D ⊂ C := by
  unfold minimalCutSets at h
  rw [mem_minimizeCutSets_iff] at h
  exact h.2

/-- Every generated minimal cut set was originally generated by `cutSets`. -/
theorem minimalCutSets_subset_cutSets [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event)
    (h : C ∈ minimalCutSets t) :
    C ∈ cutSets t := by
  unfold minimalCutSets at h
  rw [mem_minimizeCutSets_iff] at h
  exact h.1

/-- Membership characterization for `minimalCutSets`. -/
theorem mem_minimalCutSets_iff [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event) :
    C ∈ minimalCutSets t ↔
      C ∈ cutSets t ∧ ∀ D ∈ cutSets t, ¬ D ⊂ C := by
  unfold minimalCutSets
  exact mem_minimizeCutSets_iff C (cutSets t)

/-- Every generated minimal cut set is sound and minimal among generated cut sets. -/
theorem minimalCutSets_sound_and_generated_minimal [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event)
    (h : C ∈ minimalCutSets t) :
    IsCutSet C t ∧ ∀ D, D ∈ cutSets t → ¬ D ⊂ C := by
  constructor
  · exact minimalCutSets_sound t C h
  · exact minimalCutSets_generated_minimal t C h

/-- A generated cut set with no smaller generated cut set belongs to `minimalCutSets`. -/
theorem minimalCutSets_complete_generated [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event)
    (hGen : C ∈ cutSets t)
    (hMin : ∀ D, D ∈ cutSets t → ¬ D ⊂ C) :
    C ∈ minimalCutSets t := by
  rw [mem_minimalCutSets_iff]
  exact ⟨hGen, hMin⟩

/-- Characterization of generated minimal cut sets. -/
theorem minimalCutSets_correct_generated [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event) :
    C ∈ minimalCutSets t ↔
      C ∈ cutSets t ∧ ∀ D, D ∈ cutSets t → ¬ D ⊂ C := by
  exact mem_minimalCutSets_iff t C

/--
Correctness package for generated minimal cut sets:
membership in `cutSets`, semantic validity, and generated minimality.
-/
theorem minimalCutSets_correct_package [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event)
    (h : C ∈ minimalCutSets t) :
    C ∈ cutSets t ∧
    IsCutSet C t ∧
    ∀ D, D ∈ cutSets t → ¬ D ⊂ C := by
  constructor
  · exact minimalCutSets_subset_cutSets t C h
  constructor
  · exact minimalCutSets_sound t C h
  · exact minimalCutSets_generated_minimal t C h

/-- Every generated minimal cut set is a semantic cut set. -/
theorem minimalCutSets_semantic_sound [DecidableEq Event]
    (t : CFTree Event) (C : CutSet Event)
    (h : C ∈ minimalCutSets t) :
    IsCutSet C t := by
  exact minimalCutSets_sound t C h

end CFTree
