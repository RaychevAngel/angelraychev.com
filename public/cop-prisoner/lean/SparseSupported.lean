import SparseDeletion

/-! Positive-support estimates on the original vertex type. Isolated vertices
are ignored by explicit support predicates; no relabeling or game reversal is
needed. -/
namespace Delivery.SparseSupported
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport

theorem degree_support_bound {n : Nat} (degree : Fin n → Nat)
    (P : Fin n → Prop) (support : ∀ x, 1 ≤ degree x ↔ P x) :
    card P + card (fun x => 2 ≤ degree x) ≤
      ((List.finRange n).map degree).sum := by
  classical
  have bound := sum_mono (List.finRange n)
    (f := fun x => (if P x then 1 else 0) + (if 2 ≤ degree x then 1 else 0))
    (g := degree) (by
      intro x
      by_cases p : P x
      · have lower := (support x).mpr p
        by_cases q : 2 ≤ degree x <;> simp only [p,q,if_true,if_false] <;> omega
      · have zero : degree x = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro positive
          exact p ((support x).mp positive)
        simp [p,zero])
  rw [weighted_indicators] at bound
  simpa only [Nat.one_mul,card_eq] using bound

theorem inactive_supported_count {n : Nat} (degree : Fin n → Nat)
    (P : Fin n → Prop) (support : ∀ x, 1 ≤ degree x ↔ P x) :
    ((List.finRange n).map fun x => if ¬ 2 ≤ degree x then degree x else 0).sum =
      card (fun x => P x ∧ ¬ 2 ≤ degree x) := by
  classical
  have values (x : Fin n) : (if ¬ 2 ≤ degree x then degree x else 0) =
      if P x ∧ ¬ 2 ≤ degree x then 1 else 0 := by
    by_cases p : P x
    · have lower := (support x).mpr p
      by_cases q : 2 ≤ degree x <;> simp only [p,q,not_true_eq_false,
        not_false_eq_true,and_true,and_false,if_true,if_false] <;> omega
    · have zero : degree x = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro positive
        exact p ((support x).mp positive)
      simp [p,zero]
  simp only [values]
  rw [indicator_sum,Nat.one_mul]

theorem card_supported_partition {n : Nat} (P A : Fin n → Prop)
    (subset : ∀ x, A x → P x) :
    card A + card (fun x => P x ∧ ¬ A x) = card P := by
  have split := card_partition P A
  have same := card_congr (P := fun x => P x ∧ A x) (Q := A)
    (fun x => ⟨And.right,fun h => ⟨subset x h,h⟩⟩)
  omega

theorem card_overlap_in {n : Nat} (P A B : Fin n → Prop)
    (a : ∀ x, A x → P x) (b : ∀ x, B x → P x) :
    card A + card B ≤ card P + card (fun x => A x ∧ B x) := by
  have split := card_partition B A
  have both := card_congr (P := fun x => B x ∧ A x) (Q := fun x => A x ∧ B x)
    (fun _ => ⟨And.symm,And.symm⟩)
  have union := card_disjoint_union (P := A) (Q := fun x => B x ∧ ¬ A x)
    (fun _ ha hb => hb.2 ha)
  have upper := card_mono (P := fun x => A x ∨ (B x ∧ ¬ A x)) (Q := P)
    (fun x h => h.elim (a x) (fun h => b x h.1))
  omega

/-- The support cardinal, rather than the ambient order, controls all three
degree estimates. The two support equivalences are the no-source/no-sink
condition after isolated vertices are ignored. -/
theorem supported_counts {n : Nat} (E : Graph (Fin n)) (P : Fin n → Prop)
    (outSupport : ∀ s, 1 ≤ outdegree E s ↔ P s)
    (inSupport : ∀ t, 1 ≤ indegree E t ↔ P t) :
    card P + card (ActiveOut E) ≤ arcCount E ∧
    card P + card (ActiveIn E) ≤ arcCount E ∧
    arcCount E + card (ActiveOut E) + card (ActiveIn E) ≤
      cut E (ActiveOut E) (ActiveIn E) + 2 * card P := by
  classical
  have out := degree_support_bound (outdegree E) P outSupport
  have inc := degree_support_bound (indegree E) P inSupport
  have rows := arc_rows E
  have columns := arc_columns E
  change arcCount E = ((List.finRange n).map (outdegree E)).sum at rows
  change arcCount E = ((List.finRange n).map (indegree E)).sum at columns
  rw [← rows] at out
  rw [← columns] at inc
  have out' : card P + card (ActiveOut E) ≤ arcCount E := out
  have inc' : card P + card (ActiveIn E) ≤ arcCount E := inc
  have cover := cut_cover E (ActiveOut E) (ActiveIn E)
  rw [cut_out_rows,cut_in_columns] at cover
  have inactiveOut := inactive_supported_count (outdegree E) P outSupport
  have inactiveIn := inactive_supported_count (indegree E) P inSupport
  change ((List.finRange n).map fun x => if ¬ ActiveOut E x then outdegree E x else 0).sum =
    card (fun x => P x ∧ ¬ ActiveOut E x) at inactiveOut
  change ((List.finRange n).map fun x => if ¬ ActiveIn E x then indegree E x else 0).sum =
    card (fun x => P x ∧ ¬ ActiveIn E x) at inactiveIn
  rw [inactiveOut,inactiveIn] at cover
  have outSplit := card_supported_partition P (ActiveOut E)
    (fun x h => (outSupport x).mp (by exact Nat.le_trans (by decide) h))
  have inSplit := card_supported_partition P (ActiveIn E)
    (fun x h => (inSupport x).mp (by exact Nat.le_trans (by decide) h))
  exact ⟨out',inc',by omega⟩

/-- The ordinary sparse support bound, valid even with arbitrarily many
isolated ambient vertices. Every parameter is computed from the graph. -/
theorem supported_bound {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (P : Fin n → Prop)
    (outSupport : ∀ s, 1 ≤ outdegree E s ↔ P s)
    (inSupport : ∀ t, 1 ≤ indegree E t ↔ P t) :
    score E ≤ card (ActiveOut E) * card (ActiveIn E) -
      (card (ActiveOut E) + card (ActiveIn E) - card P) -
      (arcCount E + card (ActiveOut E) + card (ActiveIn E) - 2 * card P) := by
  have rectangle := eligible_rectangle E loopless
  have overlap := card_overlap_in P (ActiveOut E) (ActiveIn E)
    (fun x h => (outSupport x).mp (by exact Nat.le_trans (by decide) h))
    (fun x h => (inSupport x).mp (by exact Nat.le_trans (by decide) h))
  have counts := (supported_counts E P outSupport inSupport).2.2
  omega

/-- Direct, indirect, and diagonal pairs all fit inside the same literal
support square. This is the missing-pair bound without support renumbering. -/
theorem supported_pair_bound {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (P : Fin n → Prop)
    (outSupport : ∀ s, 1 ≤ outdegree E s ↔ P s)
    (inSupport : ∀ t, 1 ≤ indegree E t ↔ P t) :
    score E + arcCount E + card P ≤ card P * card P := by
  let D := fun s t => P s ∧ P t ∧ s = t
  have first := arcs_union (E := Indirect E) (F := E)
    (fun _ _ pair edge => pair.2.1 edge)
  have second := arcs_union (E := fun s t => Indirect E s t ∨ E s t) (F := D) (by
    intro s t pair diag
    rcases pair with pair | edge
    · exact pair.1 diag.2.2
    · exact loopless s (diag.2.2.symm ▸ edge))
  have bound := arcs_mono (E := fun s t => (Indirect E s t ∨ E s t) ∨ D s t)
    (F := fun s t => P s ∧ P t) (by
      intro s t pair
      rcases pair with (pair | edge) | diag
      · exact ⟨(outSupport s).mp (Nat.le_trans (by decide) (live_outdegree loopless pair)),
          (inSupport t).mp (Nat.le_trans (by decide) (live_indegree pair))⟩
      · exact ⟨(outSupport s).mp (card_positive.mpr ⟨t,edge⟩),
          (inSupport t).mp (card_positive.mpr ⟨s,edge⟩)⟩
      · exact ⟨diag.1,diag.2.1⟩)
  rw [rectangle_count] at bound
  have diag : arcCount D = card P := by
    rw [show arcCount D = card (fun x => P x ∧ P x) from diagonal_count P P]
    exact card_congr (fun _ => ⟨And.left,fun h => ⟨h,h⟩⟩)
  have success : arcCount (Indirect E) = score E := rfl
  omega

/-- A graph without a nonisolated source or sink satisfies the supported
hypotheses directly. -/
theorem support_equivalences {n : Nat} (E : Graph (Fin n))
    (noSource : ∀ x, (∀ y, ¬ E y x) → ∀ y, ¬ E x y)
    (noSink : ∀ x, (∀ y, ¬ E x y) → ∀ y, ¬ E y x) :
    ∀ x, 1 ≤ indegree E x ↔ 1 ≤ outdegree E x := by
  intro x
  have outZero : outdegree E x = 0 ↔ ∀ y, ¬ E x y := card_eq_zero
  have inZero : indegree E x = 0 ↔ ∀ y, ¬ E y x := card_eq_zero
  constructor
  · intro positive
    apply Nat.le_of_not_lt
    intro small
    have zero := inZero.mpr (noSink x (outZero.mp (by omega)))
    omega
  · intro positive
    apply Nat.le_of_not_lt
    intro small
    have zero := outZero.mpr (noSource x (inZero.mp (by omega)))
    omega

#print axioms supported_counts
#print axioms supported_bound
#print axioms support_equivalences
end Delivery.SparseSupported
