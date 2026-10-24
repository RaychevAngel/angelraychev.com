import FiniteExclusionKernel
import VertexBound

namespace Delivery.FiniteExclusion
open FiniteGame Extremal

/-- A strict filter comparison needs a real omitted element, not an external
cardinality assertion. Repetitions in the ambient list are harmless. -/
theorem filter_length_strict {α : Type} (xs : List α) (p q : α → Bool)
    (mono : ∀ x, p x = true → q x = true)
    (witness : ∃ x, x ∈ xs ∧ q x = true ∧ p x = false) :
    (xs.filter p).length < (xs.filter q).length := by
  induction xs with
  | nil => simpa using witness
  | cons x xs ih =>
      obtain ⟨y,member,hqy,hpy⟩ := witness
      have member' : y = x ∨ y ∈ xs := by simpa using member
      rcases member' with same | tail
      · subst y
        have bound := filter_length_mono xs p q mono
        simp [hqy,hpy]
        omega
      · have strict := ih ⟨y,tail,hqy,hpy⟩
        cases hp : p x <;> cases hq : q x <;> simp [hp,hq] <;>
          try omega
        exact False.elim (Bool.noConfusion ((mono x hp).symm.trans hq))

theorem blocked_score_lt_missing {n} {a b : Assignment n}
    (blocked : Blocked a b) : score (edgeOf a b) < missingCount (edgeOf a b) := by
  classical
  obtain ⟨s,t,different,missing,loses⟩ := blocked
  apply filter_length_strict
  · intro p hp
    simp only [decide_eq_true_eq] at *
    exact ⟨hp.1,hp.2.1⟩
  · refine ⟨(s,t),?_,?_,?_⟩
    · simp [allPairs]
    · simp [different,missing]
    · simp [Indirect,loses]

theorem two_factor_missing_bound {n} (a b : Assignment n)
    (first_loopless : ∀ i, a i ≠ i) (valid : Valid a b) :
    missingCount (edgeOf a b) ≤ n * (n-3) := by
  classical
  have rowBound (s : Fin n) :
      ((List.finRange n).filter fun t => decide (s ≠ t ∧ ¬ edgeOf a b s t)).length ≤ n-3 := by
    apply VertexBound.three_excluded _ s (a s) (b s)
    · exact Ne.symm (first_loopless s)
    · exact Ne.symm (valid.2 s).1
    · exact Ne.symm (valid.2 s).2
    · simp
    · simp [edgeOf]
    · simp [edgeOf]
  rw [missingCount_eq]
  unfold allPairs
  have bound := VertexBound.filtered_flatMap_bound (List.finRange n)
    (fun s => (List.finRange n).map fun t => (s,t))
    (fun p => decide (p.1 ≠ p.2 ∧ ¬ edgeOf a b p.1 p.2)) (n-3) (by
      intro s _
      simpa only [List.filter_map, List.length_map, Function.comp_def]
        using rowBound s)
  simpa only [List.length_finRange] using bound

theorem nine_factor_upper (a b : Assignment 9)
    (first_loopless : ∀ i, a i ≠ i) (valid : Valid a b)
    (blocked : Blocked a b) : score (edgeOf a b) ≤ 53 := by
  have strict := blocked_score_lt_missing blocked
  have bound := two_factor_missing_bound a b first_loopless valid
  omega


theorem filtered_flatMap_exact {α β : Type} (xs : List α) (row : α → List β)
    (p : β → Bool) (count : Nat)
    (each : ∀ x, x ∈ xs → ((row x).filter p).length = count) :
    ((xs.flatMap row).filter p).length = xs.length * count := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have head := each x (by simp)
      have tail := ih (fun a ha => each a (by simp [ha]))
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.length_cons, head, tail, Nat.add_mul, Nat.one_mul]
      omega

theorem two_targets_count (u v : Fin 9) (different : u ≠ v) :
    ((List.finRange 9).filter fun t => decide (t = u ∨ t = v)).length = 2 := by
  revert u v
  decide +kernel

theorem three_removed_count (s u v : Fin 9)
    (su : s ≠ u) (sv : s ≠ v) (uv : u ≠ v) :
    ((List.finRange 9).filter fun t => decide (s ≠ t ∧ ¬ (t = u ∨ t = v))).length = 6 := by
  revert s u v
  decide +kernel

theorem nine_factor_arcs (a b : Assignment 9) (valid : Valid a b) :
    arcCount (edgeOf a b) = 18 := by
  rw [arcCount_eq]
  unfold allPairs
  have count := filtered_flatMap_exact (List.finRange 9)
    (fun s => (List.finRange 9).map fun t => (s,t))
    (fun p => decide (edgeOf a b p.1 p.2)) 2 (by
      intro s _
      simp only [List.filter_map, List.length_map, Function.comp_def]
      have same : (fun t => decide (edgeOf a b s t)) =
          (fun t => decide (t = a s ∨ t = b s)) := by
        funext t
        exact decide_eq_decide.mpr Iff.rfl
      rw [same]
      exact two_targets_count (a s) (b s) (Ne.symm (valid.2 s).2))
  simpa using count

theorem nine_factor_missing (a b : Assignment 9)
    (first_loopless : ∀ i, a i ≠ i) (valid : Valid a b) :
    missingCount (edgeOf a b) = 54 := by
  rw [missingCount_eq]
  unfold allPairs
  have count := filtered_flatMap_exact (List.finRange 9)
    (fun s => (List.finRange 9).map fun t => (s,t))
    (fun p => decide (p.1 ≠ p.2 ∧ ¬ edgeOf a b p.1 p.2)) 6 (by
      intro s _
      simp only [List.filter_map, List.length_map, Function.comp_def]
      have same : (fun t => decide (s ≠ t ∧ ¬ edgeOf a b s t)) =
          (fun t => decide (s ≠ t ∧ ¬ (t = a s ∨ t = b s))) := by
        funext t
        exact decide_eq_decide.mpr Iff.rfl
      rw [same]
      exact three_removed_count s (a s) (b s) (Ne.symm (first_loopless s))
          (Ne.symm (valid.2 s).1) (Ne.symm (valid.2 s).2))
  simpa using count

theorem factor_loopless {n} (a b : Assignment n)
    (first_loopless : ∀ i, a i ≠ i) (valid : Valid a b) : Loopless (edgeOf a b) := by
  intro i edge
  rcases edge with first | second
  · exact first_loopless i first.symm
  · exact (valid.2 i).1 second.symm

#print axioms nine_factor_upper
end Delivery.FiniteExclusion
