import Extremal

/-! The unrestricted vertex upper bound from the actual game.
A live source needs two distinct outgoing neighbors. Its own vertex and those
neighbors cannot be counted as guaranteed missing pairs. -/
namespace Delivery.VertexBound
open FiniteGame Extremal

/-- A stationary cop covering a source's outgoing neighbors defeats any
indirect strategy from that source, including strategies that first wait. -/
theorem source_camping {V : Type} {E : Graph V} {s t c : V}
    (distinct : s ≠ t) (missing : ¬ E s t)
    (cover : ∀ z, E s z → Legal E c z) :
    ∀ k, ¬ Winning E t k s c := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro win
      cases win with
      | delivered => exact distinct rfl
      | finish _ legal => exact legal.elim distinct missing
      | @step k r c z _ legal _ safe next =>
          rcases legal with same | edge
          · subst z
            exact ih k (by omega) (next c (legal_wait E c))
          · exact safe z (cover z edge) rfl

theorem live_source_two_neighbors {V : Type} {E : Graph V}
    (loopless : Loopless E) {s t : V} (indirect : Indirect E s t) :
    ∃ a b, E s a ∧ E s b ∧ a ≠ b := by
  classical
  apply Classical.byContradiction
  intro none
  by_cases has : ∃ a, E s a
  · obtain ⟨a, edge⟩ := has
    have single : ∀ z, E s z → z = a := by
      intro z hz
      by_cases same : z = a
      · exact same
      · exact False.elim (none ⟨z,a,hz,edge,same⟩)
    have initial : a ≠ s := by
      intro same; subst a; exact loopless s edge
    obtain ⟨k, win⟩ := indirect.2.2 a initial
    exact source_camping indirect.1 indirect.2.1
      (fun z hz => Or.inl (single z hz).symm) k win
  · have empty : ∀ z, ¬ E s z := fun z hz => has ⟨z,hz⟩
    obtain ⟨k, win⟩ := indirect.2.2 t (Ne.symm indirect.1)
    exact source_camping indirect.1 indirect.2.1
      (fun z hz => False.elim (empty z hz)) k win

theorem filter_partition {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length + (xs.filter fun x => !(p x)).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp] <;> omega

theorem three_excluded {n : Nat} (p : Fin n → Bool) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : p a = false) (hb : p b = false) (hc : p c = false) :
    ((List.finRange n).filter p).length ≤ n - 3 := by
  have distinct : [a,b,c].Nodup := by simp [hab, hac, hbc]
  have subset : [a,b,c] ⊆ (List.finRange n).filter (fun x => !(p x)) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;>
      simp [List.mem_filter, List.mem_finRange, ha, hb, hc]
  have lower := distinct.length_le_of_subset subset
  have partition := filter_partition (List.finRange n) p
  simp only [List.length_cons, List.length_nil, List.length_finRange] at *
  omega

noncomputable def rowScore {n : Nat} (E : Graph (Fin n)) (s : Fin n) : Nat := by
  classical
  exact ((List.finRange n).filter fun t => decide (Indirect E s t)).length

theorem row_bound {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (s : Fin n) : rowScore E s ≤ n - 3 := by
  classical
  by_cases live : ∃ t, Indirect E s t
  · obtain ⟨t, ht⟩ := live
    obtain ⟨a,b,ea,eb,different⟩ := live_source_two_neighbors loopless ht
    have sa : s ≠ a := by intro h; subst a; exact loopless s ea
    have sb : s ≠ b := by intro h; subst b; exact loopless s eb
    apply three_excluded (fun t => decide (Indirect E s t)) s a b sa sb different
    · simp [Indirect]
    · simp [Indirect, ea]
    · simp [Indirect, eb]
  · have zero : rowScore E s = 0 := by
      have none : ∀ t, ¬ Indirect E s t := fun t ht => live ⟨t,ht⟩
      simp [rowScore, none]
    omega

theorem filtered_flatMap_bound {α β : Type} (xs : List α) (row : α → List β)
    (p : β → Bool) (bound : Nat)
    (each : ∀ x, x ∈ xs → ((row x).filter p).length ≤ bound) :
    ((xs.flatMap row).filter p).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have head := each x (by simp)
      have tail := ih (fun a ha => each a (by simp [ha]))
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Every loopless graph satisfies the original unrestricted vertex bound.
Natural subtraction also gives the correct zero bound at orders below three. -/
theorem vertex_upper {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E) :
    score E ≤ n * (n - 3) := by
  classical
  unfold score allPairs
  have bound := filtered_flatMap_bound (List.finRange n)
    (fun s => (List.finRange n).map fun t => (s,t))
    (fun p => decide (Indirect E p.1 p.2)) (n-3) (by
      intro s _
      simpa only [List.filter_map, List.length_map, Function.comp_def, rowScore]
        using row_bound E loopless s)
  simpa only [List.length_finRange] using bound

#print axioms live_source_two_neighbors
#print axioms vertex_upper
end Delivery.VertexBound
