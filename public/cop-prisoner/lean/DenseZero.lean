import VertexBound
import CampingObstruction

/-! The unconditional dense zero band, from the actual graph and game.
One guaranteed missing pair forces a missing nonloop arrow in every row.
Counting those rows gives the sharp density cutoff, without a supplied
degree or missing-pair cardinality hypothesis. -/
namespace Delivery.DenseZero
open FiniteGame Extremal

/-- Every row must miss a nonloop arrow if any indirect pair is guaranteed.
The source row already misses its recipient. A different full row supplies
a legal initial camping pursuer covering every possible intermediate. -/
theorem indirect_missing_each_row {V : Type} {E : Graph V} {s t : V}
    (indirect : Indirect E s t) (c : V) :
    ∃ z, c ≠ z ∧ ¬ E c z := by
  classical
  by_cases same : c = s
  · subst c
    exact ⟨t, indirect.1, indirect.2.1⟩
  · apply Classical.byContradiction
    intro none
    have full : ∀ z, Legal E c z := by
      intro z
      by_cases equal : c = z
      · exact Or.inl equal
      · apply Or.inr
        apply Classical.byContradiction
        intro missing
        exact none ⟨z, equal, missing⟩
    obtain ⟨k, win⟩ := indirect.2.2 c same
    exact camping_predecessor_obstruction indirect.1 indirect.2.1
      (fun z _ => full z) win

theorem two_excluded {n : Nat} (p : Fin n → Bool) (a b : Fin n)
    (different : a ≠ b) (ha : p a = false) (hb : p b = false) :
    ((List.finRange n).filter p).length ≤ n - 2 := by
  have distinct : [a,b].Nodup := by simp [different]
  have subset : [a,b] ⊆ (List.finRange n).filter (fun x => !(p x)) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;>
      simp [List.mem_filter, List.mem_finRange, ha, hb]
  have lower := distinct.length_le_of_subset subset
  have partition := VertexBound.filter_partition (List.finRange n) p
  simp only [List.length_cons, List.length_nil, List.length_finRange] at *
  omega

/-- The graph-to-count step: each outgoing row excludes its diagonal and
at least one further vertex, so it contributes at most `n - 2` arrows. -/
theorem arc_bound_of_indirect {n : Nat} (E : Graph (Fin n))
    (loopless : Loopless E) {s t : Fin n} (indirect : Indirect E s t) :
    arcCount E ≤ n * (n - 2) := by
  classical
  have rowBound (c : Fin n) :
      ((List.finRange n).filter fun z => decide (E c z)).length ≤ n - 2 := by
    obtain ⟨z, different, missing⟩ := indirect_missing_each_row indirect c
    exact two_excluded (fun z => decide (E c z)) c z different
      (by simp [loopless c]) (by simp [missing])
  unfold arcCount allPairs
  have bound := VertexBound.filtered_flatMap_bound (List.finRange n)
    (fun s => (List.finRange n).map fun t => (s,t))
    (fun p => decide (E p.1 p.2)) (n - 2) (by
      intro c _
      simpa only [List.filter_map, List.length_map, Function.comp_def]
        using rowBound c)
  simpa only [List.length_finRange] using bound

theorem filtered_flatMap_lower {α β : Type} (xs : List α) (row : α → List β)
    (p : β → Bool) (bound : Nat)
    (each : ∀ x, x ∈ xs → bound ≤ ((row x).filter p).length) :
    xs.length * bound ≤ ((xs.flatMap row).filter p).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have head := each x (by simp)
      have tail := ih (fun a ha => each a (by simp [ha]))
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The complementary count bridge: one indirect guarantee forces at least
one missing nonloop arrow in each of the `n` source rows. -/
theorem missing_count_lower_of_indirect {n : Nat} (E : Graph (Fin n))
    {s t : Fin n} (indirect : Indirect E s t) : n ≤ missingCount E := by
  classical
  have rowBound (c : Fin n) :
      1 ≤ ((List.finRange n).filter fun z => decide (c ≠ z ∧ ¬ E c z)).length := by
    obtain ⟨z, different, missing⟩ := indirect_missing_each_row indirect c
    have member : z ∈ (List.finRange n).filter
        (fun z => decide (c ≠ z ∧ ¬ E c z)) := by
      simp [List.mem_filter, List.mem_finRange, different, missing]
    have positive := List.length_pos_of_mem member
    omega
  unfold missingCount allPairs
  have bound := filtered_flatMap_lower (List.finRange n)
    (fun s => (List.finRange n).map fun t => (s,t))
    (fun p => decide (p.1 ≠ p.2 ∧ ¬ E p.1 p.2)) 1 (by
      intro c _
      simpa only [List.filter_map, List.length_map, Function.comp_def]
        using rowBound c)
  simpa only [List.length_finRange, Nat.mul_one] using bound

/-- Every loopless graph above the dense boundary has score zero.
No row-degree or cardinality premise is assumed. -/
theorem zero_above_dense_boundary {n : Nat} (E : Graph (Fin n))
    (loopless : Loopless E) (dense : n * (n - 2) < arcCount E) :
    score E = 0 := by
  apply score_eq_zero
  intro s t different missing guaranteed
  have bound := arc_bound_of_indirect E loopless
    (show Indirect E s t from ⟨different, missing, guaranteed⟩)
  omega

/-- The fixed-budget form of the dense zero band. -/
theorem zero_at_budget {n m : Nat} (E : Graph (Fin n))
    (loopless : Loopless E) (arrows : arcCount E = m)
    (dense : n * (n - 2) < m) : score E = 0 := by
  apply zero_above_dense_boundary E loopless
  omega

theorem positive_score_density_bound {n : Nat} (E : Graph (Fin n))
    (loopless : Loopless E) (positive : 0 < score E) :
    arcCount E ≤ n * (n - 2) := by
  apply Classical.byContradiction
  intro tooMany
  have zero := zero_above_dense_boundary E loopless (by omega)
  omega

/-- All nonloop ordered pairs, in source-first lexicographic order. -/
def nonloopPairs (n : Nat) : List (Fin n × Fin n) :=
  (allPairs n).filter fun p => decide (p.1 ≠ p.2)

/-- A prescribed graph with exactly the first `m` nonloop ordered pairs. -/
def initialGraph (n m : Nat) : Graph (Fin n) :=
  fun s t => (s,t) ∈ (nonloopPairs n).take m

theorem allPairs_nodup (n : Nat) : (allPairs n).Nodup := by
  unfold allPairs
  apply List.pairwise_flatMap.mpr
  constructor
  · intro s _
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange n).imp (fun h eq => h (congrArg Prod.snd eq))
  · apply (List.nodup_finRange n).imp
    intro a b different x hx y hy equal
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hy
    exact different (congrArg Prod.fst equal)

theorem nonloopPairs_length (n : Nat) : (nonloopPairs n).length = n * (n - 1) := by
  have row (s : Fin n) :
      ((List.finRange n).filter fun t => decide (s ≠ t)).length = n - 1 := by
    have one : ((List.finRange n).filter fun t => decide (s = t)).length = 1 := by
      simp only [eq_comm (a := s), List.filter_eq, List.length_replicate]
      simp [(List.nodup_finRange n).count]
    have partition := VertexBound.filter_partition (List.finRange n)
      (fun t => decide (s ≠ t))
    have same : (fun t => !(decide (s ≠ t))) = (fun t => decide (s = t)) := by
      funext t
      by_cases h : s = t <;> simp [h]
    rw [same, one, List.length_finRange] at partition
    omega
  unfold nonloopPairs allPairs
  rw [List.filter_flatMap, List.length_flatMap]
  simp only [List.filter_map, List.length_map, Function.comp_def, row]
  have constant (xs : List (Fin n)) :
      (xs.map fun _ => n - 1).sum = xs.length * (n - 1) := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih, Nat.add_mul, Nat.add_comm]
  simpa using constant (List.finRange n)

theorem initialGraph_loopless (n m : Nat) : Loopless (initialGraph n m) := by
  intro s edge
  have member := List.take_subset m (nonloopPairs n) edge
  have different := (List.mem_filter.mp member).2
  simp at different

theorem initialGraph_arcCount {n m : Nat} (admissible : m ≤ n * (n - 1)) :
    arcCount (initialGraph n m) = m := by
  classical
  let chosen := (nonloopPairs n).take m
  have nodup : chosen.Nodup :=
    (List.take_sublist m _).nodup ((allPairs_nodup n).filter _)
  have subset : chosen ⊆ allPairs n := by
    intro p hp
    exact (List.mem_filter.mp (List.take_subset m _ hp)).1
  have counted := (List.perm_ext_iff_of_nodup
    ((allPairs_nodup n).filter (fun p => decide (initialGraph n m p.1 p.2)))
    nodup).mpr (fun p => by
      rw [List.mem_filter]
      exact ⟨fun h => @of_decide_eq_true (initialGraph n m p.1 p.2)
          (Classical.propDecidable _) h.2,
        fun h => ⟨subset h, @decide_eq_true (initialGraph n m p.1 p.2)
          (Classical.propDecidable _) h⟩⟩)
  unfold arcCount
  rw [counted.length_eq]
  change ((nonloopPairs n).take m).length = m
  simp [List.length_take, nonloopPairs_length, Nat.min_eq_left admissible]

/-- The complete dense zero region, including an explicit attaining graph
at every admissible arrow budget. No graph-existence premise is assumed. -/
theorem maximum_zero {n m : Nat} (dense : n * (n - 2) < m)
    (admissible : m ≤ n * (n - 1)) : IsMaximum n m 0 := by
  constructor
  · intro E loopless arrows
    exact Nat.le_of_eq (zero_at_budget E loopless arrows dense)
  · refine ⟨initialGraph n m, initialGraph_loopless n m,
      initialGraph_arcCount admissible, ?_⟩
    exact zero_at_budget _ (initialGraph_loopless n m)
      (initialGraph_arcCount admissible) dense

#print axioms initialGraph_arcCount
#print axioms maximum_zero
#print axioms indirect_missing_each_row
#print axioms arc_bound_of_indirect
#print axioms missing_count_lower_of_indirect
#print axioms zero_above_dense_boundary
#print axioms zero_at_budget
#print axioms positive_score_density_bound
end Delivery.DenseZero
