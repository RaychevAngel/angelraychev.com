import ConstructionCounts
import VertexBound
import CampingObstruction

/-! Actual-game support and degree counts for the sparse upper bounds.
All active sets and rectangle counts are computed from the original graph. -/
namespace Delivery.SparseSupport
open FiniteGame Extremal DenseCombinatorics ConstructionCounts

/-- A live recipient needs two distinct predecessors, in the original arrow
direction. This is not obtained by reversing the game. -/
theorem live_recipient_two_predecessors {V : Type} {E : Graph V} {s t : V}
    (indirect : Indirect E s t) : ∃ a b, E a t ∧ E b t ∧ a ≠ b := by
  classical
  apply Classical.byContradiction
  intro absent
  by_cases has : ∃ a, E a t
  · obtain ⟨a,edge⟩ := has
    have unique : ∀ b, E b t → b = a := by
      intro b hb
      apply Classical.byContradiction
      intro different
      exact absent ⟨b,a,hb,edge,different⟩
    have initial : a ≠ s := by
      intro same
      exact indirect.2.1 (same ▸ edge)
    obtain ⟨k,win⟩ := indirect.2.2 a initial
    exact camping_predecessor_obstruction indirect.1 indirect.2.1
      (fun b hb => Or.inl (unique b hb).symm) win
  · obtain ⟨k,win⟩ := indirect.2.2 t (Ne.symm indirect.1)
    exact camping_predecessor_obstruction indirect.1 indirect.2.1
      (fun b hb => False.elim (has ⟨b,hb⟩)) win

theorem card_ge_two {n : Nat} {P : Fin n → Prop} {a b : Fin n}
    (ha : P a) (hb : P b) (different : a ≠ b) : 2 ≤ card P := by
  have nd : [a,b].Nodup := by simp [different]
  have subset : [a,b] ⊆ elems P := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> exact mem_elems.mpr (by assumption)
  exact nd.length_le_of_subset subset

noncomputable def outdegree {n : Nat} (E : Graph (Fin n)) (s : Fin n) : Nat := card (E s)
noncomputable def indegree {n : Nat} (E : Graph (Fin n)) (t : Fin n) : Nat := card (fun s => E s t)

def ActiveOut {n : Nat} (E : Graph (Fin n)) (s : Fin n) : Prop := 2 ≤ outdegree E s
def ActiveIn {n : Nat} (E : Graph (Fin n)) (t : Fin n) : Prop := 2 ≤ indegree E t

noncomputable instance {n : Nat} (E : Graph (Fin n)) (s : Fin n) : Decidable (ActiveOut E s) :=
  inferInstanceAs (Decidable (2 ≤ outdegree E s))
noncomputable instance {n : Nat} (E : Graph (Fin n)) (t : Fin n) : Decidable (ActiveIn E t) :=
  inferInstanceAs (Decidable (2 ≤ indegree E t))

theorem live_outdegree {n : Nat} {E : Graph (Fin n)} (loopless : Loopless E)
    {s t : Fin n} (indirect : Indirect E s t) : 2 ≤ outdegree E s := by
  obtain ⟨a,b,ha,hb,different⟩ := VertexBound.live_source_two_neighbors loopless indirect
  exact card_ge_two ha hb different

theorem live_indegree {n : Nat} {E : Graph (Fin n)}
    {s t : Fin n} (indirect : Indirect E s t) : 2 ≤ indegree E t := by
  obtain ⟨a,b,ha,hb,different⟩ := live_recipient_two_predecessors indirect
  exact card_ge_two ha hb different

theorem arcs_congr {n : Nat} {E F : Graph (Fin n)}
    (same : ∀ s t, E s t ↔ F s t) : arcCount E = arcCount F := by
  classical
  rw [arcCount_eq,arcCount_eq]
  exact filter_count_congr (allPairs n) _ _ (fun p => same p.1 p.2)

theorem arcs_mono {n : Nat} {E F : Graph (Fin n)}
    (subset : ∀ s t, E s t → F s t) : arcCount E ≤ arcCount F := by
  classical
  apply filter_length_mono
  intro p hp
  exact decide_eq_true (subset p.1 p.2 (of_decide_eq_true hp))

theorem arcs_partition {n : Nat} (E F : Graph (Fin n)) :
    arcCount (fun s t => E s t ∧ F s t) +
      arcCount (fun s t => E s t ∧ ¬ F s t) = arcCount E := by
  classical
  rw [arcCount_eq,arcCount_eq,arcCount_eq]
  exact filter_partition_prop (allPairs n) _ _

theorem arcs_union {n : Nat} {E F : Graph (Fin n)}
    (disjoint : ∀ s t, E s t → F s t → False) :
    arcCount (fun s t => E s t ∨ F s t) = arcCount E + arcCount F := by
  have split := arcs_partition (fun s t => E s t ∨ F s t) E
  have left : arcCount (fun s t => (E s t ∨ F s t) ∧ E s t) = arcCount E :=
    arcs_congr (fun _ _ => ⟨And.right,fun h => ⟨Or.inl h,h⟩⟩)
  have right : arcCount (fun s t => (E s t ∨ F s t) ∧ ¬ E s t) = arcCount F :=
    arcs_congr (fun s t => ⟨fun h => h.1.resolve_left h.2,
      fun h => ⟨Or.inr h,fun he => disjoint s t he h⟩⟩)
  omega

theorem arc_rows {n : Nat} (E : Graph (Fin n)) :
    arcCount E = ((List.finRange n).map fun s => card (E s)).sum := by
  classical
  unfold arcCount allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,card_eq]

theorem arc_transpose {n : Nat} (E : Graph (Fin n)) :
    arcCount (fun s t => E t s) = arcCount E := by
  classical
  have every (p : Fin n × Fin n) : p ∈ allPairs n := by
    simp [allPairs,List.mem_flatMap,List.mem_map]
    exact ⟨p.1,p.2,rfl⟩
  have nd : ((allPairs n).map Prod.swap).Nodup := by
    apply List.pairwise_map.mpr
    exact (DenseZero.allPairs_nodup n).imp
      (fun h same => h (by simpa using congrArg Prod.swap same))
  have perm := (List.perm_ext_iff_of_nodup nd (DenseZero.allPairs_nodup n)).mpr (by
    intro p
    constructor
    · intro _; exact every p
    · intro _; exact List.mem_map.mpr ⟨p.swap,every _,by simp⟩)
  have counted := (perm.filter (fun p => decide (E p.1 p.2))).length_eq
  simpa only [arcCount,List.filter_map,List.length_map,Function.comp_def,Prod.swap] using counted

theorem arc_columns {n : Nat} (E : Graph (Fin n)) :
    arcCount E = ((List.finRange n).map fun t => card (fun s => E s t)).sum := by
  rw [← arc_transpose E,arc_rows]

theorem indicator_sum {n : Nat} (P : Fin n → Prop) (d : Nat) [DecidablePred P] :
    ((List.finRange n).map fun x => if P x then d else 0).sum = d * card P := by
  have h := weighted_indicators (List.finRange n) P (fun _ => False) d 0
  simpa only [if_false,Nat.add_zero,Nat.zero_mul,card_eq] using h

theorem degree_active_bound {n : Nat} (degree : Fin n → Nat) :
    2 * card (fun x => 2 ≤ degree x) ≤ ((List.finRange n).map degree).sum := by
  classical
  have bound := sum_mono (List.finRange n) (f := fun x => if 2 ≤ degree x then 2 else 0)
    (g := degree) (by intro x; split <;> omega)
  rw [indicator_sum] at bound
  exact bound

theorem degree_positive_bound {n : Nat} (degree : Fin n → Nat)
    (positive : ∀ x, 1 ≤ degree x) :
    n + card (fun x => 2 ≤ degree x) ≤ ((List.finRange n).map degree).sum := by
  classical
  have bound := sum_mono (List.finRange n) (f := fun x => if 2 ≤ degree x then 2 else 1)
    (g := degree) (by intro x; have := positive x; split <;> omega)
  rw [one_or_two,List.length_finRange] at bound
  simpa only [card_eq] using bound

noncomputable def cut {n : Nat} (E : Graph (Fin n)) (A B : Fin n → Prop) : Nat :=
  arcCount (fun s t => E s t ∧ A s ∧ B t)

theorem rectangle_count {n : Nat} (A B : Fin n → Prop) :
    arcCount (fun s t => A s ∧ B t) = card A * card B := by
  classical
  rw [arc_rows]
  have row (s : Fin n) : card (fun t => A s ∧ B t) = if A s then card B else 0 := by
    by_cases hs : A s
    · rw [if_pos hs]
      exact card_congr (fun _ => ⟨And.right,fun h => ⟨hs,h⟩⟩)
    · rw [if_neg hs]
      exact card_eq_zero.mpr (fun _ h => hs h.1)
  simp only [row]
  rw [indicator_sum,Nat.mul_comm]

theorem diagonal_count {n : Nat} (A B : Fin n → Prop) :
    arcCount (fun s t => A s ∧ B t ∧ s = t) = card (fun s => A s ∧ B s) := by
  classical
  rw [arc_rows]
  have row (s : Fin n) : card (fun t => A s ∧ B t ∧ s = t) =
      if A s ∧ B s then 1 else 0 := by
    by_cases hs : A s ∧ B s
    · rw [if_pos hs]
      have same : card (fun t => A s ∧ B t ∧ s = t) = card (fun t => t = s) :=
        card_congr (fun t => ⟨fun h => h.2.2.symm,fun h => by subst t; exact ⟨hs.1,hs.2,rfl⟩⟩)
      rw [same,card_eq]
      simp [List.filter_eq,(List.nodup_finRange n).count]
    · rw [if_neg hs]
      apply card_eq_zero.mpr
      intro t h
      exact hs ⟨h.1,h.2.2.symm ▸ h.2.1⟩
  simp only [row]
  rw [indicator_sum,Nat.one_mul]

/-- Guarantees, diagonal pairs, and existing arrows are disjoint inside
the active source-recipient rectangle. -/
theorem eligible_rectangle {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E) :
    score E + card (fun x => ActiveOut E x ∧ ActiveIn E x) +
      cut E (ActiveOut E) (ActiveIn E) ≤ card (ActiveOut E) * card (ActiveIn E) := by
  let D := fun s t => ActiveOut E s ∧ ActiveIn E t ∧ s = t
  let F := fun s t => E s t ∧ ActiveOut E s ∧ ActiveIn E t
  have first := arcs_union (E := Indirect E) (F := D)
    (fun s t hi hd => hi.1 hd.2.2)
  have second := arcs_union (E := fun s t => Indirect E s t ∨ D s t) (F := F) (by
    intro s t h hf
    rcases h with hi | hd
    · exact hi.2.1 hf.1
    · exact loopless s (hd.2.2.symm ▸ hf.1))
  have bound := arcs_mono (E := fun s t => (Indirect E s t ∨ D s t) ∨ F s t)
    (F := fun s t => ActiveOut E s ∧ ActiveIn E t) (by
      intro s t h
      rcases h with (hi | hd) | hf
      · exact ⟨live_outdegree loopless hi,live_indegree hi⟩
      · exact ⟨hd.1,hd.2.1⟩
      · exact hf.2)
  rw [rectangle_count] at bound
  have diag : arcCount D = card (fun x => ActiveOut E x ∧ ActiveIn E x) :=
    diagonal_count _ _
  have success : arcCount (Indirect E) = score E := rfl
  change score E + card (fun x => ActiveOut E x ∧ ActiveIn E x) + arcCount F ≤ _
  omega

theorem cut_total {n : Nat} (E : Graph (Fin n)) :
    cut E (fun _ => True) (fun _ => True) = arcCount E :=
  arcs_congr (fun _ _ => ⟨And.left,fun h => ⟨h,trivial,trivial⟩⟩)

theorem cut_source_partition {n : Nat} (E : Graph (Fin n)) (A B : Fin n → Prop) :
    cut E A B + cut E (fun s => ¬ A s) B = cut E (fun _ => True) B := by
  have split := arcs_partition (fun s t => E s t ∧ B t) (fun s _ => A s)
  have l : arcCount (fun s t => (E s t ∧ B t) ∧ A s) = cut E A B :=
    arcs_congr (fun _ _ => ⟨fun h => ⟨h.1.1,h.2,h.1.2⟩,fun h => ⟨⟨h.1,h.2.2⟩,h.2.1⟩⟩)
  have r : arcCount (fun s t => (E s t ∧ B t) ∧ ¬ A s) = cut E (fun s => ¬ A s) B :=
    arcs_congr (fun _ _ => ⟨fun h => ⟨h.1.1,h.2,h.1.2⟩,fun h => ⟨⟨h.1,h.2.2⟩,h.2.1⟩⟩)
  have all : arcCount (fun s t => E s t ∧ B t) = cut E (fun _ => True) B :=
    arcs_congr (fun _ _ => ⟨fun h => ⟨h.1,trivial,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩)
  omega

theorem cut_target_partition {n : Nat} (E : Graph (Fin n)) (A B : Fin n → Prop) :
    cut E A B + cut E A (fun t => ¬ B t) = cut E A (fun _ => True) := by
  have split := arcs_partition (fun s t => E s t ∧ A s) (fun _ t => B t)
  have l : arcCount (fun s t => (E s t ∧ A s) ∧ B t) = cut E A B :=
    arcs_congr (fun _ _ => ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩⟩)
  have r : arcCount (fun s t => (E s t ∧ A s) ∧ ¬ B t) = cut E A (fun t => ¬ B t) :=
    arcs_congr (fun _ _ => ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩⟩)
  have all : arcCount (fun s t => E s t ∧ A s) = cut E A (fun _ => True) :=
    arcs_congr (fun _ _ => ⟨fun h => ⟨h.1,h.2,trivial⟩,fun h => ⟨h.1,h.2.1⟩⟩)
  omega

theorem cut_incidence {n : Nat} (E : Graph (Fin n)) (A B : Fin n → Prop) :
    cut E A (fun _ => True) + cut E (fun _ => True) B ≤ arcCount E + cut E A B := by
  have p := cut_source_partition E A (fun _ => True)
  have q := cut_target_partition E A B
  have r := cut_target_partition E (fun s => ¬ A s) B
  have s := cut_source_partition E A B
  rw [cut_total] at p
  omega

theorem cut_cover {n : Nat} (E : Graph (Fin n)) (A B : Fin n → Prop) :
    arcCount E ≤ cut E A B + cut E (fun s => ¬ A s) (fun _ => True) +
      cut E (fun _ => True) (fun t => ¬ B t) := by
  have p := cut_source_partition E A (fun _ => True)
  have q := cut_target_partition E A B
  have r := cut_source_partition E A (fun t => ¬ B t)
  rw [cut_total] at p
  omega

theorem cut_out_rows {n : Nat} (E : Graph (Fin n)) (A : Fin n → Prop) [DecidablePred A] :
    cut E A (fun _ => True) =
      ((List.finRange n).map fun s => if A s then outdegree E s else 0).sum := by
  classical
  unfold cut
  rw [arc_rows]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  by_cases hs : A s
  · rw [if_pos hs]
    exact card_congr (fun _ => ⟨And.left,fun h => ⟨h,hs,trivial⟩⟩)
  · rw [if_neg hs]
    exact card_eq_zero.mpr (fun _ h => hs h.2.1)

theorem cut_transpose {n : Nat} (E : Graph (Fin n)) (A B : Fin n → Prop) :
    cut (fun s t => E t s) B A = cut E A B := by
  unfold cut
  rw [← arc_transpose (fun s t => E s t ∧ A s ∧ B t)]
  exact arcs_congr (fun _ _ => ⟨fun h => ⟨h.1,h.2.2,h.2.1⟩,fun h => ⟨h.1,h.2.2,h.2.1⟩⟩)

theorem cut_in_columns {n : Nat} (E : Graph (Fin n)) (B : Fin n → Prop) [DecidablePred B] :
    cut E (fun _ => True) B =
      ((List.finRange n).map fun t => if B t then indegree E t else 0).sum := by
  rw [← cut_transpose E (fun _ => True) B,cut_out_rows]
  rfl

theorem selected_degree_bound {n : Nat} (degree : Fin n → Nat) :
    2 * card (fun x => 2 ≤ degree x) ≤
      ((List.finRange n).map fun x => if 2 ≤ degree x then degree x else 0).sum := by
  classical
  have bound := sum_mono (List.finRange n) (f := fun x => if 2 ≤ degree x then 2 else 0)
    (g := fun x => if 2 ≤ degree x then degree x else 0)
    (by intro x; by_cases h : 2 ≤ degree x <;> simp only [h,if_true,if_false] <;> omega)
  rw [indicator_sum] at bound
  exact bound

theorem inactive_degree_count {n : Nat} (degree : Fin n → Nat)
    (positive : ∀ x, 1 ≤ degree x) :
    ((List.finRange n).map fun x => if ¬ 2 ≤ degree x then degree x else 0).sum =
      card (fun x => ¬ 2 ≤ degree x) := by
  classical
  have values (x : Fin n) : (if ¬ 2 ≤ degree x then degree x else 0) =
      if ¬ 2 ≤ degree x then 1 else 0 := by
    have lower := positive x
    by_cases h : 2 ≤ degree x <;> simp only [h,not_true_eq_false,not_false_eq_true,if_true,if_false] <;> omega
  simp only [values]
  rw [indicator_sum,Nat.one_mul]

theorem card_complement {n : Nat} (P : Fin n → Prop) :
    card P + card (fun x => ¬ P x) = n := by
  have split := card_partition (fun _ : Fin n => True) P
  have left := card_congr (P := fun x => True ∧ P x) (Q := P)
    (fun _ => ⟨And.right,fun h => ⟨trivial,h⟩⟩)
  have right := card_congr (P := fun x => True ∧ ¬ P x) (Q := fun x => ¬ P x)
    (fun _ => ⟨And.right,fun h => ⟨trivial,h⟩⟩)
  rw [card_true] at split
  omega

theorem card_overlap {n : Nat} (P Q : Fin n → Prop) :
    card P + card Q ≤ n + card (fun x => P x ∧ Q x) := by
  have split := card_partition Q P
  have both := card_congr (P := fun x => Q x ∧ P x) (Q := fun x => P x ∧ Q x)
    (fun _ => ⟨And.symm,And.symm⟩)
  have union := card_disjoint_union (P := P) (Q := fun x => Q x ∧ ¬ P x)
    (fun _ hp hq => hq.2 hp)
  have upper := card_mono (P := fun x => P x ∨ (Q x ∧ ¬ P x))
    (Q := fun _ => True) (fun _ _ => trivial)
  rw [card_true] at upper
  omega

/-- The active outgoing and incoming incidence counts share only the A×B cut. -/
theorem active_incidence {n : Nat} (E : Graph (Fin n)) :
    2 * card (ActiveOut E) + 2 * card (ActiveIn E) ≤
      arcCount E + cut E (ActiveOut E) (ActiveIn E) := by
  classical
  have out := selected_degree_bound (outdegree E)
  have inc := selected_degree_bound (indegree E)
  have shared := cut_incidence E (ActiveOut E) (ActiveIn E)
  rw [cut_out_rows,cut_in_columns] at shared
  change 2 * card (ActiveOut E) ≤
    ((List.finRange n).map fun x => if ActiveOut E x then outdegree E x else 0).sum at out
  change 2 * card (ActiveIn E) ≤
    ((List.finRange n).map fun x => if ActiveIn E x then indegree E x else 0).sum at inc
  omega

/-- Each active side consumes at least two original arrows per vertex. -/
theorem active_card_bounds {n : Nat} (E : Graph (Fin n)) :
    2 * card (ActiveOut E) ≤ arcCount E ∧ 2 * card (ActiveIn E) ≤ arcCount E := by
  have out := degree_active_bound (outdegree E)
  have inc := degree_active_bound (indegree E)
  have rows := arc_rows E
  have columns := arc_columns E
  change arcCount E = ((List.finRange n).map (outdegree E)).sum at rows
  change arcCount E = ((List.finRange n).map (indegree E)).sum at columns
  rw [← rows] at out
  rw [← columns] at inc
  exact ⟨out,inc⟩

/-- Positive support forces degree one outside each active set, giving the
stronger support capacities and active-cut lower bound used by sparse induction. -/
theorem positive_support_counts {n : Nat} (E : Graph (Fin n))
    (outPositive : ∀ s, 1 ≤ outdegree E s) (inPositive : ∀ t, 1 ≤ indegree E t) :
    n + card (ActiveOut E) ≤ arcCount E ∧
    n + card (ActiveIn E) ≤ arcCount E ∧
    arcCount E + card (ActiveOut E) + card (ActiveIn E) ≤
      cut E (ActiveOut E) (ActiveIn E) + 2*n := by
  classical
  have out := degree_positive_bound (outdegree E) outPositive
  have inc := degree_positive_bound (indegree E) inPositive
  have rows := arc_rows E
  have columns := arc_columns E
  change arcCount E = ((List.finRange n).map (outdegree E)).sum at rows
  change arcCount E = ((List.finRange n).map (indegree E)).sum at columns
  rw [← rows] at out
  rw [← columns] at inc
  have out' : n + card (ActiveOut E) ≤ arcCount E := out
  have inc' : n + card (ActiveIn E) ≤ arcCount E := inc
  have cover := cut_cover E (ActiveOut E) (ActiveIn E)
  rw [cut_out_rows,cut_in_columns] at cover
  have inactiveOut := inactive_degree_count (outdegree E) outPositive
  have inactiveIn := inactive_degree_count (indegree E) inPositive
  change ((List.finRange n).map fun x => if ¬ ActiveOut E x then outdegree E x else 0).sum =
    card (fun x => ¬ ActiveOut E x) at inactiveOut
  change ((List.finRange n).map fun x => if ¬ ActiveIn E x then indegree E x else 0).sum =
    card (fun x => ¬ ActiveIn E x) at inactiveIn
  rw [inactiveOut,inactiveIn] at cover
  have outSplit := card_complement (ActiveOut E)
  have inSplit := card_complement (ActiveIn E)
  exact ⟨out',inc',by omega⟩

/-- The ordinary positive-support bound, with every parameter derived from
the graph and every counted pair justified by the actual game. -/
theorem positive_support_bound {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (outPositive : ∀ s, 1 ≤ outdegree E s) (inPositive : ∀ t, 1 ≤ indegree E t) :
    score E ≤ card (ActiveOut E) * card (ActiveIn E) -
      (card (ActiveOut E) + card (ActiveIn E) - n) -
      (arcCount E + card (ActiveOut E) + card (ActiveIn E) - 2*n) := by
  have rectangle := eligible_rectangle E loopless
  have overlap := card_overlap (ActiveOut E) (ActiveIn E)
  have counts := (positive_support_counts E outPositive inPositive).2.2
  omega

#print axioms live_recipient_two_predecessors
#print axioms live_outdegree
#print axioms live_indegree
#print axioms eligible_rectangle
#print axioms active_incidence
#print axioms positive_support_counts
#print axioms positive_support_bound
end Delivery.SparseSupport
