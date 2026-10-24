import GraphRestriction
import SparseSupport
import ComplementarySum

/-! Source/sink deletion and the capacities in the original arrow direction. -/
namespace Delivery.SparseDeletion
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport

variable {V : Type}

/-- A nonterminal finite winning route must eventually use an outgoing arrow;
waiting cannot create an escape from a sink. -/
theorem winning_has_successor {E : Graph V} {t r c : V} {k : Nat}
    (win : Winning E t k r c) : r ≠ t → ∃ z, E r z := by
  induction win with
  | delivered => exact fun different => False.elim (different rfl)
  | finish _ move =>
    intro different
    rcases move with same | edge
    · exact False.elim (different same)
    · exact ⟨_,edge⟩
  | @step k r c z _ move _ _ next ih =>
    intro different
    rcases move with same | edge
    · exact same ▸ ih c (legal_wait E c) (same.symm ▸ different)
    · exact ⟨z,edge⟩

/-- Camping need only cover predecessors that themselves have an incoming
arrow: an indegree-zero predecessor cannot be entered on an indirect route. -/
theorem camping_usable_predecessors {E : Graph V} {t r c : V} {k : Nat}
    (win : Winning E t k r c)
    (cover : ∀ z, E z t → (∃ u, E u z) → Legal E c z) : r = t ∨ E r t := by
  induction win with
  | delivered => exact Or.inl rfl
  | finish _ move => exact move
  | @step k r c z _ move _ safe next ih =>
    have nextDirect := ih c (legal_wait E c) cover
    rcases nextDirect with delivered | edgeToTarget
    · exact delivered ▸ move
    · rcases move with waiting | edgeToNext
      · exact Or.inr (waiting ▸ edgeToTarget)
      · exact False.elim (safe z (cover z edgeToTarget ⟨r,edgeToNext⟩) rfl)

/-- Source camping need only cover nonsink successors; any alternative
nonterminal departure traps the messenger at a sink. -/
theorem camping_nonsink_successors {E : Graph V} {s t c : V}
    (different : s ≠ t) (missing : ¬ E s t)
    (cover : ∀ z, E s z → (∃ u, E z u) → Legal E c z) :
    ∀ k, ¬ Winning E t k s c := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro win
    cases win with
    | delivered => exact different rfl
    | finish _ move => exact move.elim different missing
    | @step k r c z _ move _ safe next =>
      rcases move with waiting | edge
      · subst z
        exact ih k (by omega) (next c (legal_wait E c))
      · have zt : z ≠ t := fun same => missing (same ▸ edge)
        have usable := winning_has_successor (next c (legal_wait E c)) zt
        exact safe z (cover z edge usable) rfl

def UsablePredecessor (E : Graph V) (z t : V) : Prop := E z t ∧ ∃ u, E u z
def NonsinkSuccessor (E : Graph V) (s z : V) : Prop := E s z ∧ ∃ u, E z u

theorem live_two_usable_predecessors {E : Graph V} {s t : V}
    (pair : Indirect E s t) :
    ∃ a b, UsablePredecessor E a t ∧ UsablePredecessor E b t ∧ a ≠ b := by
  classical
  apply Classical.byContradiction
  intro absent
  by_cases has : ∃ a, UsablePredecessor E a t
  · obtain ⟨a,ha⟩ := has
    have unique : ∀ b, UsablePredecessor E b t → b = a := by
      intro b hb
      apply Classical.byContradiction
      intro different
      exact absent ⟨b,a,hb,ha,different⟩
    have initial : a ≠ s := fun same => pair.2.1 (same ▸ ha.1)
    obtain ⟨k,win⟩ := pair.2.2 a initial
    have direct := camping_usable_predecessors win
      (fun z edge usable => Or.inl (unique z ⟨edge,usable⟩).symm)
    exact direct.elim pair.1 pair.2.1
  · obtain ⟨k,win⟩ := pair.2.2 t (Ne.symm pair.1)
    have direct := camping_usable_predecessors win
      (fun z edge usable => False.elim (has ⟨z,edge,usable⟩))
    exact direct.elim pair.1 pair.2.1

theorem live_two_nonsink_successors {E : Graph V} (loopless : Loopless E) {s t : V}
    (pair : Indirect E s t) :
    ∃ a b, NonsinkSuccessor E s a ∧ NonsinkSuccessor E s b ∧ a ≠ b := by
  classical
  apply Classical.byContradiction
  intro absent
  by_cases has : ∃ a, NonsinkSuccessor E s a
  · obtain ⟨a,ha⟩ := has
    have unique : ∀ b, NonsinkSuccessor E s b → b = a := by
      intro b hb
      apply Classical.byContradiction
      intro different
      exact absent ⟨b,a,hb,ha,different⟩
    have initial : a ≠ s := fun same => loopless s (same ▸ ha.1)
    obtain ⟨k,win⟩ := pair.2.2 a initial
    exact camping_nonsink_successors pair.1 pair.2.1
      (fun z edge usable => Or.inl (unique z ⟨edge,usable⟩).symm) k win
  · obtain ⟨k,win⟩ := pair.2.2 t (Ne.symm pair.1)
    exact camping_nonsink_successors pair.1 pair.2.1
      (fun z edge usable => False.elim (has ⟨z,edge,usable⟩)) k win

def LiveIn {n : Nat} (E : Graph (Fin n)) (t : Fin n) : Prop := ∃ s, Indirect E s t
def LiveOut {n : Nat} (E : Graph (Fin n)) (s : Fin n) : Prop := ∃ t, Indirect E s t

theorem live_in_capacity {n : Nat} (E : Graph (Fin n)) :
    2 * card (LiveIn E) ≤ arcCount (UsablePredecessor E) := by
  classical
  have bound := sum_mono (List.finRange n)
    (f := fun t => if LiveIn E t then 2 else 0)
    (g := fun t => card (fun s => UsablePredecessor E s t)) (by
      intro t
      by_cases live : LiveIn E t
      · rw [if_pos live]
        obtain ⟨s,pair⟩ := live
        obtain ⟨a,b,ha,hb,different⟩ := live_two_usable_predecessors pair
        exact card_ge_two ha hb different
      · simp [live])
  rw [indicator_sum,← arc_columns] at bound
  exact bound

theorem live_out_capacity {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E) :
    2 * card (LiveOut E) ≤ arcCount (NonsinkSuccessor E) := by
  classical
  have bound := sum_mono (List.finRange n)
    (f := fun s => if LiveOut E s then 2 else 0)
    (g := fun s => card (NonsinkSuccessor E s)) (by
      intro s
      by_cases live : LiveOut E s
      · rw [if_pos live]
        obtain ⟨t,pair⟩ := live
        obtain ⟨a,b,ha,hb,different⟩ := live_two_nonsink_successors loopless pair
        exact card_ge_two ha hb different
      · simp [live])
  rw [indicator_sum,← arc_rows] at bound
  exact bound

def masked (E : Graph V) (P : V → Prop) : Graph V := fun s t => E s t ∧ P s ∧ P t

theorem masked_legal {E : Graph V} {P : V → Prop} {s t : V}
    (move : Legal (masked E P) s t) : Legal E s t :=
  move.elim Or.inl (fun edge => Or.inr edge.1)

/-- A retained winning messenger strategy also works when removed vertices
are isolated, including against a pursuer starting at a new isolate. -/
theorem winning_masked {E : Graph V} {P : V → Prop} {t : V}
    (retain : ∀ r c z k, P r → Legal E r z → Winning E t k z c → P z)
    {r c : V} {k : Nat} (win : Winning E t k r c) :
    P t → P r → Winning (masked E P) t k r c := by
  induction win with
  | delivered => intro _ _; exact Winning.delivered
  | finish distinct move =>
    intro target source
    apply Winning.finish distinct
    exact move.elim Or.inl (fun edge => Or.inr ⟨edge,source,target⟩)
  | @step k r c z distinct move safeNow safeReply next ih =>
    intro target source
    have hz : P z := retain r c z k source move (next c (legal_wait E c))
    apply Winning.step distinct
      (move.elim Or.inl (fun edge => Or.inr ⟨edge,source,hz⟩)) safeNow
    · intro c' reply
      exact safeReply c' (masked_legal reply)
    · intro c' reply
      exact ih c' (masked_legal reply) target hz

def isolate (E : Graph V) (v : V) : Graph V := masked E (fun x => x ≠ v)

theorem isolate_loopless {E : Graph V} (loopless : Loopless E) (v : V) :
    Loopless (isolate E v) := fun x edge => loopless x edge.1

theorem source_pair_survives {E : Graph V} (v : V) (source : ∀ x, ¬ E x v)
    {s t : V} (hs : s ≠ v) (ht : t ≠ v) (pair : Indirect E s t) :
    Indirect (isolate E v) s t := by
  refine ⟨pair.1,fun edge => pair.2.1 edge.1,?_⟩
  intro c initial
  obtain ⟨k,win⟩ := pair.2.2 c initial
  refine ⟨k,winning_masked (P := fun x => x ≠ v) ?_ win ht hs⟩
  intro r c z k retained move _
  rcases move with same | edge
  · exact same.symm ▸ retained
  · intro same
    exact source r (same ▸ edge)

theorem sink_pair_survives {E : Graph V} (v : V) (sink : ∀ x, ¬ E v x)
    {s t : V} (hs : s ≠ v) (ht : t ≠ v) (pair : Indirect E s t) :
    Indirect (isolate E v) s t := by
  refine ⟨pair.1,fun edge => pair.2.1 edge.1,?_⟩
  intro c initial
  obtain ⟨k,win⟩ := pair.2.2 c initial
  refine ⟨k,winning_masked (P := fun x => x ≠ v) ?_ win ht hs⟩
  intro r c z k _ _ next
  apply GraphRestriction.winning_source_mem (win := next) (target := ht)
  intro x y _ edge same
  exact sink y (same ▸ edge)

theorem card_singleton {n : Nat} (v : Fin n) : card (fun x => x = v) = 1 := by
  classical
  rw [card_eq]
  simp [List.filter_eq,(List.nodup_finRange n).count]

theorem single_source_cut {n : Nat} (E : Graph (Fin n)) (v : Fin n) :
    cut E (fun s => s = v) (fun _ => True) = outdegree E v := by
  classical
  rw [cut_out_rows]
  have values (s : Fin n) : (if s = v then outdegree E s else 0) =
      if s = v then outdegree E v else 0 := by
    by_cases same : s = v
    · subst s; rfl
    · simp [same]
  simp only [values]
  rw [indicator_sum,card_singleton,Nat.mul_one]

theorem single_target_cut {n : Nat} (E : Graph (Fin n)) (v : Fin n) :
    cut E (fun _ => True) (fun t => t = v) = indegree E v := by
  classical
  rw [cut_in_columns]
  have values (t : Fin n) : (if t = v then indegree E t else 0) =
      if t = v then indegree E v else 0 := by
    by_cases same : t = v
    · subst t; rfl
    · simp [same]
  simp only [values]
  rw [indicator_sum,card_singleton,Nat.mul_one]

theorem source_arc_count {n : Nat} (E : Graph (Fin n)) (v : Fin n)
    (source : ∀ x, ¬ E x v) : arcCount (isolate E v) + outdegree E v = arcCount E := by
  have split := cut_source_partition E (fun s => s = v) (fun _ => True)
  rw [cut_total,single_source_cut] at split
  have retained : cut E (fun s => ¬ s = v) (fun _ => True) = arcCount (isolate E v) := by
    apply arcs_congr
    intro s t
    exact ⟨fun h => ⟨h.1,h.2.1,fun same => source s (same ▸ h.1)⟩,
      fun h => ⟨h.1,h.2.1,trivial⟩⟩
  omega

theorem sink_arc_count {n : Nat} (E : Graph (Fin n)) (v : Fin n)
    (sink : ∀ x, ¬ E v x) : arcCount (isolate E v) + indegree E v = arcCount E := by
  have split := cut_target_partition E (fun _ => True) (fun t => t = v)
  rw [cut_total,single_target_cut] at split
  have retained : cut E (fun _ => True) (fun t => ¬ t = v) = arcCount (isolate E v) := by
    apply arcs_congr
    intro s t
    exact ⟨fun h => ⟨h.1,fun same => sink t (same ▸ h.1),h.2.2⟩,
      fun h => ⟨h.1,trivial,h.2.2⟩⟩
  omega

theorem source_score_bound {n : Nat} (E : Graph (Fin n)) (v : Fin n)
    (source : ∀ x, ¬ E x v) :
    score E ≤ score (isolate E v) + card (Indirect E v) := by
  have split := cut_source_partition (Indirect E) (fun s => s = v) (fun _ => True)
  rw [cut_total,single_source_cut] at split
  have bound : cut (Indirect E) (fun s => ¬ s = v) (fun _ => True) ≤
      arcCount (Indirect (isolate E v)) := by
    apply arcs_mono
    intro s t h
    have ht : t ≠ v := by
      intro same
      exact GraphRestriction.no_indirect_to_source v source s (same ▸ h.1)
    exact source_pair_survives v source h.2.1 ht h.1
  change card (Indirect E v) + _ = score E at split
  change _ ≤ score (isolate E v) at bound
  omega

theorem sink_score_bound {n : Nat} (E : Graph (Fin n)) (v : Fin n)
    (sink : ∀ x, ¬ E v x) :
    score E ≤ score (isolate E v) + card (fun s => Indirect E s v) := by
  have split := cut_target_partition (Indirect E) (fun _ => True) (fun t => t = v)
  rw [cut_total,single_target_cut] at split
  have bound : cut (Indirect E) (fun _ => True) (fun t => ¬ t = v) ≤
      arcCount (Indirect (isolate E v)) := by
    apply arcs_mono
    intro s t h
    have hs : s ≠ v := by
      intro same
      exact GraphRestriction.no_indirect_from_sink v sink t (same ▸ h.1)
    exact sink_pair_survives v sink hs h.2.2 h.1
  change card (fun s => Indirect E s v) + _ = score E at split
  change _ ≤ score (isolate E v) at bound
  omega

theorem source_row_capacity {n : Nat} (E : Graph (Fin n)) (v : Fin n)
    (source : ∀ x, ¬ E x v) :
    2 * card (Indirect E v) ≤ arcCount (isolate E v) := by
  have rows := card_mono (P := Indirect E v) (Q := LiveIn E) (fun t pair => ⟨v,pair⟩)
  have capacity := live_in_capacity E
  have bound : arcCount (UsablePredecessor E) ≤ arcCount (isolate E v) := by
    apply arcs_mono
    intro s t h
    refine ⟨h.1,?_,?_⟩
    · intro same
      obtain ⟨u,edge⟩ := h.2
      exact source u (same ▸ edge)
    · intro same
      exact source s (same ▸ h.1)
  omega

theorem sink_column_capacity {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (v : Fin n) (sink : ∀ x, ¬ E v x) :
    2 * card (fun s => Indirect E s v) ≤ arcCount (isolate E v) := by
  have rows := card_mono (P := fun s => Indirect E s v) (Q := LiveOut E) (fun s pair => ⟨v,pair⟩)
  have capacity := live_out_capacity E loopless
  have bound : arcCount (NonsinkSuccessor E) ≤ arcCount (isolate E v) := by
    apply arcs_mono
    intro s t h
    refine ⟨h.1,?_,?_⟩
    · intro same
      exact sink t (same ▸ h.1)
    · intro same
      obtain ⟨u,edge⟩ := h.2
      exact sink u (same ▸ edge)
  omega

/-- A diagonal and all incident arrows are excluded from an indirect row. -/
theorem row_nonadjacent_bound {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E) (v : Fin n) :
    card (Indirect E v) + outdegree E v + 1 ≤ n := by
  have first := card_disjoint_union (P := Indirect E v) (Q := E v)
    (fun t pair edge => pair.2.1 edge)
  have second := card_disjoint_union (P := fun t => Indirect E v t ∨ E v t)
    (Q := fun t => t = v) (by
      intro t h same
      subst t
      exact h.elim (fun pair => pair.1 rfl) (loopless v))
  have bound := card_mono (P := fun t => (Indirect E v t ∨ E v t) ∨ t = v)
    (Q := fun _ => True) (fun _ _ => trivial)
  rw [card_true] at bound
  rw [card_singleton] at second
  change card (fun t => Indirect E v t ∨ E v t) = card (Indirect E v) + outdegree E v at first
  omega

/-- The incoming version keeps the original direction of play. -/
theorem column_nonadjacent_bound {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E) (v : Fin n) :
    card (fun s => Indirect E s v) + indegree E v + 1 ≤ n := by
  have first := card_disjoint_union (P := fun s => Indirect E s v) (Q := fun s => E s v)
    (fun s pair edge => pair.2.1 edge)
  have second := card_disjoint_union (P := fun s => Indirect E s v ∨ E s v)
    (Q := fun s => s = v) (by
      intro s h same
      subst s
      exact h.elim (fun pair => pair.1 rfl) (loopless v))
  have bound := card_mono (P := fun s => (Indirect E s v ∨ E s v) ∨ s = v)
    (Q := fun _ => True) (fun _ _ => trivial)
  rw [card_true] at bound
  rw [card_singleton] at second
  change card (fun s => Indirect E s v ∨ E s v) =
    card (fun s => Indirect E s v) + indegree E v at first
  omega

/-- Exact source deletion bookkeeping, including both standard added-pair
bounds and the degree-zero/one case in which no pair is added. -/
theorem source_deletion {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (v : Fin n) (source : ∀ x, ¬ E x v) :
    arcCount (isolate E v) + outdegree E v = arcCount E ∧
    score E ≤ score (isolate E v) + arcCount (isolate E v) / 2 ∧
    score E ≤ score (isolate E v) + (n - 1 - outdegree E v) ∧
    (outdegree E v ≤ 1 → score E ≤ score (isolate E v)) := by
  have scoreBound := source_score_bound E v source
  have capacity := source_row_capacity E v source
  have nonadjacent := row_nonadjacent_bound E loopless v
  refine ⟨source_arc_count E v source,by omega,by omega,?_⟩
  intro small
  have empty : card (Indirect E v) = 0 := by
    apply card_eq_zero.mpr
    intro t pair
    have active := live_outdegree loopless pair
    omega
  omega

/-- Exact sink deletion bookkeeping; no graph reversal is used. -/
theorem sink_deletion {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (v : Fin n) (sink : ∀ x, ¬ E v x) :
    arcCount (isolate E v) + indegree E v = arcCount E ∧
    score E ≤ score (isolate E v) + arcCount (isolate E v) / 2 ∧
    score E ≤ score (isolate E v) + (n - 1 - indegree E v) ∧
    (indegree E v ≤ 1 → score E ≤ score (isolate E v)) := by
  have scoreBound := sink_score_bound E v sink
  have capacity := sink_column_capacity E loopless v sink
  have nonadjacent := column_nonadjacent_bound E loopless v
  refine ⟨sink_arc_count E v sink,by omega,by omega,?_⟩
  intro small
  have empty : card (fun s => Indirect E s v) = 0 := by
    apply card_eq_zero.mpr
    intro s pair
    have active := live_indegree pair
    omega
  omega

#print axioms camping_usable_predecessors
#print axioms camping_nonsink_successors
#print axioms live_in_capacity
#print axioms live_out_capacity
#print axioms winning_masked
#print axioms source_deletion
#print axioms sink_deletion
end Delivery.SparseDeletion
