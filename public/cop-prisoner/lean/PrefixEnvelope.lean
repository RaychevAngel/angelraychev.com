import ConstructionCounts
import GraphRelabeling
import RobustTwoMove

/-! A literal optional-prefix recipe for every budget between two proved
two-move delivery envelopes. This supplies the formerly separate budget/count
obligation for finite envelope certificates. -/
namespace Delivery.PrefixEnvelope
open FiniteGame Extremal DenseCombinatorics RobustTwoMove

noncomputable def optional {n : Nat} (L U : Graph (Fin n)) : List (Fin n × Fin n) := by
  classical
  exact (allPairs n).filter fun p => decide (U p.1 p.2 ∧ ¬ L p.1 p.2)

noncomputable def graph {n : Nat} (L U : Graph (Fin n)) (q : Nat) : Graph (Fin n) :=
  fun s t => L s t ∨ (s,t) ∈ (optional L U).take q

theorem mem_optional {n : Nat} (L U : Graph (Fin n)) (p : Fin n × Fin n) :
    p ∈ optional L U ↔ U p.1 p.2 ∧ ¬ L p.1 p.2 := by
  classical
  simp only [optional,List.mem_filter,GraphRelabeling.allPairs_mem,true_and,decide_eq_true_eq]

theorem optional_nodup {n : Nat} (L U : Graph (Fin n)) : (optional L U).Nodup := by
  classical
  exact (DenseZero.allPairs_nodup n).filter _

theorem optional_length {n : Nat} (L U : Graph (Fin n)) (subset : Subgraph L U) :
    arcCount L + (optional L U).length = arcCount U := by
  classical
  have split := filter_partition_prop (allPairs n) (fun p => U p.1 p.2) (fun p => L p.1 p.2)
  have first : ((allPairs n).filter fun p => decide (U p.1 p.2 ∧ L p.1 p.2)).length = arcCount L := by
    rw [arcCount_eq]
    apply filter_count_congr
    intro p
    exact ⟨fun h => h.2,fun h => ⟨subset _ _ h,h⟩⟩
  rw [first] at split
  exact split

theorem lower {n : Nat} (L U : Graph (Fin n)) (q : Nat) : Subgraph L (graph L U q) :=
  fun _ _ h => Or.inl h

theorem upper {n : Nat} (L U : Graph (Fin n)) (q : Nat) (subset : Subgraph L U) :
    Subgraph (graph L U q) U := by
  intro s t edge
  rcases edge with h | h
  · exact subset s t h
  · exact ((mem_optional L U (s,t)).mp (List.take_subset q _ h)).1

theorem loopless {n : Nat} (L U : Graph (Fin n)) (q : Nat)
    (subset : Subgraph L U) (noLoops : Loopless U) : Loopless (graph L U q) :=
  fun s h => noLoops s (upper L U q subset s s h)

theorem selected_count {n : Nat} (xs : List (Fin n × Fin n)) (nd : xs.Nodup) :
    arcCount (fun s t => (s,t) ∈ xs) = xs.length := by
  classical
  rw [arcCount_eq]
  have perm := (List.perm_ext_iff_of_nodup
    ((DenseZero.allPairs_nodup n).filter (fun p => decide (p ∈ xs))) nd).mpr
    (fun p => by simp only [List.mem_filter,GraphRelabeling.allPairs_mem,true_and,decide_eq_true_eq])
  exact perm.length_eq

theorem arc_count {n : Nat} (L U : Graph (Fin n)) (q : Nat)
    (range : q ≤ (optional L U).length) : arcCount (graph L U q) = arcCount L + q := by
  classical
  let S : Graph (Fin n) := fun s t => (s,t) ∈ (optional L U).take q
  have separate (s t : Fin n) : L s t → S s t → False := by
    intro l mem
    exact ((mem_optional L U (s,t)).mp (List.take_subset q _ mem)).2 l
  have split := filter_partition_prop (allPairs n)
    (fun p => graph L U q p.1 p.2) (fun p => L p.1 p.2)
  have first : ((allPairs n).filter fun p => decide (graph L U q p.1 p.2 ∧ L p.1 p.2)).length = arcCount L := by
    rw [arcCount_eq]
    apply filter_count_congr
    intro p
    exact ⟨fun h => h.2,fun h => ⟨Or.inl h,h⟩⟩
  have second : ((allPairs n).filter fun p => decide (graph L U q p.1 p.2 ∧ ¬ L p.1 p.2)).length = arcCount S := by
    rw [arcCount_eq]
    apply filter_count_congr
    intro p
    exact ⟨fun h => h.1.resolve_left h.2,fun h => ⟨Or.inr h,fun l => separate _ _ l h⟩⟩
  rw [first,second] at split
  have selected : arcCount S = q := by
    rw [selected_count _ ((optional_nodup L U).take),List.length_take,Nat.min_eq_left range]
  rw [selected] at split
  exact split.symm

theorem two_move {n : Nat} (L U : Graph (Fin n)) (q : Nat)
    (subset : Subgraph L U) (witnesses : Witnesses L U) (s t : Fin n) :
    Universal (graph L U q) t 2 s :=
  envelope_universal (lower L U q) (upper L U q subset) witnesses s t

theorem score_count {n : Nat} (L U : Graph (Fin n)) (q : Nat)
    (subset : Subgraph L U) (noLoops : Loopless U) (witnesses : Witnesses L U)
    (range : q ≤ (optional L U).length) :
    score (graph L U q) = n*(n-1)-(arcCount L+q) := by
  have score : score (graph L U q) = missingCount (graph L U q) :=
    score_eq_missing _ (fun s t _ _ => universal_guaranteed (two_move L U q subset witnesses s t))
  have partition := arcCount_add_missingCount _ (loopless L U q subset noLoops)
  rw [arc_count L U q range] at partition
  omega

theorem maximum_at {n m : Nat} (L U : Graph (Fin n))
    (subset : Subgraph L U) (noLoops : Loopless U) (witnesses : Witnesses L U)
    (low : arcCount L ≤ m) (high : m ≤ arcCount U) :
    IsMaximum n m (n*(n-1)-m) := by
  have length := optional_length L U subset
  have range : m-arcCount L ≤ (optional L U).length := by omega
  have exactBudget : arcCount L+(m-arcCount L) = m := by omega
  constructor
  · intro E loops arrows
    have partition := arcCount_add_missingCount E loops
    have bound := score_le_missing E
    omega
  · refine ⟨graph L U (m-arcCount L),loopless L U _ subset noLoops,?_,?_⟩
    · rw [arc_count L U _ range,exactBudget]
    · rw [score_count L U _ subset noLoops witnesses range,exactBudget]

#print axioms graph
#print axioms arc_count
#print axioms maximum_at
end Delivery.PrefixEnvelope
