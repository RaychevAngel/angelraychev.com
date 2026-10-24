import SparseSupported

/-! High-support cutoffs after source/sink deletion has left only
zero-side vertices of total degree two. All capacities count the actual graph. -/
namespace Delivery.SmallBudgetHighSupport
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport SparseDeletion

/-- Positive rows consume one arrow, and every live row consumes one more. -/
theorem outgoing_support {n : Nat} (E : Graph (Fin n)) (loops : Loopless E) :
    n + card (LiveOut E) ≤ arcCount E + card (fun x => outdegree E x=0) := by
  have support := SparseSupported.degree_support_bound (outdegree E)
    (fun x => ¬outdegree E x=0) (by intro x; omega)
  have live := card_mono (P:=LiveOut E) (Q:=ActiveOut E) (by
    rintro x ⟨t,pair⟩
    exact live_outdegree loops pair)
  have partition := card_complement (fun x => outdegree E x=0)
  have total := arc_rows E
  change arcCount E=((List.finRange n).map (outdegree E)).sum at total
  change card (fun x => ¬outdegree E x=0)+card (ActiveOut E)≤_ at support
  omega

/-- The incoming version uses the proved recipient obstruction, not reversal. -/
theorem incoming_support {n : Nat} (E : Graph (Fin n)) :
    n + card (LiveIn E) ≤ arcCount E + card (fun x => indegree E x=0) := by
  have support := SparseSupported.degree_support_bound (indegree E)
    (fun x => ¬indegree E x=0) (by intro x; omega)
  have live := card_mono (P:=LiveIn E) (Q:=ActiveIn E) (by
    rintro x ⟨s,pair⟩
    exact live_indegree pair)
  have partition := card_complement (fun x => indegree E x=0)
  have total := arc_columns E
  change arcCount E=((List.finRange n).map (indegree E)).sum at total
  change card (fun x => ¬indegree E x=0)+card (ActiveIn E)≤_ at support
  omega

theorem sink_capacity {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (sinks : ∀ x, outdegree E x=0 → indegree E x=2) :
    2*card (LiveOut E)+2*card (fun x => outdegree E x=0)≤arcCount E := by
  classical
  let S := fun x => outdegree E x=0
  have sinkCount : cut E (fun _ => True) S=2*card S := by
    rw [cut_in_columns]
    have values (x) : (if S x then indegree E x else 0)=(if S x then 2 else 0) := by
      by_cases h : S x
      · simp only [h,if_true,sinks x h]
      · simp only [h,if_false]
    simp only [values]
    exact indicator_sum S 2
  have split := cut_target_partition E (fun _ => True) S
  rw [cut_total] at split
  have rest : cut E (fun _ => True) (fun x => ¬S x)=arcCount (NonsinkSuccessor E) := by
    apply arcs_congr
    intro s t
    constructor
    · rintro ⟨edge,_,nonzero⟩
      exact ⟨edge,card_positive.mp (by change 0<outdegree E t; exact Nat.pos_of_ne_zero nonzero)⟩
    · rintro ⟨edge,existsEdge⟩
      exact ⟨edge,trivial,by
        have positive : 0<outdegree E t := card_positive.mpr existsEdge
        change ¬outdegree E t=0
        omega⟩
  have live := live_out_capacity E loops
  rw [sinkCount,rest] at split
  dsimp only [S] at split
  omega

theorem source_capacity {n : Nat} (E : Graph (Fin n))
    (sources : ∀ x, indegree E x=0 → outdegree E x=2) :
    2*card (LiveIn E)+2*card (fun x => indegree E x=0)≤arcCount E := by
  classical
  let S := fun x => indegree E x=0
  have sourceCount : cut E S (fun _ => True)=2*card S := by
    rw [cut_out_rows]
    have values (x) : (if S x then outdegree E x else 0)=(if S x then 2 else 0) := by
      by_cases h : S x
      · simp only [h,if_true,sources x h]
      · simp only [h,if_false]
    simp only [values]
    exact indicator_sum S 2
  have split := cut_source_partition E S (fun _ => True)
  rw [cut_total] at split
  have rest : cut E (fun x => ¬S x) (fun _ => True)=arcCount (UsablePredecessor E) := by
    apply arcs_congr
    intro s t
    constructor
    · rintro ⟨edge,nonzero,_⟩
      exact ⟨edge,card_positive.mp (by change 0<indegree E s; exact Nat.pos_of_ne_zero nonzero)⟩
    · rintro ⟨edge,existsEdge⟩
      exact ⟨edge,by
        have positive : 0<indegree E s := card_positive.mpr existsEdge
        change ¬indegree E s=0
        omega,trivial⟩
  have live := live_in_capacity E
  rw [sourceCount,rest] at split
  dsimp only [S] at split
  omega

theorem live_card_bound {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (sinks : ∀ x, outdegree E x=0 → indegree E x=2)
    (sources : ∀ x, indegree E x=0 → outdegree E x=2) :
    n+2*card (LiveOut E)≤arcCount E+arcCount E/2 ∧
    n+2*card (LiveIn E)≤arcCount E+arcCount E/2 := by
  have outSupport := outgoing_support E loops
  have inSupport := incoming_support E
  have outCapacity := sink_capacity E loops sinks
  have inCapacity := source_capacity E sources
  constructor <;> omega

theorem live_rectangle {n : Nat} (E : Graph (Fin n)) :
    score E≤card (LiveOut E)*card (LiveIn E) := by
  have bound := arcs_mono (E:=Indirect E) (F:=fun s t => LiveOut E s ∧ LiveIn E t)
    (fun s t pair => ⟨⟨t,pair⟩,⟨s,pair⟩⟩)
  rw [rectangle_count] at bound
  exact bound

theorem bound_nine {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (regularity : ∀ x, (0<outdegree E x ∧ 0<indegree E x) ∨ outdegree E x+indegree E x=2)
    (large : arcCount E+arcCount E/2<n+8) : score E≤9 := by
  have sinks (x) (zero : outdegree E x=0) : indegree E x=2 := by
    rcases regularity x with positive|two <;> omega
  have sources (x) (zero : indegree E x=0) : outdegree E x=2 := by
    rcases regularity x with positive|two <;> omega
  have counts := live_card_bound E loops sinks sources
  have a : card (LiveOut E)≤3 := by omega
  have b : card (LiveIn E)≤3 := by omega
  exact Nat.le_trans (live_rectangle E) (Nat.mul_le_mul a b)

theorem twelve {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=12) (large : 11≤n)
    (regularity : ∀ x, (0<outdegree E x ∧ 0<indegree E x) ∨ outdegree E x+indegree E x=2) :
    score E≤9 := by
  apply bound_nine E loops regularity
  rw [budget]
  omega

theorem thirteen {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=13) (large : 12≤n)
    (regularity : ∀ x, (0<outdegree E x ∧ 0<indegree E x) ∨ outdegree E x+indegree E x=2) :
    score E≤9 := by
  apply bound_nine E loops regularity
  rw [budget]
  omega

#print axioms live_card_bound
#print axioms twelve
#print axioms thirteen
end Delivery.SmallBudgetHighSupport
