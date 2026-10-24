import FourVertexClassification
import TinyOrderClassification
import GraphSupport

/-! Reduction of the exceptional five-vertex middle budgets to positive
in/out support. Removing any source or sink is controlled by the exact
four-vertex table, with its actual direction-specific deletion theorem. -/
namespace Delivery.FiveVertexReduction
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseDeletion

theorem small_order_upper {n : Nat} (order : n≤4) (E : Graph (Fin n))
    (loops : Loopless E) : score E≤FourVertexClassification.value (arcCount E) := by
  by_cases four : n=4
  · subst n
    have size := DenseCombinatorics.arcCount_add_missingCount E loops
    exact (FourVertexClassification.maximum (arcCount E) (by omega)).1 E loops rfl
  · have zero := TinyOrderClassification.score_zero (by omega) E loops
    omega

theorem isolate_order (E : Graph (Fin 5)) (v : Fin 5) :
    card (GraphSupport.Support (isolate E v))≤4 := by
  have subset : ∀x,GraphSupport.Support (isolate E v) x → x≠v := by
    intro x h
    rcases h with ⟨y,edge⟩|⟨y,edge⟩
    · exact edge.2.1
    · exact edge.2.2
  have bound := card_mono subset
  have partition := card_complement (fun x : Fin 5 => x=v)
  rw [card_singleton] at partition
  change 1+card (fun x : Fin 5 => x≠v)=5 at partition
  omega

theorem isolate_bound (E : Graph (Fin 5)) (loops : Loopless E) (v : Fin 5) :
    score (isolate E v)≤FourVertexClassification.value (arcCount (isolate E v)) := by
  have small := small_order_upper (isolate_order E v) (GraphSupport.graph (isolate E v))
    (GraphSupport.loopless _ (isolate_loopless loops v))
  rw [GraphSupport.arcCount_eq] at small
  exact Nat.le_trans (GraphSupport.score_le _ (isolate_loopless loops v)) small

theorem scalar (m d rest I J : Nat) (low : 9≤m) (degree : d≤4)
    (count : rest+d=m) (old : J≤FourVertexClassification.value rest)
    (loss : I≤J+(4-d)) (preserved : d≤1 → I≤J) :
    I≤if m≤11 then 3 else 2 := by
  have max_two : FourVertexClassification.value rest≤2 := by
    unfold FourVertexClassification.value
    split <;> (try omega)
    split <;> (try omega)
    split <;> omega
  by_cases tiny : d≤1
  · have := preserved tiny
    split <;> omega
  · by_cases early : m≤11
    · rw [if_pos early]
      by_cases two : d=2
      · have later : 7≤rest := by omega
        have one : FourVertexClassification.value rest≤1 := by
          unfold FourVertexClassification.value
          rw [if_neg (by omega),if_neg (by omega)]
          split <;> omega
        omega
      · omega
    · rw [if_neg early]
      by_cases four : d=4
      · omega
      · have later : 8<rest := by omega
        have zero : FourVertexClassification.value rest=0 := by
          simp [FourVertexClassification.value,show ¬rest≤3 by omega,
            show rest≠6 by omega,show ¬rest≤8 by omega]
        omega

theorem source_upper (E : Graph (Fin 5)) (loops : Loopless E)
    (low : 9≤arcCount E) (v : Fin 5) (source : ∀x,¬E x v) :
    score E≤if arcCount E≤11 then 3 else 2 := by
  have deletion := source_deletion E loops v source
  have degree := row_nonadjacent_bound E loops v
  exact scalar (arcCount E) (outdegree E v) (arcCount (isolate E v))
    (score E) (score (isolate E v)) low (by omega) deletion.1
    (isolate_bound E loops v) deletion.2.2.1 deletion.2.2.2

theorem sink_upper (E : Graph (Fin 5)) (loops : Loopless E)
    (low : 9≤arcCount E) (v : Fin 5) (sink : ∀x,¬E v x) :
    score E≤if arcCount E≤11 then 3 else 2 := by
  have deletion := sink_deletion E loops v sink
  have degree := column_nonadjacent_bound E loops v
  exact scalar (arcCount E) (indegree E v) (arcCount (isolate E v))
    (score E) (score (isolate E v)) low (by omega) deletion.1
    (isolate_bound E loops v) deletion.2.2.1 deletion.2.2.2

theorem upper_with_positive
    (positive : ∀ E : Graph (Fin 5),Loopless E →
      (9≤arcCount E ∧ arcCount E≤14) →
      (∀x,1≤outdegree E x) → (∀x,1≤indegree E x) →
      score E≤if arcCount E≤11 then 3 else 2)
    (E : Graph (Fin 5)) (loops : Loopless E)
    (budget : 9≤arcCount E ∧ arcCount E≤14) :
    score E≤if arcCount E≤11 then 3 else 2 := by
  by_cases small : score E≤if arcCount E≤11 then 3 else 2
  · exact small
  · apply positive E loops budget
    · intro x
      by_cases zero : outdegree E x=0
      · exact False.elim (small (sink_upper E loops budget.1 x (card_eq_zero.mp zero)))
      · omega
    · intro x
      by_cases zero : indegree E x=0
      · exact False.elim (small (source_upper E loops budget.1 x (card_eq_zero.mp zero)))
      · omega

#print axioms source_upper
#print axioms sink_upper
#print axioms upper_with_positive
end Delivery.FiveVertexReduction
