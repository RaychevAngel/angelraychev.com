import PrefixEnvelope

/-! Exact-budget prefix constructions for any delivery envelope, regardless
of its number of moves or whether its ranks depend on both positions. -/
namespace Delivery.GuaranteedPrefix
open FiniteGame Extremal RobustTwoMove DenseCombinatorics

def Delivers {n : Nat} (L U : Graph (Fin n)) : Prop :=
  ∀ G : Graph (Fin n), Subgraph L G → Subgraph G U → ∀ s t, Guaranteed G s t

theorem score_count {n : Nat} (L U : Graph (Fin n)) (q : Nat)
    (subset : Subgraph L U) (noLoops : Loopless U) (delivery : Delivers L U)
    (range : q ≤ (PrefixEnvelope.optional L U).length) :
    score (PrefixEnvelope.graph L U q) = n*(n-1)-(arcCount L+q) := by
  have guarantees := delivery _ (PrefixEnvelope.lower L U q) (PrefixEnvelope.upper L U q subset)
  have all := score_eq_missing _ (fun s t _ _ => guarantees s t)
  have partition := arcCount_add_missingCount _ (PrefixEnvelope.loopless L U q subset noLoops)
  rw [PrefixEnvelope.arc_count L U q range] at partition
  omega

theorem maximum {n m : Nat} (L U : Graph (Fin n))
    (subset : Subgraph L U) (noLoops : Loopless U) (delivery : Delivers L U)
    (low : arcCount L ≤ m) (high : m ≤ arcCount U) :
    IsMaximum n m (n*(n-1)-m) := by
  have length := PrefixEnvelope.optional_length L U subset
  have range : m-arcCount L ≤ (PrefixEnvelope.optional L U).length := by omega
  have exactBudget : arcCount L+(m-arcCount L) = m := by omega
  constructor
  · intro E loops arrows
    have partition := arcCount_add_missingCount E loops
    have bound := score_le_missing E
    omega
  · refine ⟨PrefixEnvelope.graph L U (m-arcCount L),
      PrefixEnvelope.loopless L U _ subset noLoops,?_,?_⟩
    · rw [PrefixEnvelope.arc_count L U _ range,exactBudget]
    · rw [score_count L U _ subset noLoops delivery range,exactBudget]

#print axioms score_count
#print axioms maximum
end Delivery.GuaranteedPrefix
