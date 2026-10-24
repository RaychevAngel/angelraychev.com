import SmallDenseEnvelopes
import PrefixEnvelope

/-! Exact budgets for the six certified arbitrary-subset envelopes. -/
namespace Delivery.SmallDenseEnvelopeMaxima
open FiniteGame Extremal

theorem inclusion : ∀ i : Fin 6, RobustTwoMove.Subgraph
    (SmallDenseEnvelopes.lower (i.val+16)) (SmallDenseEnvelopes.upper (i.val+16)) := by
  unfold RobustTwoMove.Subgraph
  decide +kernel

theorem maximum (i : Fin 6) (m : Nat)
    (low : (i.val+16)*(i.val+16-1)-3*(i.val+16) ≤ m)
    (high : m ≤ (i.val+16)*(i.val+16-1)-2*(i.val+16)) :
    IsMaximum (i.val+16) m ((i.val+16)*(i.val+16-1)-m) := by
  have counts := SmallDenseEnvelopes.exact_endpoint_counts i
  have lo : arcCount (SmallDenseEnvelopes.lower (i.val+16)) =
      (i.val+16)*(i.val+16-1)-3*(i.val+16) := by
    rw [Extremal.arcCount_eq]
    exact counts.1
  have hi : arcCount (SmallDenseEnvelopes.upper (i.val+16)) =
      (i.val+16)*(i.val+16-1)-2*(i.val+16) := by
    rw [Extremal.arcCount_eq]
    exact counts.2
  exact PrefixEnvelope.maximum_at _ _ (inclusion i)
    (fun s edge => edge.1 rfl) (SmallDenseEnvelopes.witnesses i)
    (lo ▸ low) (hi ▸ high)

#print axioms maximum
end Delivery.SmallDenseEnvelopeMaxima
