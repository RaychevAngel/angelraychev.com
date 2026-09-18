import VertexBound
import TwelveVertexCertificate
import ElevenVertexDense

/-! Existing checked graphs connected to the general score and maximum
specification. These are individual exact cells, not the full classification. -/
namespace Delivery.ExtremalExamples
open FiniteGame Extremal

theorem twelve_score : score TwelveVertex.edge = 108 := by
  have allGuaranteed : ∀ s t : Fin 12, s ≠ t → ¬ TwelveVertex.edge s t →
      Guaranteed TwelveVertex.edge s t := by
    intro s t _ _ c initial
    exact ⟨_, rankCertificate_winning (TwelveVertex.certificate t) s c (Ne.symm initial)⟩
  rw [score_eq_missing TwelveVertex.edge allGuaranteed]
  rw [missingCount_eq]
  exact TwelveVertex.indirect_count

theorem twelve_loopless : Loopless TwelveVertex.edge := by
  unfold Loopless
  decide +kernel

theorem twelve_arcs : arcCount TwelveVertex.edge = 24 := by
  rw [arcCount_eq]
  exact TwelveVertex.arc_count

/-- The sparse endpoint at (12,24), including the unrestricted upper bound. -/
theorem maximum_twelve_twentyfour : IsMaximum 12 24 108 := by
  constructor
  · intro E loopless _
    exact VertexBound.vertex_upper E loopless
  · exact ⟨TwelveVertex.edge, twelve_loopless, twelve_arcs, twelve_score⟩

theorem eleven_score : score ElevenVertexDense.edge = 22 := by
  have allGuaranteed : ∀ s t : Fin 11, s ≠ t → ¬ ElevenVertexDense.edge s t →
      Guaranteed ElevenVertexDense.edge s t := by
    intro s t _ _
    exact universal_guaranteed
      (RobustTwoMove.envelope_universal (fun _ _ h => h) (fun _ _ h => h)
        ElevenVertexDense.witnesses s t)
  rw [score_eq_missing ElevenVertexDense.edge allGuaranteed]
  rw [missingCount_eq]
  exact ElevenVertexDense.indirect_count

/- The dense graph is now connected to the score definition; an exact maximum
at its arrow budget is not asserted by this module. -/
theorem eleven_loopless : Loopless ElevenVertexDense.edge := by
  intro v h
  exact h.1 rfl

#print axioms twelve_score
#print axioms maximum_twelve_twentyfour
#print axioms eleven_score
end Delivery.ExtremalExamples
