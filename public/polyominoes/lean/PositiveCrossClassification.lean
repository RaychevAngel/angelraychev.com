import PositiveTheorems
import CoreBoundaryObstructions

namespace PolyominoFormal

/-- Every capability in the hierarchy for every four-positive-arm tuple.
    Rep-tiling uses the explicitly defined integer-cell enlargement. -/
theorem classify_positive_cross (a b c d : Int)
    (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) :
    (Tiles a b c d Plane ↔ ((a=1 ∧ c=1) ∨ (b=1 ∧ d=1))) ∧
    (¬Tiles a b c d HalfPlane) ∧
    (¬StripTileable a b c d) ∧
    (¬Tiles a b c d Quadrant) ∧
    (¬BentStripTileable a b c d) ∧
    (¬HalfStripTileable a b c d) ∧
    (¬RectangleTileable a b c d) ∧
    (∀ k : Int, 2≤k → ¬Tiles a b c d (CoreBoundaryObstructions.ScaledCross a b c d k)) := by
  exact ⟨PositiveTheorems.cross_plane_iff a b c d ha hb hc hd,
    CoreBoundaryObstructions.positive_cross_no_halfplane ha hb hc hd,
    CoreBoundaryObstructions.positive_cross_no_strip ha hb hc hd,
    CoreBoundaryObstructions.positive_cross_no_quadrant ha hb hc hd,
    CoreBoundaryObstructions.positive_cross_no_bentstrip ha hb hc hd,
    CoreBoundaryObstructions.positive_cross_no_halfstrip ha hb hc hd,
    CoreBoundaryObstructions.positive_cross_no_rectangle ha hb hc hd,
    fun k hk => CoreBoundaryObstructions.positive_cross_no_scaled_copy ha hb hc hd hk⟩

#print axioms classify_positive_cross
end PolyominoFormal
