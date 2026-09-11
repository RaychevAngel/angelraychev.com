import LHalfPlaneUnequalAssembly
import LHalfPlaneShortbarFinal
import LHalfPlaneAlternatingOuter
import LHalfPlaneMixedMotif

namespace PolyominoFormal.LHalfPlaneUnequal

/-- No unequal L with shorter arm at least three and longer arm at least five
tiles an ordinary infinite half-plane, with every D4 orientation allowed. -/
theorem no_halfplane (a b : Int) (ha : 5≤a) (hb : 3≤b) (hab : b<a) :
    ¬Tiles a b 0 0 HalfPlane := by
  apply no_halfplane_from_inputs ha hb hab
    (LHalfPlaneShortbarAssembly.no_shortbars ha hb hab)
    (LHalfPlaneAlternating.delta_two ha hb hab)
  intro T delta nonexception h0 h1 h2 h3 hU hS
  exact LHalfPlaneMixedMotif.mixed_impossible ha hb hab delta nonexception
    T h0 h1 h2 h3 hU hS

#print axioms no_halfplane
end PolyominoFormal.LHalfPlaneUnequal
