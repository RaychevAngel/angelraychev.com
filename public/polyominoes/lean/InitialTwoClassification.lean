import CornerCertificateFour
import CornerCertificateFive
import HalfStripObstruction
import RectangleHierarchy
import PositiveHierarchy
import RepObstruction
import RepConvention

namespace PolyominoFormal

/-- The full BS capability profile, including the independent exclusion
    of lattice rep-tilings. Widths in every capability are existential. -/
structure ExactBS (a : Int) : Prop where
  no_rectangle : ¬RectangleTileable a 1 1 0
  no_half_strip : ¬HalfStripTileable a 1 1 0
  bent_strip : BentStripTileable a 1 1 0
  quadrant : Tiles a 1 1 0 Quadrant
  strip : StripTileable a 1 1 0
  half_plane : Tiles a 1 1 0 HalfPlane
  plane : Tiles a 1 1 0 Plane
  no_rep : ¬RepTileable a 1 1 0

theorem exact_bs_of_local {a : Int} (ha : 4≤a)
    (replay : HalfStripObstruction.LocalTheorem a) : ExactBS a := by
  have noHS := HalfStripObstruction.no_half_strip replay
  have hBS := PositiveConstructions.bent_tileable a (by omega)
  have hS := PositiveConstructions.strip_tileable a 1 (by omega) (by omega)
  have repReplay : RepObstruction.Replay a := by
    intro world h kind B copies separate clean closed bounded cover ceiling
    exact replay world h kind B copies separate cover ceiling closed bounded clean
  exact ⟨(fun hR => noHS (rectangle_implies_half_strip hR)),noHS,hBS,
    PositiveHierarchy.bent_tiles_quadrant hBS,hS,
    PositiveHierarchy.strip_tiles_halfplane hS,PositiveHierarchy.strip_tiles_plane hS,
    no_rep_of_replay ha repReplay⟩

theorem p4_exact_bs : ExactBS 4 :=
  exact_bs_of_local (by decide) CornerCertificate.four_local

theorem p5_exact_bs : ExactBS 5 :=
  exact_bs_of_local (by decide) CornerCertificate.five_local

#print axioms p4_exact_bs
#print axioms p5_exact_bs

end PolyominoFormal
