import ProfileAssembly
import THalfPlaneUnit
import HPFinite
import TPlaneLong
import TPlaneTwoLong

namespace PolyominoFormal

theorem t_no_halfplane {a b c : Int} (ha : c≤a) (hc : 1≤c) (hb : 2≤b) :
    ¬Tiles a b c 0 HalfPlane := by
  by_cases unit : c=1
  · subst c
    by_cases long : a<b
    · exact THalfPlane.no_halfplane_unit_long ha long
    · by_cases large : 7≤a
      · exact THalfPlaneUnit.no_halfplane_unit_large large hb
      · exact THalfPlaneFinite.finite_no_half_plane a b ⟨hb,by omega,by omega⟩
  · exact THalfPlane.no_halfplane_two ha (by omega) hb

theorem t_halfplane_iff {a b c : Int} (ha : c≤a) (hb : 1≤b) (hc : 1≤c) :
    Tiles a b c 0 HalfPlane ↔ b=1 := by
  constructor
  · intro tiled
    apply Classical.byContradiction
    intro other
    exact t_no_halfplane ha hc (by omega) tiled
  · rintro rfl
    exact PositiveHierarchy.t_unit_stem_halfplane a c (by omega) hc

theorem t_plane_iff {a b c : Int} (ha : c≤a) (hb : 1≤b) (hc : 1≤c) :
    Tiles a b c 0 Plane ↔ b≤2 ∨ c=1 ∨ (c=2∧b=a+3) := by
  constructor
  · intro tiled
    apply Classical.byContradiction
    intro other
    have b3 : 3≤b := by omega
    have c2 : 2≤c := by omega
    by_cases eq : c=2
    · subst c
      by_cases short : b<a+3
      · exact short_stem_two_arm_no_plane a b ha b3 short tiled
      · exact TPlaneTwoLong.no_plane ha (by omega) tiled
    · exact TPlaneLong.three_arms_no_plane ha (by omega) b3 tiled
  · intro h
    apply PositiveTheorems.t_plane_of_conditions a b c ha hb hc
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- Complete capability profile of every normalized genuine T. -/
theorem normalized_T_classified (a b c : Nat) (hc : 1≤c) (ha : c≤a) (hb : 1≤b) :
    Classified a b c 0 (classifyT a b c) := by
  by_cases unitStem : b=1
  · subst b
    by_cases unitSide : c=1
    · subst c
      simpa only [Int.natCast_one,classifyT,if_pos] using gun_classified a
    · have h := (unit_stem_exact_strip a c (by omega) (by omega)).classified
      simpa only [Int.natCast_one,classifyT,if_pos,if_neg unitSide] using h
  · have noHP := t_no_halfplane (a:=(a : Int)) (b:=(b : Int)) (c:=(c : Int))
      (by omega) (by omega) (by omega)
    have positive := t_plane_iff (a:=(a : Int)) (b:=(b : Int)) (c:=(c : Int))
      (by omega) (by omega) (by omega)
    have result := no_halfplane_zero_south_profile (by omega : 0≤(a : Int))
      (by omega : 0≤(b : Int)) (by omega : 0≤(c : Int)) noHP positive
    have condition : ((b : Int)≤2 ∨ (c : Int)=1 ∨ ((c : Int)=2∧(b : Int)=(a : Int)+3))=
        (b≤2 ∨ c=1 ∨ (c=2∧b=a+3)) := propext (by omega)
    simp only [condition] at result
    simpa only [classifyT,if_neg unitStem] using result

#print axioms t_halfplane_iff
#print axioms t_plane_iff
#print axioms normalized_T_classified
end PolyominoFormal
