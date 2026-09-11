import InitialTwoClassification
import RectangleClassification
import CornerCertificateLarge

namespace PolyominoFormal

theorem gun_exact_bs {a : Int} (ha : 4≤a) : ExactBS a := by
  by_cases four : a=4
  · subst a
    exact p4_exact_bs
  by_cases five : a=5
  · subst a
    exact p5_exact_bs
  exact exact_bs_of_local ha (CornerCertificate.large_local a (by omega))

/-- The complete threshold statement for every nonnegative gun parameter. -/
theorem classify_gun (n : Nat) :
    if n≤3 then ExactRectangle n 1 1 0 else ExactBS n := by
  split
  · rename_i small
    have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact p0_exact_rectangle
    · exact p1_exact_rectangle
    · exact p2_exact_rectangle
    · exact p3_exact_rectangle
  · rename_i large
    exact gun_exact_bs (by omega)

theorem gun_rectangle_iff (n : Nat) : RectangleTileable n 1 1 0 ↔ n≤3 := by
  by_cases small : n≤3
  · have result := classify_gun n
    simp only [small,if_true] at result
    exact ⟨fun _ => small,fun _ => result.rectangle⟩
  · have result := gun_exact_bs (by omega : (4:Int)≤n)
    exact ⟨fun h => False.elim (result.no_rectangle h),fun h => False.elim (small h)⟩

theorem gun_half_strip_iff (n : Nat) : HalfStripTileable n 1 1 0 ↔ n≤3 := by
  by_cases small : n≤3
  · have result := classify_gun n
    simp only [small,if_true] at result
    exact ⟨fun _ => small,fun _ => result.half_strip⟩
  · have result := gun_exact_bs (by omega : (4:Int)≤n)
    exact ⟨fun h => False.elim (result.no_half_strip h),fun h => False.elim (small h)⟩

theorem gun_rep_iff (n : Nat) : RepTileable n 1 1 0 ↔ n≤3 := by
  by_cases small : n≤3
  · have result := classify_gun n
    simp only [small,if_true] at result
    exact ⟨fun _ => small,fun _ => result.rep⟩
  · have result := gun_exact_bs (by omega : (4:Int)≤n)
    exact ⟨fun h => False.elim (result.no_rep h),fun h => False.elim (small h)⟩

#print axioms classify_gun
#print axioms gun_half_strip_iff
#print axioms gun_rep_iff
end PolyominoFormal
