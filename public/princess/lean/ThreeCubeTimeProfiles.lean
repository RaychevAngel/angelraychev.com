import ThreeCubeLower
import FiniteSubsetProfiles

/-! Exhaustive same-parity isoperimetric certificates, checked by Lean's
kernel over only 2^14 + 2^13 supports. Neighbor bitmasks are independently
proved equivalent to the coordinate definition of physical adjacency. -/
namespace Princess.ThreeCubeTimeProfiles
open Princess.ThreeCubeTrap Princess.ThreeCubeLower
open Princess.LadderCardinality Princess.CaptureRecurrence
open Princess.FiniteSubsetProfiles

def neighborMask (v : Room) : Nat := (885262202045999447621934297017895758051286593911679830123152831752099397471579708479521788727544551298105553707413063230347961857633201947961436918615312259287587369086756471969609800269075823954433966004819773209182730 >>> (27 * v.val)) &&& 134217727

def rooms (p : Nat) : List Room := if p % 2 = 0 then [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26] else [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25]

def profile (p k : Nat) : Nat :=
  ((if p % 2 = 0 then 999197459644708144 else 67252577022604864) >>> (4 * k)) &&& 15

theorem mask_adjacency : ∀ u v : Room,
    (neighborMask u).testBit v.val = true ↔ adj u v := by decide

theorem rooms_membership : ∀ p : Fin 2, ∀ v : Room,
    v ∈ rooms p.val ↔ color v = p.val := by decide

theorem rooms_nodup : ∀ p : Fin 2, (rooms p.val).Nodup := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem even_profile_checked : checkAll 27 neighborMask (profile 0) (rooms 0) 0 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem odd_profile_checked : checkAll 27 neighborMask (profile 1) (rooms 1) 0 0 = true := by
  decide +kernel

end Princess.ThreeCubeTimeProfiles
#print axioms Princess.ThreeCubeTimeProfiles.even_profile_checked
#print axioms Princess.ThreeCubeTimeProfiles.odd_profile_checked
