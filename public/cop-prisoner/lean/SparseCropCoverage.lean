import Std

/-! Canonical six-type removals need only 81 local hole patterns. The crop
positions are 0..12, corresponding to columns -6..6 around its center.
This is an unbounded coverage theorem, not a replay of local game ranks. -/
namespace Delivery.SparseCropCoverage

def Present (k r c x : Nat) : Prop :=
  ∃ i : Fin 5, i.val<r ∧ (c+x)%k=3*i.val
instance (k r c x : Nat) : Decidable (Present k r c x) :=
  inferInstanceAs (Decidable (∃ _i : Fin 5, _ ∧ _))

def crop (k r c : Nat) : List Nat := (List.range 13).filter fun x => decide (Present k r c x)

theorem crop_congr {k r c k' r' c' : Nat}
    (same : ∀ x, x<13 → (Present k r c x ↔ Present k' r' c' x)) :
    crop k r c=crop k' r' c' := by
  apply List.filter_congr
  intro x member
  exact decide_eq_decide.mpr (same x (List.mem_range.mp member))

/-- A crop of a sufficiently long circumference is already represented at
circumference25, or is the empty pattern. Its only possible wrap crossing is
separated from the entire hole block {0,3,...,12}. -/
theorem large_representative (k r c : Nat) (large : 25 ≤ k) (holes : r ≤ 5) (base : c<k) :
    ∃ r' c', r' ≤ 5 ∧ c'<25 ∧ crop k r c=crop 25 r' c' := by
  by_cases early : c≤12
  · refine ⟨r,c,holes,by omega,?_⟩
    apply crop_congr
    intro x small
    simp only [Present,Nat.mod_eq_of_lt (show c+x<k by omega),
      Nat.mod_eq_of_lt (show c+x<25 by omega)]
  let d := k-c
  have distance : c+d=k := by dsimp [d]; omega
  by_cases near : d≤12
  · refine ⟨r,25-d,holes,by omega,?_⟩
    apply crop_congr
    intro x small
    have same (i : Fin 5) : ((c+x)%k=3*i.val) ↔ (((25-d)+x)%25=3*i.val) := by
      have hi := i.isLt
      by_cases before : x<d
      · rw [Nat.mod_eq_of_lt (show c+x<k by omega),
          Nat.mod_eq_of_lt (show 25-d+x<25 by omega)]
        constructor <;> intro h <;> omega
      · rw [Nat.mod_eq_sub_mod (show k≤c+x by omega),
          Nat.mod_eq_sub_mod (show 25≤25-d+x by omega)]
        rw [Nat.mod_eq_of_lt (show c+x-k<k by omega),
          Nat.mod_eq_of_lt (show 25-d+x-25<25 by omega)]
        have equal : c+x-k=25-d+x-25 := by omega
        rw [equal]
    simp only [Present,same]
  · refine ⟨0,0,by decide,by decide,?_⟩
    apply crop_congr
    intro x small
    constructor
    · rintro ⟨i,_,hit⟩
      have hi := i.isLt
      rw [Nat.mod_eq_of_lt (show c+x<k by omega)] at hit
      omega
    · rintro ⟨i,impossible,_⟩
      omega

-- The explicit catalog is filled from all k15..25 crops and kernel checked.
def catalog : List (List Nat) := [
  [],
  [0],
  [0,3],
  [0,3,6],
  [0,3,6,9],
  [0,3,6,9,12],
  [0,3,6,10],
  [0,3,6,11],
  [0,3,6,12],
  [0,3,7,10],
  [0,3,8,11],
  [0,3,9,12],
  [0,3,10],
  [0,3,11],
  [0,3,12],
  [0,4,7,10],
  [0,5,8,11],
  [0,6,9,12],
  [0,7,10],
  [0,8,11],
  [0,9,12],
  [0,10],
  [0,11],
  [0,12],
  [1],
  [1,4],
  [1,4,7],
  [1,4,7,10],
  [1,4,7,11],
  [1,4,7,12],
  [1,4,8,11],
  [1,4,9,12],
  [1,4,10],
  [1,4,11],
  [1,4,12],
  [1,5,8,11],
  [1,6,9,12],
  [1,7,10],
  [1,8,11],
  [1,9,12],
  [1,10],
  [1,11],
  [1,12],
  [2],
  [2,5],
  [2,5,8],
  [2,5,8,11],
  [2,5,8,12],
  [2,5,9,12],
  [2,5,10],
  [2,5,11],
  [2,5,12],
  [2,6,9,12],
  [2,7,10],
  [2,8,11],
  [2,9,12],
  [2,10],
  [2,11],
  [2,12],
  [3],
  [3,6],
  [3,6,9],
  [3,6,9,12],
  [4],
  [4,7],
  [4,7,10],
  [5],
  [5,8],
  [5,8,11],
  [6],
  [6,9],
  [6,9,12],
  [7],
  [7,10],
  [8],
  [8,11],
  [9],
  [9,12],
  [10],
  [11],
  [12]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bounded_coverage : ∀ k : Fin 26, 15 ≤ k.val →
    ∀ r : Fin 6, ∀ c : Fin 26, c.val<k.val → crop k.val r.val c.val ∈ catalog := by
  decide +kernel

/-- All circumference and residue parameters of the canonical constructor
are covered. This replaces the stronger arbitrary-hole spacing enumeration. -/
theorem coverage (k r c : Nat) (large : 15 ≤ k) (holes : r ≤ 5) (base : c<k) :
    crop k r c ∈ catalog := by
  by_cases small : k≤25
  · exact bounded_coverage ⟨k,by omega⟩ large ⟨r,by omega⟩ ⟨c,by omega⟩ base
  · obtain ⟨r',c',hr,hc,same⟩ := large_representative k r c (by omega) holes base
    rw [same]
    exact bounded_coverage ⟨25,by decide⟩ (by decide) ⟨r',by omega⟩ ⟨c',by omega⟩ hc

theorem pattern_count : catalog.length=81 := by decide +kernel
theorem patterns_distinct : catalog.Nodup := by decide +kernel

/-- Six recipient objectives and one transfer objective, except that the
type-four recipient is absent when the central position6 is a hole. -/
theorem objective_count : (catalog.map fun p => if 6 ∈ p then 6 else 7).sum=552 := by
  decide +kernel

#print axioms coverage
#print axioms objective_count
end Delivery.SparseCropCoverage
