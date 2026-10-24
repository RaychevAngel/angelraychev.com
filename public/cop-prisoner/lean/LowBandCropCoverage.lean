import Std

/-! Canonical low-band removals need only 101 local hole patterns. The crop
positions are 0..16, corresponding to columns -8..8 around its center.
This is an unbounded coverage theorem, not a replay of local game ranks. -/
namespace Delivery.LowBandCropCoverage

def Present (k r c x : Nat) : Prop :=
  ∃ i : Fin 5, i.val<r ∧ (c+x)%k=3*i.val
instance (k r c x : Nat) : Decidable (Present k r c x) :=
  inferInstanceAs (Decidable (∃ _i : Fin 5, _ ∧ _))

def crop (k r c : Nat) : List Nat := (List.range 17).filter fun x => decide (Present k r c x)

theorem crop_congr {k r c k' r' c' : Nat}
    (same : ∀ x, x<17 → (Present k r c x ↔ Present k' r' c' x)) :
    crop k r c=crop k' r' c' := by
  apply List.filter_congr
  intro x member
  exact decide_eq_decide.mpr (same x (List.mem_range.mp member))

/-- A crop of a sufficiently long circumference is already represented at
circumference29, or is the empty pattern. Its only possible wrap crossing is
separated from the entire hole block {0,3,...,12}. -/
theorem large_representative (k r c : Nat) (large : 29 ≤ k) (holes : r ≤ 5) (base : c<k) :
    ∃ r' c', r' ≤ 5 ∧ c'<29 ∧ crop k r c=crop 29 r' c' := by
  by_cases early : c≤12
  · refine ⟨r,c,holes,by omega,?_⟩
    apply crop_congr
    intro x small
    simp only [Present,Nat.mod_eq_of_lt (show c+x<k by omega),
      Nat.mod_eq_of_lt (show c+x<29 by omega)]
  let d := k-c
  have distance : c+d=k := by dsimp [d]; omega
  by_cases near : d≤16
  · refine ⟨r,29-d,holes,by omega,?_⟩
    apply crop_congr
    intro x small
    have same (i : Fin 5) : ((c+x)%k=3*i.val) ↔ (((29-d)+x)%29=3*i.val) := by
      have hi := i.isLt
      by_cases before : x<d
      · rw [Nat.mod_eq_of_lt (show c+x<k by omega),
          Nat.mod_eq_of_lt (show 29-d+x<29 by omega)]
        constructor <;> intro h <;> omega
      · rw [Nat.mod_eq_sub_mod (show k≤c+x by omega),
          Nat.mod_eq_sub_mod (show 29≤29-d+x by omega)]
        rw [Nat.mod_eq_of_lt (show c+x-k<k by omega),
          Nat.mod_eq_of_lt (show 29-d+x-29<29 by omega)]
        have equal : c+x-k=29-d+x-29 := by omega
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

-- The explicit catalog is filled from all k20..29 crops and kernel checked.
def catalog : List (List Nat) := [
  [],
  [
    0
  ],
  [
    0,
    3
  ],
  [
    0,
    3,
    6
  ],
  [
    0,
    3,
    6,
    9
  ],
  [
    0,
    3,
    6,
    9,
    12
  ],
  [
    0,
    3,
    6,
    14
  ],
  [
    0,
    3,
    6,
    15
  ],
  [
    0,
    3,
    6,
    16
  ],
  [
    0,
    3,
    11,
    14
  ],
  [
    0,
    3,
    12,
    15
  ],
  [
    0,
    3,
    13,
    16
  ],
  [
    0,
    3,
    14
  ],
  [
    0,
    3,
    15
  ],
  [
    0,
    3,
    16
  ],
  [
    0,
    8,
    11,
    14
  ],
  [
    0,
    9,
    12,
    15
  ],
  [
    0,
    10,
    13,
    16
  ],
  [
    0,
    11,
    14
  ],
  [
    0,
    12,
    15
  ],
  [
    0,
    13,
    16
  ],
  [
    0,
    14
  ],
  [
    0,
    15
  ],
  [
    0,
    16
  ],
  [
    1
  ],
  [
    1,
    4
  ],
  [
    1,
    4,
    7
  ],
  [
    1,
    4,
    7,
    10
  ],
  [
    1,
    4,
    7,
    10,
    13
  ],
  [
    1,
    4,
    7,
    15
  ],
  [
    1,
    4,
    7,
    16
  ],
  [
    1,
    4,
    12,
    15
  ],
  [
    1,
    4,
    13,
    16
  ],
  [
    1,
    4,
    14
  ],
  [
    1,
    4,
    15
  ],
  [
    1,
    4,
    16
  ],
  [
    1,
    9,
    12,
    15
  ],
  [
    1,
    10,
    13,
    16
  ],
  [
    1,
    11,
    14
  ],
  [
    1,
    12,
    15
  ],
  [
    1,
    13,
    16
  ],
  [
    1,
    14
  ],
  [
    1,
    15
  ],
  [
    1,
    16
  ],
  [
    2
  ],
  [
    2,
    5
  ],
  [
    2,
    5,
    8
  ],
  [
    2,
    5,
    8,
    11
  ],
  [
    2,
    5,
    8,
    11,
    14
  ],
  [
    2,
    5,
    8,
    16
  ],
  [
    2,
    5,
    13,
    16
  ],
  [
    2,
    5,
    14
  ],
  [
    2,
    5,
    15
  ],
  [
    2,
    5,
    16
  ],
  [
    2,
    10,
    13,
    16
  ],
  [
    2,
    11,
    14
  ],
  [
    2,
    12,
    15
  ],
  [
    2,
    13,
    16
  ],
  [
    2,
    14
  ],
  [
    2,
    15
  ],
  [
    2,
    16
  ],
  [
    3
  ],
  [
    3,
    6
  ],
  [
    3,
    6,
    9
  ],
  [
    3,
    6,
    9,
    12
  ],
  [
    3,
    6,
    9,
    12,
    15
  ],
  [
    4
  ],
  [
    4,
    7
  ],
  [
    4,
    7,
    10
  ],
  [
    4,
    7,
    10,
    13
  ],
  [
    4,
    7,
    10,
    13,
    16
  ],
  [
    5
  ],
  [
    5,
    8
  ],
  [
    5,
    8,
    11
  ],
  [
    5,
    8,
    11,
    14
  ],
  [
    6
  ],
  [
    6,
    9
  ],
  [
    6,
    9,
    12
  ],
  [
    6,
    9,
    12,
    15
  ],
  [
    7
  ],
  [
    7,
    10
  ],
  [
    7,
    10,
    13
  ],
  [
    7,
    10,
    13,
    16
  ],
  [
    8
  ],
  [
    8,
    11
  ],
  [
    8,
    11,
    14
  ],
  [
    9
  ],
  [
    9,
    12
  ],
  [
    9,
    12,
    15
  ],
  [
    10
  ],
  [
    10,
    13
  ],
  [
    10,
    13,
    16
  ],
  [
    11
  ],
  [
    11,
    14
  ],
  [
    12
  ],
  [
    12,
    15
  ],
  [
    13
  ],
  [
    13,
    16
  ],
  [
    14
  ],
  [
    15
  ],
  [
    16
  ]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bounded_coverage : ∀ k : Fin 30, 20 ≤ k.val →
    ∀ r : Fin 6, ∀ c : Fin 30, c.val<k.val → crop k.val r.val c.val ∈ catalog := by
  decide +kernel

/-- All circumference and residue parameters of the canonical constructor
are covered. This replaces the stronger arbitrary-hole spacing enumeration. -/
theorem coverage (k r c : Nat) (large : 20 ≤ k) (holes : r ≤ 5) (base : c<k) :
    crop k r c ∈ catalog := by
  by_cases small : k≤29
  · exact bounded_coverage ⟨k,by omega⟩ large ⟨r,by omega⟩ ⟨c,by omega⟩ base
  · obtain ⟨r',c',hr,hc,same⟩ := large_representative k r c (by omega) holes base
    rw [same]
    exact bounded_coverage ⟨29,by decide⟩ (by decide) ⟨r',by omega⟩ ⟨c',by omega⟩ hc

theorem pattern_count : catalog.length=101 := by decide +kernel
theorem patterns_distinct : catalog.Nodup := by decide +kernel

/-- Six recipient objectives and one transfer objective, except that the
type-four recipient is absent when the central position8 is a hole. -/
theorem objective_count : (catalog.map fun p => if 8 ∈ p then 6 else 7).sum=696 := by
  decide +kernel

#print axioms coverage
#print axioms objective_count
end Delivery.LowBandCropCoverage
