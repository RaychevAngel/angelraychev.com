import FiniteExclusionThirtyNineHamiltonian2x0
import FiniteExclusionThirtyNineHamiltonian2x3
import FiniteExclusionThirtyNineHamiltonian2x4
import FiniteExclusionThirtyNineHamiltonian2x5
import FiniteExclusionThirtyNineHamiltonian2x6
import FiniteExclusionThirtyNineHamiltonian2x7
import FiniteExclusionThirtyNineHamiltonian2x8
import FiniteExclusionThirtyNineHamiltonian3x0
import FiniteExclusionThirtyNineHamiltonian3x4
import FiniteExclusionThirtyNineHamiltonian3x5
import FiniteExclusionThirtyNineHamiltonian3x6
import FiniteExclusionThirtyNineHamiltonian3x7
import FiniteExclusionThirtyNineHamiltonian3x8
import FiniteExclusionThirtyNineHamiltonian4x0
import FiniteExclusionThirtyNineHamiltonian4x3
import FiniteExclusionThirtyNineHamiltonian4x5
import FiniteExclusionThirtyNineHamiltonian4x6
import FiniteExclusionThirtyNineHamiltonian4x7
import FiniteExclusionThirtyNineHamiltonian4x8
import FiniteExclusionThirtyNineHamiltonian5x0
import FiniteExclusionThirtyNineHamiltonian5x3
import FiniteExclusionThirtyNineHamiltonian5x4
import FiniteExclusionThirtyNineHamiltonian5x6
import FiniteExclusionThirtyNineHamiltonian5x7
import FiniteExclusionThirtyNineHamiltonian5x8
import FiniteExclusionThirtyNineHamiltonian6x0
import FiniteExclusionThirtyNineHamiltonian6x3
import FiniteExclusionThirtyNineHamiltonian6x4
import FiniteExclusionThirtyNineHamiltonian6x5
import FiniteExclusionThirtyNineHamiltonian6x7
import FiniteExclusionThirtyNineHamiltonian6x8
import FiniteExclusionThirtyNineHamiltonian7x0
import FiniteExclusionThirtyNineHamiltonian7x3
import FiniteExclusionThirtyNineHamiltonian7x4
import FiniteExclusionThirtyNineHamiltonian7x5
import FiniteExclusionThirtyNineHamiltonian7x6
import FiniteExclusionThirtyNineHamiltonian7x8
import FiniteExclusionThirtyNineHamiltonian8x0
import FiniteExclusionThirtyNineHamiltonian8x3
import FiniteExclusionThirtyNineHamiltonian8x4
import FiniteExclusionThirtyNineHamiltonian8x5
import FiniteExclusionThirtyNineHamiltonian8x6
import FiniteExclusionThirtyNineHamiltonian8x7
namespace Delivery.FiniteExclusion.Thirty9Minimum
open RotationBounds Extremal
theorem piece_2 : UpperPrefix a [2] 30 :=
  branch_upper a [2] 30 (by decide) (fin9_cases _
    piece_2_0
    (invalid_upper a [2,1] 30 (by decide +kernel))
    (invalid_upper a [2,2] 30 (by decide +kernel))
    piece_2_3
    piece_2_4
    piece_2_5
    piece_2_6
    piece_2_7
    piece_2_8)

theorem piece_3 : UpperPrefix a [3] 30 :=
  branch_upper a [3] 30 (by decide) (fin9_cases _
    piece_3_0
    (invalid_upper a [3,1] 30 (by decide +kernel))
    (invalid_upper a [3,2] 30 (by decide +kernel))
    (invalid_upper a [3,3] 30 (by decide +kernel))
    piece_3_4
    piece_3_5
    piece_3_6
    piece_3_7
    piece_3_8)

theorem piece_4 : UpperPrefix a [4] 30 :=
  branch_upper a [4] 30 (by decide) (fin9_cases _
    piece_4_0
    (invalid_upper a [4,1] 30 (by decide +kernel))
    (invalid_upper a [4,2] 30 (by decide +kernel))
    piece_4_3
    (invalid_upper a [4,4] 30 (by decide +kernel))
    piece_4_5
    piece_4_6
    piece_4_7
    piece_4_8)

theorem piece_5 : UpperPrefix a [5] 30 :=
  branch_upper a [5] 30 (by decide) (fin9_cases _
    piece_5_0
    (invalid_upper a [5,1] 30 (by decide +kernel))
    (invalid_upper a [5,2] 30 (by decide +kernel))
    piece_5_3
    piece_5_4
    (invalid_upper a [5,5] 30 (by decide +kernel))
    piece_5_6
    piece_5_7
    piece_5_8)

theorem piece_6 : UpperPrefix a [6] 30 :=
  branch_upper a [6] 30 (by decide) (fin9_cases _
    piece_6_0
    (invalid_upper a [6,1] 30 (by decide +kernel))
    (invalid_upper a [6,2] 30 (by decide +kernel))
    piece_6_3
    piece_6_4
    piece_6_5
    (invalid_upper a [6,6] 30 (by decide +kernel))
    piece_6_7
    piece_6_8)

theorem piece_7 : UpperPrefix a [7] 30 :=
  branch_upper a [7] 30 (by decide) (fin9_cases _
    piece_7_0
    (invalid_upper a [7,1] 30 (by decide +kernel))
    (invalid_upper a [7,2] 30 (by decide +kernel))
    piece_7_3
    piece_7_4
    piece_7_5
    piece_7_6
    (invalid_upper a [7,7] 30 (by decide +kernel))
    piece_7_8)

theorem piece_8 : UpperPrefix a [8] 30 :=
  branch_upper a [8] 30 (by decide) (fin9_cases _
    piece_8_0
    (invalid_upper a [8,1] 30 (by decide +kernel))
    (invalid_upper a [8,2] 30 (by decide +kernel))
    piece_8_3
    piece_8_4
    piece_8_5
    piece_8_6
    piece_8_7
    (invalid_upper a [8,8] 30 (by decide +kernel)))

theorem piece_root : UpperPrefix a [] 30 :=
  branch_upper a [] 30 (by decide) (fin9_cases _
    (invalid_upper a [0] 30 (by decide +kernel))
    (invalid_upper a [1] 30 (by decide +kernel))
    piece_2
    piece_3
    piece_4
    piece_5
    piece_6
    piece_7
    piece_8)

theorem prefix_upper : UpperPrefix a [] 30 := piece_root
#print axioms prefix_upper
theorem upper (b : Assignment 9) (valid : Valid a b) : score (edgeOf a b) ≤ 30 := by
  obtain ⟨b',valid',minimum,same⟩ := HamiltonianNormalization.normalized_cover a b
    (by decide +kernel) valid
  rw [←same]
  exact prefix_upper b' valid' minimum (by intro i h; simp at h)
#print axioms upper
end Delivery.FiniteExclusion.Thirty9Minimum
