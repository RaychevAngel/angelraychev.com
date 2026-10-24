import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0121

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23700 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 52 76 274 96 69 133 261), lower := (rows 35 138 52 76 274 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 48 104 275 96 96 128 256) }] }

theorem u23700 : Upper (D 6) (R 6) [34,136,48,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23701 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 52 76 276 33 67 195 323), lower := (rows 35 138 52 76 276 33 64 128 256), losses := [] }

theorem u23701 : Upper (D 6) (R 6) [34,136,48,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23702 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 76 276 34 65 193 321), lower := (rows 35 138 52 76 276 34 64 128 256), losses := [] }

theorem u23702 : Upper (D 6) (R 6) [34,136,48,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23703 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 52 76 276 96 67 131 259), lower := (rows 35 138 52 76 276 96 64 128 256), losses := [] }

theorem u23703 : Upper (D 6) (R 6) [34,136,48,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23704 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 138 52 76 336 33 71 135 263), lower := (rows 35 138 52 76 336 33 64 128 256), losses := [] }

theorem u23704 : Upper (D 6) (R 6) [34,136,48,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23705 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 76 336 34 69 133 261), lower := (rows 35 138 52 76 336 34 64 128 256), losses := [] }

theorem u23705 : Upper (D 6) (R 6) [34,136,48,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23706 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 138 52 76 336 36 67 131 259), lower := (rows 35 138 52 76 336 36 64 128 256), losses := [] }

theorem u23706 : Upper (D 6) (R 6) [34,136,48,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23707 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 265 81 34 68 196 324), lower := (rows 35 138 52 265 81 34 64 128 256), losses := [] }

theorem u23707 : Upper (D 6) (R 6) [34,136,48,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23708 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 265 81 36 70 198 326), lower := (rows 35 138 52 265 81 36 64 128 256), losses := [] }

theorem u23708 : Upper (D 6) (R 6) [34,136,48,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23709 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 265 81 96 70 134 262), lower := (rows 35 138 52 265 81 96 64 128 256), losses := [] }

theorem u23709 : Upper (D 6) (R 6) [34,136,48,257,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23710 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 52 265 82 33 68 196 324), lower := (rows 35 138 52 265 82 33 64 128 256), losses := [] }

theorem u23710 : Upper (D 6) (R 6) [34,136,48,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23711 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 52 265 82 36 69 197 325), lower := (rows 35 138 52 265 82 36 64 128 256), losses := [] }

theorem u23711 : Upper (D 6) (R 6) [34,136,48,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23712 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 265 82 96 69 133 261), lower := (rows 35 138 52 265 82 96 64 128 256), losses := [] }

theorem u23712 : Upper (D 6) (R 6) [34,136,48,257,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23713 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 52 265 84 33 70 198 326), lower := (rows 35 138 52 265 84 33 64 128 256), losses := [] }

theorem u23713 : Upper (D 6) (R 6) [34,136,48,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23714 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 265 84 34 69 197 325), lower := (rows 35 138 52 265 84 34 64 128 256), losses := [] }

theorem u23714 : Upper (D 6) (R 6) [34,136,48,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23715 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 52 265 84 36 67 195 323), lower := (rows 35 138 52 265 84 36 64 128 256), losses := [] }

theorem u23715 : Upper (D 6) (R 6) [34,136,48,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23716 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 52 265 84 96 71 135 263), lower := (rows 35 138 52 265 84 96 64 128 256), losses := [] }

theorem u23716 : Upper (D 6) (R 6) [34,136,48,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23717 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 266 81 33 68 196 324), lower := (rows 35 138 52 266 81 33 64 128 256), losses := [] }

theorem u23717 : Upper (D 6) (R 6) [34,136,48,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23718 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 52 266 81 36 69 197 325), lower := (rows 35 138 52 266 81 36 64 128 256), losses := [] }

theorem u23718 : Upper (D 6) (R 6) [34,136,48,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23719 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 266 81 96 69 133 261), lower := (rows 35 138 52 266 81 96 64 128 256), losses := [] }

theorem u23719 : Upper (D 6) (R 6) [34,136,48,258,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23720 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 52 266 84 33 69 197 325), lower := (rows 35 138 52 266 84 33 64 128 256), losses := [] }

theorem u23720 : Upper (D 6) (R 6) [34,136,48,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23721 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 52 266 84 36 65 193 321), lower := (rows 35 138 52 266 84 36 64 128 256), losses := [] }

theorem u23721 : Upper (D 6) (R 6) [34,136,48,258,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23722 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 52 266 84 96 69 133 261), lower := (rows 35 138 52 266 84 96 64 128 256), losses := [] }

theorem u23722 : Upper (D 6) (R 6) [34,136,48,258,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23723 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 268 81 33 70 198 326), lower := (rows 35 138 52 268 81 33 64 128 256), losses := [] }

theorem u23723 : Upper (D 6) (R 6) [34,136,48,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23724 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 268 81 34 69 197 325), lower := (rows 35 138 52 268 81 34 64 128 256), losses := [] }

theorem u23724 : Upper (D 6) (R 6) [34,136,48,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23725 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 268 81 36 67 195 323), lower := (rows 35 138 52 268 81 36 64 128 256), losses := [] }

theorem u23725 : Upper (D 6) (R 6) [34,136,48,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23726 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 268 81 96 71 135 263), lower := (rows 35 138 52 268 81 96 64 128 256), losses := [] }

theorem u23726 : Upper (D 6) (R 6) [34,136,48,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23727 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 138 52 268 82 33 69 197 325), lower := (rows 35 138 52 268 82 33 64 128 256), losses := [] }

theorem u23727 : Upper (D 6) (R 6) [34,136,48,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23728 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 138 52 268 82 36 65 193 321), lower := (rows 35 138 52 268 82 36 64 128 256), losses := [] }

theorem u23728 : Upper (D 6) (R 6) [34,136,48,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23729 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 268 82 96 69 133 261), lower := (rows 35 138 52 268 82 96 64 128 256), losses := [] }

theorem u23729 : Upper (D 6) (R 6) [34,136,48,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23730 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 52 268 84 33 67 195 323), lower := (rows 35 138 52 268 84 33 64 128 256), losses := [] }

theorem u23730 : Upper (D 6) (R 6) [34,136,48,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23731 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 268 84 34 65 193 321), lower := (rows 35 138 52 268 84 34 64 128 256), losses := [] }

theorem u23731 : Upper (D 6) (R 6) [34,136,48,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23732 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 52 268 84 96 67 131 259), lower := (rows 35 138 52 268 84 96 64 128 256), losses := [] }

theorem u23732 : Upper (D 6) (R 6) [34,136,48,260,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23733 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 328 81 33 70 134 262), lower := (rows 35 138 52 328 81 33 64 128 256), losses := [] }

theorem u23733 : Upper (D 6) (R 6) [34,136,48,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23734 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 328 81 34 69 133 261), lower := (rows 35 138 52 328 81 34 64 128 256), losses := [] }

theorem u23734 : Upper (D 6) (R 6) [34,136,48,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23735 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 328 81 36 71 135 263), lower := (rows 35 138 52 328 81 36 64 128 256), losses := [] }

theorem u23735 : Upper (D 6) (R 6) [34,136,48,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23736 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 138 52 328 82 33 69 133 261), lower := (rows 35 138 52 328 82 33 64 128 256), losses := [] }

theorem u23736 : Upper (D 6) (R 6) [34,136,48,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23737 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 52 328 82 36 69 133 261), lower := (rows 35 138 52 328 82 36 64 128 256), losses := [] }

theorem u23737 : Upper (D 6) (R 6) [34,136,48,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23738 : Route 9 := (fun mask => (mask,id))

def c23738 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23738 : Upper (D 6) (R 6) [34,136,48,320,68,1] 13 := by
  apply FastRouting.sound _ _ [34,136,48,320,68,1] 13 (by decide) (choices 1) [1,2,4] r23738 c23738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7284
  · exact u7285
  · exact u7286

def b23739 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 328 84 34 69 133 261), lower := (rows 35 138 52 328 84 34 64 128 256), losses := [] }

theorem u23739 : Upper (D 6) (R 6) [34,136,48,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23740 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 52 328 84 36 67 131 259), lower := (rows 35 138 52 328 84 36 64 128 256), losses := [] }

theorem u23740 : Upper (D 6) (R 6) [34,136,48,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23741 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 138 70 13 52 33 336 464 336), lower := (rows 35 138 70 13 52 33 64 128 256), losses := [] }

theorem u23741 : Upper (D 6) (R 6) [34,136,66,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23742 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 70 13 52 48 321 449 321), lower := (rows 35 138 70 13 52 48 64 128 256), losses := [] }

theorem u23742 : Upper (D 6) (R 6) [34,136,66,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23742 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23743 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 70 13 52 96 337 401 273), lower := (rows 35 138 70 13 52 96 64 128 256), losses := [] }

theorem u23743 : Upper (D 6) (R 6) [34,136,66,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23744 : Route 9 := (fun mask => (mask,id))

def c23744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23744 : Upper (D 6) (R 6) [34,136,66,5,36,256] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5,36,256] 13 (by decide) (choices 1) [1,16] r23744 c23744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7287
  · exact u7288

def b23745 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 70 13 112 33 340 404 276), lower := (rows 35 138 70 13 112 33 64 128 256), losses := [] }

theorem u23745 : Upper (D 6) (R 6) [34,136,66,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23746 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 138 70 13 112 36 337 401 273), lower := (rows 35 138 70 13 112 36 64 128 256), losses := [] }

theorem u23746 : Upper (D 6) (R 6) [34,136,66,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23747 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 70 13 112 48 325 389 261), lower := (rows 35 138 70 13 112 48 64 128 256), losses := [] }

theorem u23747 : Upper (D 6) (R 6) [34,136,66,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23747 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m23748_1 : Upper (D 6) (R 6) [34,136,66,5,96,256,1] 13 :=
  permutation_upper _ _ _ [34,136,66,5,96,4,256] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7290

theorem m23748_4 : Upper (D 6) (R 6) [34,136,66,5,96,256,4] 13 :=
  permutation_upper _ _ _ [34,136,66,5,96,1,256] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7289

theorem m23748_16 : Upper (D 6) (R 6) [34,136,66,5,96,256,16] 13 :=
  permutation_upper _ _ _ [34,136,66,5,96,16,256] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7291

def r23748 : Route 9 := (fun mask => (mask,id))

def c23748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23748 : Upper (D 6) (R 6) [34,136,66,5,96,256] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5,96,256] 13 (by decide) (choices 1) [1,4,16] r23748 c23748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m23748_1
  · exact m23748_4
  · exact m23748_16

def b23749 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 138 70 13 273 36 112 240 368), lower := (rows 35 138 70 13 273 36 64 128 256), losses := [] }

theorem u23749 : Upper (D 6) (R 6) [34,136,66,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23750 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 3, region := 368, targets := 2 }], pairs := [(2,0),(4,1)], upper := (rows 35 138 70 13 273 48 100 228 356), lower := (rows 35 138 70 13 273 48 64 128 256), losses := [] }

theorem u23750 : Upper (D 6) (R 6) [34,136,66,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23750 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23751 : Route 9 := (fun mask => (mask,id))

def c23751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23751 : Upper (D 6) (R 6) [34,136,66,5,257,64] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5,257,64] 13 (by decide) (choices 1) [4,16,32] r23751 c23751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7292
  · exact u7293
  · exact u7294

def b23752 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 70 13 304 33 84 212 340), lower := (rows 35 138 70 13 304 33 64 128 256), losses := [] }

theorem u23752 : Upper (D 6) (R 6) [34,136,66,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23753 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 138 70 13 304 36 81 209 337), lower := (rows 35 138 70 13 304 36 64 128 256), losses := [] }

theorem u23753 : Upper (D 6) (R 6) [34,136,66,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23754 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 138 70 13 304 48 69 197 325), lower := (rows 35 138 70 13 304 48 64 128 256), losses := [] }

theorem u23754 : Upper (D 6) (R 6) [34,136,66,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23754 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23755 : Route 9 := (fun mask => (mask,id))

def c23755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23755 : Upper (D 6) (R 6) [34,136,66,5,288,64] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5,288,64] 13 (by decide) (choices 1) [1,4,16] r23755 c23755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7295
  · exact u7296
  · exact u7297

def b23756 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 138 70 25 52 33 324 452 324), lower := (rows 35 138 70 25 52 33 64 128 256), losses := [] }

theorem u23756 : Upper (D 6) (R 6) [34,136,66,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23757 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 138 70 25 52 36 321 449 321), lower := (rows 35 138 70 25 52 36 64 128 256), losses := [] }

theorem u23757 : Upper (D 6) (R 6) [34,136,66,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23758 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 70 25 52 96 325 389 261), lower := (rows 35 138 70 25 52 96 64 128 256), losses := [] }

theorem u23758 : Upper (D 6) (R 6) [34,136,66,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23759 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 70 25 52 288 69 197 325), lower := (rows 35 138 70 25 52 288 64 128 256), losses := [] }

theorem u23759 : Upper (D 6) (R 6) [34,136,66,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23759 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23759
end Delivery.IrregularNine14.P06
