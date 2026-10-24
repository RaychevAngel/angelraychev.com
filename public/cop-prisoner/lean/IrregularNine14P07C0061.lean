import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0003

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3660 : Route 9 := (fun mask => (mask,id))

def c3660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3660 : Upper (D 7) (R 7) [12,48,66,160,320,1,128] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,320,1,128] 13 (by decide) (choices 1) [1,2] r3660 c3660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u232
  · exact u233

def b3661 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 400, targets := 33 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 13 50 70 168 400 33 65 194 322), lower := (rows 13 50 70 168 400 33 65 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 21 32 64 132 260), good := (rows 412 50 470 170 400 50 80 128 256) },{ target := 5, region := (rows 1 2 6 8 23 0 97 134 262), good := (rows 477 470 470 200 400 81 81 128 256) }] }

theorem u3661 : Upper (D 7) (R 7) [12,48,66,160,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3662 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 50 70 168 400 33 66 193 321), lower := (rows 13 50 70 168 400 33 66 128 256), losses := [] }

theorem u3662 : Upper (D 7) (R 7) [12,48,66,160,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3663 : Route 9 := (fun mask => (mask,id))

def c3663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3663 : Upper (D 7) (R 7) [12,48,66,160,384,64,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,384,64,1] 13 (by decide) (choices 1) [1,2] r3663 c3663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u234
  · exact u235

def b3664 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 400, targets := 98 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,6)], upper := (rows 13 50 70 168 400 96 66 129 257), lower := (rows 13 50 70 168 400 96 66 128 256), losses := [] }

theorem u3664 : Upper (D 7) (R 7) [12,48,66,160,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3665 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 168, targets := 1 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 13 50 70 200 273 160 65 162 290), lower := (rows 13 50 70 200 273 160 65 128 256), losses := [] }

theorem u3665 : Upper (D 7) (R 7) [12,48,66,192,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3666 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 50 70 200 273 160 66 161 289), lower := (rows 13 50 70 200 273 160 66 128 256), losses := [] }

theorem u3666 : Upper (D 7) (R 7) [12,48,66,192,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3667 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 50 70 200 273 160 96 131 259), lower := (rows 13 50 70 200 273 160 96 128 256), losses := [] }

theorem u3667 : Upper (D 7) (R 7) [12,48,66,192,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3668 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 70 200 400 33 65 162 290), lower := (rows 13 50 70 200 400 33 65 128 256), losses := [] }

theorem u3668 : Upper (D 7) (R 7) [12,48,66,192,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3669 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 50 70 200 400 33 66 161 289), lower := (rows 13 50 70 200 400 33 66 128 256), losses := [] }

theorem u3669 : Upper (D 7) (R 7) [12,48,66,192,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3670 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 50 70 200 400 33 96 131 259), lower := (rows 13 50 70 200 400 33 96 128 256), losses := [] }

theorem u3670 : Upper (D 7) (R 7) [12,48,66,192,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3671 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 150, targets := 1 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(4,0)], upper := (rows 13 50 70 265 146 96 65 160 416), lower := (rows 13 50 70 265 146 96 65 128 256), losses := [] }

theorem u3671 : Upper (D 7) (R 7) [12,48,66,257,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3672 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 393, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 50 70 265 146 96 96 129 385), lower := (rows 13 50 70 265 146 96 96 128 256), losses := [] }

theorem u3672 : Upper (D 7) (R 7) [12,48,66,257,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3673 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 54, targets := 1 },{ cop := 2, region := 297, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(4,0)], upper := (rows 13 50 70 265 146 96 192 161 289), lower := (rows 13 50 70 265 146 96 192 128 256), losses := [] }

theorem u3673 : Upper (D 7) (R 7) [12,48,66,257,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3674 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(3,6)], upper := (rows 13 50 70 266 145 96 65 160 416), lower := (rows 13 50 70 266 145 96 65 128 256), losses := [] }

theorem u3674 : Upper (D 7) (R 7) [12,48,66,258,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3675 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 393, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 50 70 266 145 96 96 129 385), lower := (rows 13 50 70 266 145 96 96 128 256), losses := [] }

theorem u3675 : Upper (D 7) (R 7) [12,48,66,258,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3676 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 297, targets := 128 },{ cop := 4, region := 102, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(3,7)], upper := (rows 13 50 70 266 145 96 192 161 289), lower := (rows 13 50 70 266 145 96 192 128 256), losses := [] }

theorem u3676 : Upper (D 7) (R 7) [12,48,66,258,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3677 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(3,6)], upper := (rows 13 50 70 266 208 33 65 160 416), lower := (rows 13 50 70 266 208 33 65 128 256), losses := [] }

theorem u3677 : Upper (D 7) (R 7) [12,48,66,258,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3678 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 50 70 266 208 33 96 129 385), lower := (rows 13 50 70 266 208 33 96 128 256), losses := [] }

theorem u3678 : Upper (D 7) (R 7) [12,48,66,258,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3679 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 70 266 208 33 192 161 289), lower := (rows 13 50 70 266 208 33 192 128 256), losses := [] }

theorem u3679 : Upper (D 7) (R 7) [12,48,66,258,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3680 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 296 19 160 65 192 448), lower := (rows 13 50 70 296 19 160 65 128 256), losses := [] }

theorem u3680 : Upper (D 7) (R 7) [12,48,66,288,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3681 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 425, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,1),(2,0),(2,5),(3,1)], upper := (rows 13 50 70 296 19 160 192 193 321), lower := (rows 13 50 70 296 19 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 224 224 128 256), good := (rows 12 118 102 360 22 224 224 224 256) }] }

theorem u3681 : Upper (D 7) (R 7) [12,48,66,288,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3682 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 296 81 160 65 130 386), lower := (rows 13 50 70 296 81 160 65 128 256), losses := [] }

theorem u3682 : Upper (D 7) (R 7) [12,48,66,288,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3683 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 296 81 160 66 129 385), lower := (rows 13 50 70 296 81 160 66 128 256), losses := [] }

theorem u3683 : Upper (D 7) (R 7) [12,48,66,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3684 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 162, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(3,6)], upper := (rows 13 50 70 296 81 160 192 131 259), lower := (rows 13 50 70 296 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 18 22 8 16 224 224 128 256), good := (rows 12 118 102 360 118 224 224 224 256) }] }

theorem u3684 : Upper (D 7) (R 7) [12,48,66,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3685 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,7),(3,0),(3,6)], upper := (rows 13 50 70 296 145 96 65 130 386), lower := (rows 13 50 70 296 145 96 65 128 256), losses := [] }

theorem u3685 : Upper (D 7) (R 7) [12,48,66,288,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3686 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 102, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 296 145 96 66 129 385), lower := (rows 13 50 70 296 145 96 66 128 256), losses := [] }

theorem u3686 : Upper (D 7) (R 7) [12,48,66,288,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3687 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 297, targets := 128 },{ cop := 4, region := 102, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(3,7)], upper := (rows 13 50 70 296 145 96 192 131 259), lower := (rows 13 50 70 296 145 96 192 128 256), losses := [] }

theorem u3687 : Upper (D 7) (R 7) [12,48,66,288,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3688 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,5)], upper := (rows 13 50 70 296 146 96 65 129 385), lower := (rows 13 50 70 296 146 96 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 65 193 321), good := (rows 477 18 470 264 146 448 449 128 256) },{ target := 6, region := (rows 1 42 4 40 53 32 0 193 321), good := (rows 415 58 406 314 146 442 401 128 256) }] }

theorem u3688 : Upper (D 7) (R 7) [12,48,66,288,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3689 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 54, targets := 1 },{ cop := 2, region := 297, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(4,0)], upper := (rows 13 50 70 296 146 96 192 129 257), lower := (rows 13 50 70 296 146 96 192 128 256), losses := [] }

theorem u3689 : Upper (D 7) (R 7) [12,48,66,288,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3690 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 2, region := 144, targets := 33 }], pairs := [(3,0),(3,6),(4,0),(4,5)], upper := (rows 13 50 70 296 208 33 65 130 386), lower := (rows 13 50 70 296 208 33 65 128 256), losses := [] }

theorem u3690 : Upper (D 7) (R 7) [12,48,66,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3691 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 50 70 296 208 33 66 129 385), lower := (rows 13 50 70 296 208 33 66 128 256), losses := [] }

theorem u3691 : Upper (D 7) (R 7) [12,48,66,288,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3692 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 70 296 208 33 192 131 259), lower := (rows 13 50 70 296 208 33 192 128 256), losses := [] }

theorem u3692 : Upper (D 7) (R 7) [12,48,66,288,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3693 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 50 70 392 81 160 65 162 290), lower := (rows 13 50 70 392 81 160 65 128 256), losses := [] }

theorem u3693 : Upper (D 7) (R 7) [12,48,66,384,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3694 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 50 70 392 81 160 66 161 289), lower := (rows 13 50 70 392 81 160 66 128 256), losses := [] }

theorem u3694 : Upper (D 7) (R 7) [12,48,66,384,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3695 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 50 70 392 81 160 96 131 259), lower := (rows 13 50 70 392 81 160 96 128 256), losses := [] }

theorem u3695 : Upper (D 7) (R 7) [12,48,66,384,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3696 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,7),(3,0),(3,6)], upper := (rows 13 50 70 392 145 96 65 162 290), lower := (rows 13 50 70 392 145 96 65 128 256), losses := [] }

theorem u3696 : Upper (D 7) (R 7) [12,48,66,384,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3697 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 13 50 70 392 145 96 66 161 289), lower := (rows 13 50 70 392 145 96 66 128 256), losses := [] }

theorem u3697 : Upper (D 7) (R 7) [12,48,66,384,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3698 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 393, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 50 70 392 145 96 96 131 259), lower := (rows 13 50 70 392 145 96 96 128 256), losses := [] }

theorem u3698 : Upper (D 7) (R 7) [12,48,66,384,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3699 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,5),(2,7),(3,1)], upper := (rows 13 50 70 392 146 33 65 224 352), lower := (rows 13 50 70 392 146 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 8 16 0 97 128 256), good := (rows 77 86 70 392 150 65 65 128 256) },{ target := 7, region := (rows 1 2 6 8 16 97 97 0 359), good := (rows 365 374 358 264 278 353 353 0 256) }] }

theorem u3699 : Upper (D 7) (R 7) [12,48,66,384,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3700 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 50 70 392 146 33 96 193 321), lower := (rows 13 50 70 392 146 33 96 128 256), losses := [] }

theorem u3700 : Upper (D 7) (R 7) [12,48,66,384,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3701 : Route 9 := (fun mask => (mask,id))

def c3701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3701 : Upper (D 7) (R 7) [12,48,66,384,130,64,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,130,64,1] 13 (by decide) (choices 1) [1,32] r3701 c3701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u236
  · exact u237

def b3702 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 393, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 50 70 392 146 96 96 129 257), lower := (rows 13 50 70 392 146 96 96 128 256), losses := [] }

theorem u3702 : Upper (D 7) (R 7) [12,48,66,384,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3703 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(3,0),(3,6),(4,0)], upper := (rows 13 50 70 392 208 33 65 162 290), lower := (rows 13 50 70 392 208 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 20 32 64 130 258), good := (rows 28 442 478 392 208 32 64 128 256) }] }

theorem u3703 : Upper (D 7) (R 7) [12,48,66,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3704 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 50 70 392 208 33 66 161 289), lower := (rows 13 50 70 392 208 33 66 128 256), losses := [] }

theorem u3704 : Upper (D 7) (R 7) [12,48,66,384,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3705 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 50 70 392 208 33 96 131 259), lower := (rows 13 50 70 392 208 33 96 128 256), losses := [] }

theorem u3705 : Upper (D 7) (R 7) [12,48,66,384,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3706 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 13 50 100 200 146 288 65 131 259), lower := (rows 13 50 100 200 146 288 65 128 256), losses := [{ target := 1, region := (rows 19 0 6 24 16 288 83 128 256), good := (rows 77 125 100 200 221 288 65 128 288) }] }

theorem u3706 : Upper (D 7) (R 7) [12,48,96,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3706 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3707 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 429, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 50 100 200 146 288 66 129 257), lower := (rows 13 50 100 200 146 288 66 128 256), losses := [] }

theorem u3707 : Upper (D 7) (R 7) [12,48,96,192,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3707 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3708 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 429, targets := 2 },{ cop := 2, region := 393, targets := 32 }], pairs := [(0,1),(0,5),(2,1),(3,1)], upper := (rows 13 50 100 265 19 160 66 192 448), lower := (rows 13 50 100 265 19 160 66 128 256), losses := [] }

theorem u3708 : Upper (D 7) (R 7) [12,48,96,257,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3709 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 50 100 265 19 160 192 194 322), lower := (rows 13 50 100 265 19 160 192 128 256), losses := [] }

theorem u3709 : Upper (D 7) (R 7) [12,48,96,257,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3710 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 4, region := 456, targets := 32 },{ cop := 6, region := 164, targets := 1 }], pairs := [(0,1),(2,0),(2,1),(3,5)], upper := (rows 13 50 100 266 19 160 65 192 448), lower := (rows 13 50 100 266 19 160 65 128 256), losses := [] }

theorem u3710 : Upper (D 7) (R 7) [12,48,96,258,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3711 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 50 100 266 19 160 192 193 321), lower := (rows 13 50 100 266 19 160 192 128 256), losses := [] }

theorem u3711 : Upper (D 7) (R 7) [12,48,96,258,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3712 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 50 100 266 81 160 65 130 386), lower := (rows 13 50 100 266 81 160 65 128 256), losses := [] }

theorem u3712 : Upper (D 7) (R 7) [12,48,96,258,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3713 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 68, targets := 129 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(2,7),(3,6)], upper := (rows 13 50 100 266 81 160 66 129 385), lower := (rows 13 50 100 266 81 160 66 128 256), losses := [] }

theorem u3713 : Upper (D 7) (R 7) [12,48,96,258,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3714 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 50 100 266 81 160 192 131 259), lower := (rows 13 50 100 266 81 160 192 128 256), losses := [] }

theorem u3714 : Upper (D 7) (R 7) [12,48,96,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3715 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 100 266 208 33 65 130 386), lower := (rows 13 50 100 266 208 33 65 128 256), losses := [] }

theorem u3715 : Upper (D 7) (R 7) [12,48,96,258,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3716 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 68, targets := 129 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,0),(2,7),(4,1)], upper := (rows 13 50 100 266 208 33 66 129 385), lower := (rows 13 50 100 266 208 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 33 64 161 289), good := (rows 445 432 500 264 208 417 64 128 256) }] }

theorem u3716 : Upper (D 7) (R 7) [12,48,96,258,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3717 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 100 266 208 33 192 131 259), lower := (rows 13 50 100 266 208 33 192 128 256), losses := [] }

theorem u3717 : Upper (D 7) (R 7) [12,48,96,258,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3718 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 4, region := 162, targets := 1 },{ cop := 4, region := 456, targets := 32 }], pairs := [(1,0),(1,6),(3,5),(4,6)], upper := (rows 13 50 100 328 19 160 65 130 386), lower := (rows 13 50 100 328 19 160 65 128 256), losses := [] }

theorem u3718 : Upper (D 7) (R 7) [12,48,96,320,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3719 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 429, targets := 2 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(3,1)], upper := (rows 13 50 100 328 19 160 66 129 385), lower := (rows 13 50 100 328 19 160 66 128 256), losses := [] }

theorem u3719 : Upper (D 7) (R 7) [12,48,96,320,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3719
end Delivery.IrregularNine14.P07
