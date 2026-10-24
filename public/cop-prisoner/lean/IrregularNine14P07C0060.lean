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

def b3600 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 101, targets := 2 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 69 266 146 96 96 129 385), lower := (rows 13 50 69 266 146 96 96 128 256), losses := [] }

theorem u3600 : Upper (D 7) (R 7) [12,48,65,258,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3601 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 6, region := 50, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 13 50 69 266 146 96 192 161 289), lower := (rows 13 50 69 266 146 96 192 128 256), losses := [] }

theorem u3601 : Upper (D 7) (R 7) [12,48,65,258,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3602 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 50 69 266 208 34 65 160 416), lower := (rows 13 50 69 266 208 34 65 128 256), losses := [] }

theorem u3602 : Upper (D 7) (R 7) [12,48,65,258,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3603 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 144, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 13 50 69 266 208 34 96 129 385), lower := (rows 13 50 69 266 208 34 96 128 256), losses := [] }

theorem u3603 : Upper (D 7) (R 7) [12,48,65,258,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3604 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 69 266 208 34 192 161 289), lower := (rows 13 50 69 266 208 34 192 128 256), losses := [] }

theorem u3604 : Upper (D 7) (R 7) [12,48,65,258,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3605 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 69 296 19 160 66 192 448), lower := (rows 13 50 69 296 19 160 66 128 256), losses := [] }

theorem u3605 : Upper (D 7) (R 7) [12,48,65,288,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3606 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,1),(1,0),(2,5),(3,0)], upper := (rows 13 50 69 296 19 160 192 194 322), lower := (rows 13 50 69 296 19 160 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 224 224 128 256), good := (rows 13 112 101 365 17 224 224 224 256) }] }

theorem u3606 : Upper (D 7) (R 7) [12,48,65,288,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3607 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 50 69 296 82 160 65 130 386), lower := (rows 13 50 69 296 82 160 65 128 256), losses := [] }

theorem u3607 : Upper (D 7) (R 7) [12,48,65,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3608 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 50 69 296 82 160 66 129 385), lower := (rows 13 50 69 296 82 160 66 128 256), losses := [] }

theorem u3608 : Upper (D 7) (R 7) [12,48,65,288,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3609 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 82, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 13 50 69 296 82 160 192 131 259), lower := (rows 13 50 69 296 82 160 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 224 224 128 256), good := (rows 13 112 101 365 112 224 224 224 256) }] }

theorem u3609 : Upper (D 7) (R 7) [12,48,65,288,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3610 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 50 69 296 145 96 66 130 386), lower := (rows 13 50 69 296 145 96 66 128 256), losses := [] }

theorem u3610 : Upper (D 7) (R 7) [12,48,65,288,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3611 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 1, region := 264, targets := 64 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,0),(3,0),(3,6),(3,7)], upper := (rows 13 50 69 296 145 96 192 130 258), lower := (rows 13 50 69 296 145 96 192 128 256), losses := [] }

theorem u3611 : Upper (D 7) (R 7) [12,48,65,288,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3612 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 296 146 96 65 130 386), lower := (rows 13 50 69 296 146 96 65 128 256), losses := [] }

theorem u3612 : Upper (D 7) (R 7) [12,48,65,288,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3613 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 397, targets := 2 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 69 296 146 96 66 129 385), lower := (rows 13 50 69 296 146 96 66 128 256), losses := [] }

theorem u3613 : Upper (D 7) (R 7) [12,48,65,288,130,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3614 : Route 9 := (fun mask => (mask,id))

def c3614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3614 : Upper (D 7) (R 7) [12,48,65,288,130,64,128] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,130,64,128] 13 (by decide) (choices 1) [1,2] r3614 c3614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u224
  · exact u225

def b3615 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 50 69 296 208 34 65 130 386), lower := (rows 13 50 69 296 208 34 65 128 256), losses := [] }

theorem u3615 : Upper (D 7) (R 7) [12,48,65,288,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3616 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 144, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 50 69 296 208 34 66 129 385), lower := (rows 13 50 69 296 208 34 66 128 256), losses := [] }

theorem u3616 : Upper (D 7) (R 7) [12,48,65,288,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3617 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 69 296 208 34 192 131 259), lower := (rows 13 50 69 296 208 34 192 128 256), losses := [] }

theorem u3617 : Upper (D 7) (R 7) [12,48,65,288,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3618 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 69 392 82 160 65 162 290), lower := (rows 13 50 69 392 82 160 65 128 256), losses := [] }

theorem u3618 : Upper (D 7) (R 7) [12,48,65,384,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3619 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 50 69 392 82 160 66 161 289), lower := (rows 13 50 69 392 82 160 66 128 256), losses := [] }

theorem u3619 : Upper (D 7) (R 7) [12,48,65,384,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3620 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 82, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 392 82 160 96 131 259), lower := (rows 13 50 69 392 82 160 96 128 256), losses := [] }

theorem u3620 : Upper (D 7) (R 7) [12,48,65,384,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3621 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 6, region := 429, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 69 392 146 33 66 224 352), lower := (rows 13 50 69 392 146 33 66 128 256), losses := [] }

theorem u3621 : Upper (D 7) (R 7) [12,48,65,384,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3622 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 69 392 146 33 96 194 322), lower := (rows 13 50 69 392 146 33 96 128 256), losses := [] }

theorem u3622 : Upper (D 7) (R 7) [12,48,65,384,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3623 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 392 146 96 65 162 290), lower := (rows 13 50 69 392 146 96 65 128 256), losses := [] }

theorem u3623 : Upper (D 7) (R 7) [12,48,65,384,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3624 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 397, targets := 2 },{ cop := 3, region := 114, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 69 392 146 96 66 161 289), lower := (rows 13 50 69 392 146 96 66 128 256), losses := [] }

theorem u3624 : Upper (D 7) (R 7) [12,48,65,384,130,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3625 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 69 392 146 96 96 131 259), lower := (rows 13 50 69 392 146 96 96 128 256), losses := [] }

theorem u3625 : Upper (D 7) (R 7) [12,48,65,384,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3626 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 50 69 392 208 34 65 162 290), lower := (rows 13 50 69 392 208 34 65 128 256), losses := [] }

theorem u3626 : Upper (D 7) (R 7) [12,48,65,384,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3627 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 4, region := 34, targets := 128 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 69 392 208 34 66 161 289), lower := (rows 13 50 69 392 208 34 66 128 256), losses := [] }

theorem u3627 : Upper (D 7) (R 7) [12,48,65,384,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3628 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 4, region := 34, targets := 128 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 69 392 208 34 96 131 259), lower := (rows 13 50 69 392 208 34 96 128 256), losses := [] }

theorem u3628 : Upper (D 7) (R 7) [12,48,65,384,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3629 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 50 70 104 145 288 65 130 386), lower := (rows 13 50 70 104 145 288 65 128 256), losses := [] }

theorem u3629 : Upper (D 7) (R 7) [12,48,66,96,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3629 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3630 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 50 70 104 145 288 66 129 385), lower := (rows 13 50 70 104 145 288 66 128 256), losses := [] }

theorem u3630 : Upper (D 7) (R 7) [12,48,66,96,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3630 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3631 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 297, targets := 128 }], pairs := [(0,7),(1,6),(4,6)], upper := (rows 13 50 70 104 145 288 192 131 259), lower := (rows 13 50 70 104 145 288 192 128 256), losses := [] }

theorem u3631 : Upper (D 7) (R 7) [12,48,66,96,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3631 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3632 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 13 50 70 104 273 160 65 130 386), lower := (rows 13 50 70 104 273 160 65 128 256), losses := [] }

theorem u3632 : Upper (D 7) (R 7) [12,48,66,96,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3633 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 13 50 70 104 273 160 66 129 385), lower := (rows 13 50 70 104 273 160 66 128 256), losses := [] }

theorem u3633 : Upper (D 7) (R 7) [12,48,66,96,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3634 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 104 273 160 192 131 259), lower := (rows 13 50 70 104 273 160 192 128 256), losses := [] }

theorem u3634 : Upper (D 7) (R 7) [12,48,66,96,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3635 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 136, targets := 65 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(3,6)], upper := (rows 13 50 70 138 273 96 65 160 416), lower := (rows 13 50 70 138 273 96 65 128 256), losses := [] }

theorem u3635 : Upper (D 7) (R 7) [12,48,66,130,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3636 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 137, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 50 70 138 273 96 96 129 385), lower := (rows 13 50 70 138 273 96 96 128 256), losses := [] }

theorem u3636 : Upper (D 7) (R 7) [12,48,66,130,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3637 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 0, region := 496, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(2,5),(4,1)], upper := (rows 13 50 70 138 273 96 192 161 289), lower := (rows 13 50 70 138 273 96 192 128 256), losses := [] }

theorem u3637 : Upper (D 7) (R 7) [12,48,66,130,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3638 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 136, targets := 65 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(3,6)], upper := (rows 13 50 70 138 336 33 65 160 416), lower := (rows 13 50 70 138 336 33 65 128 256), losses := [] }

theorem u3638 : Upper (D 7) (R 7) [12,48,66,130,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3639 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 50 70 138 336 33 96 129 385), lower := (rows 13 50 70 138 336 33 96 128 256), losses := [] }

theorem u3639 : Upper (D 7) (R 7) [12,48,66,130,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3640 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(0,6),(2,5),(3,6)], upper := (rows 13 50 70 138 336 33 192 161 289), lower := (rows 13 50 70 138 336 33 192 128 256), losses := [] }

theorem u3640 : Upper (D 7) (R 7) [12,48,66,130,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3641 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 70 138 336 160 65 161 289), lower := (rows 13 50 70 138 336 160 65 128 256), losses := [] }

theorem u3641 : Upper (D 7) (R 7) [12,48,66,130,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3642 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 50 70 138 336 160 96 129 257), lower := (rows 13 50 70 138 336 160 96 128 256), losses := [] }

theorem u3642 : Upper (D 7) (R 7) [12,48,66,130,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3643 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,7),(3,0),(3,6)], upper := (rows 13 50 70 168 145 96 65 386 258), lower := (rows 13 50 70 168 145 96 65 128 256), losses := [] }

theorem u3643 : Upper (D 7) (R 7) [12,48,66,160,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3644 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 400, targets := 98 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,6)], upper := (rows 13 50 70 168 145 96 66 385 257), lower := (rows 13 50 70 168 145 96 66 128 256), losses := [] }

theorem u3644 : Upper (D 7) (R 7) [12,48,66,160,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3645 : Route 9 := (fun mask => (mask,id))

def c3645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3645 : Upper (D 7) (R 7) [12,48,66,160,129,64,256] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,129,64,256] 13 (by decide) (choices 1) [1,2] r3645 c3645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u226
  · exact u227

def b3646 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 358, targets := 128 },{ cop := 2, region := 424, targets := 1 }], pairs := [(1,7),(2,7),(3,0)], upper := (rows 13 50 70 168 145 288 65 194 322), lower := (rows 13 50 70 168 145 288 65 128 256), losses := [] }

theorem u3646 : Upper (D 7) (R 7) [12,48,66,160,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3646 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3647 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 13 50 70 168 145 288 66 193 321), lower := (rows 13 50 70 168 145 288 66 128 256), losses := [] }

theorem u3647 : Upper (D 7) (R 7) [12,48,66,160,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3647 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3648 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 2, region := 400, targets := 33 }], pairs := [(3,0),(3,6),(4,0),(4,5)], upper := (rows 13 50 70 168 208 33 65 386 258), lower := (rows 13 50 70 168 208 33 65 128 256), losses := [] }

theorem u3648 : Upper (D 7) (R 7) [12,48,66,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3649 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 50 70 168 208 33 66 385 257), lower := (rows 13 50 70 168 208 33 66 128 256), losses := [] }

theorem u3649 : Upper (D 7) (R 7) [12,48,66,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3650 : Route 9 := (fun mask => (mask,id))

def c3650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3650 : Upper (D 7) (R 7) [12,48,66,160,192,1,256] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,192,1,256] 13 (by decide) (choices 1) [1,2] r3650 c3650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u228
  · exact u229

def r3651 : Route 9 := (fun mask => (mask,id))

def c3651 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3651 : Upper (D 7) (R 7) [12,48,66,160,192,256,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,192,256,1] 13 (by decide) (choices 1) [1,2] r3651 c3651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u230
  · exact u231

def b3652 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 13 50 70 168 208 288 66 129 257), lower := (rows 13 50 70 168 208 288 66 128 256), losses := [] }

theorem u3652 : Upper (D 7) (R 7) [12,48,66,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3652 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3653 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 136, targets := 65 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,7),(3,0),(3,6)], upper := (rows 13 50 70 168 273 96 65 130 386), lower := (rows 13 50 70 168 273 96 65 128 256), losses := [] }

theorem u3653 : Upper (D 7) (R 7) [12,48,66,160,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3654 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 102, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 168 273 96 66 129 385), lower := (rows 13 50 70 168 273 96 66 128 256), losses := [] }

theorem u3654 : Upper (D 7) (R 7) [12,48,66,160,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3655 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 40, targets := 3 }], pairs := [(0,1),(1,0),(3,0),(3,1)], upper := (rows 13 50 70 168 273 96 192 131 259), lower := (rows 13 50 70 168 273 96 192 128 256), losses := [{ target := 0, region := (rows 0 18 4 200 16 237 200 128 256), good := (rows 108 50 110 232 306 104 232 232 256) },{ target := 1, region := (rows 5 0 4 200 16 237 200 128 256), good := (rows 109 48 109 232 305 104 232 232 256) }] }

theorem u3655 : Upper (D 7) (R 7) [12,48,66,160,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3656 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,5)], upper := (rows 13 50 70 168 274 96 65 129 385), lower := (rows 13 50 70 168 274 96 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 65 193 321), good := (rows 477 18 470 136 274 448 449 128 256) },{ target := 6, region := (rows 1 42 4 40 53 32 0 193 321), good := (rows 415 58 406 186 274 442 401 128 256) }] }

theorem u3656 : Upper (D 7) (R 7) [12,48,66,160,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3657 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 6, region := 40, targets := 1 }], pairs := [(0,1),(1,7),(3,0),(3,1)], upper := (rows 13 50 70 168 274 96 192 129 257), lower := (rows 13 50 70 168 274 96 192 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 17 100 64 0 257), good := (rows 319 50 102 40 274 96 96 0 256) }] }

theorem u3657 : Upper (D 7) (R 7) [12,48,66,160,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3658 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 136, targets := 65 },{ cop := 2, region := 400, targets := 33 }], pairs := [(3,0),(3,6),(4,0),(4,5)], upper := (rows 13 50 70 168 336 33 65 130 386), lower := (rows 13 50 70 168 336 33 65 128 256), losses := [] }

theorem u3658 : Upper (D 7) (R 7) [12,48,66,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3659 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 50 70 168 336 33 66 129 385), lower := (rows 13 50 70 168 336 33 66 128 256), losses := [] }

theorem u3659 : Upper (D 7) (R 7) [12,48,66,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3659
end Delivery.IrregularNine14.P07
