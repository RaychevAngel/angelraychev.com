import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0090

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18660 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 137 274 36 97 225 353), lower := (rows 25 38 70 137 274 36 64 128 256), losses := [] }

theorem u18660 : Upper (D 6) (R 6) [24,36,66,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18661 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 137 274 96 101 165 293), lower := (rows 25 38 70 137 274 96 64 128 256), losses := [] }

theorem u18661 : Upper (D 6) (R 6) [24,36,66,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18662 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 70 137 304 33 70 198 326), lower := (rows 25 38 70 137 304 33 64 128 256), losses := [] }

theorem u18662 : Upper (D 6) (R 6) [24,36,66,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18663 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 473, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 137 304 34 69 197 325), lower := (rows 25 38 70 137 304 34 64 128 256), losses := [] }

theorem u18663 : Upper (D 6) (R 6) [24,36,66,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18664 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 137 304 36 67 195 323), lower := (rows 25 38 70 137 304 36 64 128 256), losses := [] }

theorem u18664 : Upper (D 6) (R 6) [24,36,66,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18665 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 137 304 96 71 135 263), lower := (rows 25 38 70 137 304 96 64 128 256), losses := [] }

theorem u18665 : Upper (D 6) (R 6) [24,36,66,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18666 : PairBound 9 := { available := 97, camps := [], pairs := [(0,1),(3,2),(4,1)], upper := (rows 25 38 70 138 276 33 97 225 353), lower := (rows 25 38 70 138 276 33 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 18 41 105 169 297), good := (rows 505 500 84 505 276 481 64 128 256) },{ target := 2, region := (rows 1 2 0 10 16 33 97 161 289), good := (rows 505 490 74 138 272 481 64 128 256) }] }

theorem u18666 : Upper (D 6) (R 6) [24,36,66,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18667 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 138 276 96 97 161 289), lower := (rows 25 38 70 138 276 96 64 128 256), losses := [] }

theorem u18667 : Upper (D 6) (R 6) [24,36,66,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18668 : Route 9 := (fun mask => (mask,id))

def c18668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18668 : Upper (D 6) (R 6) [24,36,66,130,288,1] 13 := by
  apply FastRouting.sound _ _ [24,36,66,130,288,1] 13 (by decide) (choices 1) [1,4] r18668 c18668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5437
  · exact u5438

def b18669 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 138 304 36 65 193 321), lower := (rows 25 38 70 138 304 36 64 128 256), losses := [] }

theorem u18669 : Upper (D 6) (R 6) [24,36,66,130,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18670 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 138 304 96 69 133 261), lower := (rows 25 38 70 138 304 96 64 128 256), losses := [] }

theorem u18670 : Upper (D 6) (R 6) [24,36,66,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18671 : Route 9 := (fun mask => (mask,id))

def c18671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18671 : Upper (D 6) (R 6) [24,36,66,130,320,1] 13 := by
  apply FastRouting.sound _ _ [24,36,66,130,320,1] 13 (by decide) (choices 1) [1,4,32] r18671 c18671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5439
  · exact u5440
  · exact u5441

def b18672 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 138 336 36 97 161 289), lower := (rows 25 38 70 138 336 36 64 128 256), losses := [] }

theorem u18672 : Upper (D 6) (R 6) [24,36,66,130,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18673 : Route 9 := (fun mask => (mask,id))

def c18673 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18673 : Upper (D 6) (R 6) [24,36,66,160,320,1] 13 := by
  apply FastRouting.sound _ _ [24,36,66,160,320,1] 13 (by decide) (choices 1) [1,2,4] r18673 c18673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5442
  · exact u5443
  · exact u5444

def b18674 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 473, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 168 336 34 69 133 261), lower := (rows 25 38 70 168 336 34 64 128 256), losses := [] }

theorem u18674 : Upper (D 6) (R 6) [24,36,66,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18675 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 168 336 36 67 131 259), lower := (rows 25 38 70 168 336 36 64 128 256), losses := [] }

theorem u18675 : Upper (D 6) (R 6) [24,36,66,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18676 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 133 11 84 34 352 480 352), lower := (rows 25 38 133 11 84 34 64 128 256), losses := [] }

theorem u18676 : Upper (D 6) (R 6) [24,36,129,3,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18677 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 25 38 133 11 84 96 354 418 290), lower := (rows 25 38 133 11 84 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 32 0 130 258), good := (rows 29 422 133 399 20 32 0 128 256) }] }

theorem u18677 : Upper (D 6) (R 6) [24,36,129,3,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18678 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 25 38 133 11 84 288 98 226 354), lower := (rows 25 38 133 11 84 288 64 128 256), losses := [] }

theorem u18678 : Upper (D 6) (R 6) [24,36,129,3,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18678 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18679 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 133 11 276 34 96 224 352), lower := (rows 25 38 133 11 276 34 64 128 256), losses := [] }

theorem u18679 : Upper (D 6) (R 6) [24,36,129,3,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18680 : Route 9 := (fun mask => (mask,id))

def c18680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18680 : Upper (D 6) (R 6) [24,36,129,3,260,64] 13 := by
  apply FastRouting.sound _ _ [24,36,129,3,260,64] 13 (by decide) (choices 1) [2,32] r18680 c18680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5445
  · exact u5446

def b18681 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 25 38 133 11 336 34 100 228 356), lower := (rows 25 38 133 11 336 34 64 128 256), losses := [] }

theorem u18681 : Upper (D 6) (R 6) [24,36,129,3,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18682 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 11 336 36 98 226 354), lower := (rows 25 38 133 11 336 36 64 128 256), losses := [] }

theorem u18682 : Upper (D 6) (R 6) [24,36,129,3,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18683 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 25 38 133 11 336 96 102 166 294), lower := (rows 25 38 133 11 336 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 32 0 130 258), good := (rows 29 422 133 399 272 32 0 128 256) }] }

theorem u18683 : Upper (D 6) (R 6) [24,36,129,3,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18684 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 25 38 133 73 274 34 100 228 356), lower := (rows 25 38 133 73 274 34 64 128 256), losses := [] }

theorem u18684 : Upper (D 6) (R 6) [24,36,129,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18685 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 73 274 36 98 226 354), lower := (rows 25 38 133 73 274 36 64 128 256), losses := [] }

theorem u18685 : Upper (D 6) (R 6) [24,36,129,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18686 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 25 38 133 73 274 96 102 166 294), lower := (rows 25 38 133 73 274 96 64 128 256), losses := [] }

theorem u18686 : Upper (D 6) (R 6) [24,36,129,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18687 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 25 38 133 73 276 34 98 226 354), lower := (rows 25 38 133 73 276 34 64 128 256), losses := [] }

theorem u18687 : Upper (D 6) (R 6) [24,36,129,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18688 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 25 38 133 73 276 96 98 162 290), lower := (rows 25 38 133 73 276 96 64 128 256), losses := [] }

theorem u18688 : Upper (D 6) (R 6) [24,36,129,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18689 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 25 38 133 73 304 34 70 198 326), lower := (rows 25 38 133 73 304 34 64 128 256), losses := [] }

theorem u18689 : Upper (D 6) (R 6) [24,36,129,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18690 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 73 304 36 66 194 322), lower := (rows 25 38 133 73 304 36 64 128 256), losses := [] }

theorem u18690 : Upper (D 6) (R 6) [24,36,129,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18691 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 25 38 133 73 304 96 70 134 262), lower := (rows 25 38 133 73 304 96 64 128 256), losses := [] }

theorem u18691 : Upper (D 6) (R 6) [24,36,129,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18692 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 1, region := 328, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 25 38 133 74 84 33 354 418 290), lower := (rows 25 38 133 74 84 33 64 128 256), losses := [] }

theorem u18692 : Upper (D 6) (R 6) [24,36,129,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18693 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 25 38 133 74 84 34 353 417 289), lower := (rows 25 38 133 74 84 34 64 128 256), losses := [] }

theorem u18693 : Upper (D 6) (R 6) [24,36,129,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18694 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 38 133 74 84 288 99 163 291), lower := (rows 25 38 133 74 84 288 64 128 256), losses := [] }

theorem u18694 : Upper (D 6) (R 6) [24,36,129,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18694 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18695 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 133 74 112 33 326 390 262), lower := (rows 25 38 133 74 112 33 64 128 256), losses := [] }

theorem u18695 : Upper (D 6) (R 6) [24,36,129,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18696 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 388, targets := 34 },{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 25 38 133 74 112 34 325 389 261), lower := (rows 25 38 133 74 112 34 64 128 256), losses := [] }

theorem u18696 : Upper (D 6) (R 6) [24,36,129,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18697 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 74 112 36 323 387 259), lower := (rows 25 38 133 74 112 36 64 128 256), losses := [] }

theorem u18697 : Upper (D 6) (R 6) [24,36,129,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18698 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 38 133 74 112 288 71 135 263), lower := (rows 25 38 133 74 112 288 64 128 256), losses := [] }

theorem u18698 : Upper (D 6) (R 6) [24,36,129,66,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18698 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18699 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 38 133 74 273 34 100 228 356), lower := (rows 25 38 133 74 273 34 64 128 256), losses := [] }

theorem u18699 : Upper (D 6) (R 6) [24,36,129,66,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18700 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 74 273 36 98 226 354), lower := (rows 25 38 133 74 273 36 64 128 256), losses := [] }

theorem u18700 : Upper (D 6) (R 6) [24,36,129,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18701 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 106, targets := 1 }], pairs := [(0,6),(1,0),(3,0)], upper := (rows 25 38 133 74 273 96 102 166 294), lower := (rows 25 38 133 74 273 96 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 24 32 0 130 258), good := (rows 29 422 133 415 273 32 0 128 256) }] }

theorem u18701 : Upper (D 6) (R 6) [24,36,129,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18702 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 25 38 133 74 274 33 100 228 356), lower := (rows 25 38 133 74 274 33 64 128 256), losses := [] }

theorem u18702 : Upper (D 6) (R 6) [24,36,129,66,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18703 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 74 274 36 97 225 353), lower := (rows 25 38 133 74 274 36 64 128 256), losses := [] }

theorem u18703 : Upper (D 6) (R 6) [24,36,129,66,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18704 : Route 9 := (fun mask => (mask,id))

def c18704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18704 : Upper (D 6) (R 6) [24,36,129,66,258,64] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,258,64] 13 (by decide) (choices 1) [1,4,32] r18704 c18704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5447
  · exact u5448
  · exact u5449

def b18705 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 1, region := 72, targets := 4 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 25 38 133 74 276 33 98 226 354), lower := (rows 25 38 133 74 276 33 64 128 256), losses := [] }

theorem u18705 : Upper (D 6) (R 6) [24,36,129,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18706 : Route 9 := (fun mask => (mask,id))

def c18706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18706 : Upper (D 6) (R 6) [24,36,129,66,260,2] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,260,2] 13 (by decide) (choices 1) [1,32] r18706 c18706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5450
  · exact u5451

def r18707 : Route 9 := (fun mask => (mask,id))

def c18707 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18707 : Upper (D 6) (R 6) [24,36,129,66,260,64] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,260,64] 13 (by decide) (choices 1) [1,2,32] r18707 c18707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5452
  · exact u5453
  · exact u5454

def b18708 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 1, region := 72, targets := 32 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 25 38 133 74 304 33 70 198 326), lower := (rows 25 38 133 74 304 33 64 128 256), losses := [] }

theorem u18708 : Upper (D 6) (R 6) [24,36,129,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18709 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 38 133 74 304 34 69 197 325), lower := (rows 25 38 133 74 304 34 64 128 256), losses := [] }

theorem u18709 : Upper (D 6) (R 6) [24,36,129,66,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18710 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 74 304 36 67 195 323), lower := (rows 25 38 133 74 304 36 64 128 256), losses := [] }

theorem u18710 : Upper (D 6) (R 6) [24,36,129,66,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18711 : Route 9 := (fun mask => (mask,id))

def c18711 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18711 : Upper (D 6) (R 6) [24,36,129,66,288,64] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,288,64] 13 (by decide) (choices 1) [1,2,4] r18711 c18711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5455
  · exact u5456
  · exact u5457

def b18712 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 1, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 25 38 133 74 336 33 102 166 294), lower := (rows 25 38 133 74 336 33 64 128 256), losses := [] }

theorem u18712 : Upper (D 6) (R 6) [24,36,129,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18713 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 25 38 133 74 336 34 101 165 293), lower := (rows 25 38 133 74 336 34 64 128 256), losses := [] }

theorem u18713 : Upper (D 6) (R 6) [24,36,129,66,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18714 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 74 336 36 99 163 291), lower := (rows 25 38 133 74 336 36 64 128 256), losses := [] }

theorem u18714 : Upper (D 6) (R 6) [24,36,129,66,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18715 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 133 76 112 33 322 386 258), lower := (rows 25 38 133 76 112 33 64 128 256), losses := [] }

theorem u18715 : Upper (D 6) (R 6) [24,36,129,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18716 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 25 38 133 76 112 34 323 387 259), lower := (rows 25 38 133 76 112 34 64 128 256), losses := [] }

theorem u18716 : Upper (D 6) (R 6) [24,36,129,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18717 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 38 133 76 112 288 67 131 259), lower := (rows 25 38 133 76 112 288 64 128 256), losses := [] }

theorem u18717 : Upper (D 6) (R 6) [24,36,129,68,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18717 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18718 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 38 133 76 273 34 98 226 354), lower := (rows 25 38 133 76 273 34 64 128 256), losses := [] }

theorem u18718 : Upper (D 6) (R 6) [24,36,129,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18719 : Route 9 := (fun mask => (mask,id))

def c18719 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18719 : Upper (D 6) (R 6) [24,36,129,68,257,64] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,257,64] 13 (by decide) (choices 1) [2,32] r18719 c18719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5458
  · exact u5459

#print axioms u18719
end Delivery.IrregularNine14.P06
