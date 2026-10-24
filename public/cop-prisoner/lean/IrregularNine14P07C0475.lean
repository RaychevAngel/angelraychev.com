import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0179

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28500 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 14 44 208 33 210 146 402), lower := (rows 97 259 14 44 208 33 64 128 256), losses := [] }

theorem u28500 : Upper (D 7) (R 7) [96,257,10,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28501 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0)], upper := (rows 97 259 14 44 208 34 209 145 401), lower := (rows 97 259 14 44 208 34 64 128 256), losses := [] }

theorem u28501 : Upper (D 7) (R 7) [96,257,10,36,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28502 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 14 44 208 48 195 131 387), lower := (rows 97 259 14 44 208 48 64 128 256), losses := [] }

theorem u28502 : Upper (D 7) (R 7) [96,257,10,36,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28502 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28503 : Route 9 := (fun mask => (mask,id))

def c28503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28503 : Upper (D 7) (R 7) [96,257,10,36,192,128] 13 := by
  apply FastRouting.sound _ _ [96,257,10,36,192,128] 13 (by decide) (choices 1) [1,2,16] r28503 c28503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10742
  · exact u10743
  · exact u10744

def b28504 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 208, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 97 259 14 56 82 33 196 132 388), lower := (rows 97 259 14 56 82 33 64 128 256), losses := [] }

theorem u28504 : Upper (D 7) (R 7) [96,257,10,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28505 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 259 14 56 82 36 193 129 385), lower := (rows 97 259 14 56 82 36 64 128 256), losses := [] }

theorem u28505 : Upper (D 7) (R 7) [96,257,10,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28505 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28506 : Route 9 := (fun mask => (mask,id))

def c28506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28506 : Upper (D 7) (R 7) [96,257,10,48,66,128] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,66,128] 13 (by decide) (choices 1) [1,4,128] r28506 c28506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10745
  · exact u10746
  · exact u10747

def b28507 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 14 56 84 33 194 130 386), lower := (rows 97 259 14 56 84 33 64 128 256), losses := [] }

theorem u28507 : Upper (D 7) (R 7) [96,257,10,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28508 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 0, region := 386, targets := 64 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(1,5),(1,6),(2,0)], upper := (rows 97 259 14 56 84 34 193 129 385), lower := (rows 97 259 14 56 84 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 38 27 17 38 64 128 256), good := (rows 124 318 46 60 124 46 64 128 256) }] }

theorem u28508 : Upper (D 7) (R 7) [96,257,10,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28509 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 97 259 14 56 84 160 195 131 387), lower := (rows 97 259 14 56 84 160 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 20 0 67 131 259), good := (rows 451 451 478 24 84 128 64 128 256) },{ target := 6, region := (rows 1 3 4 24 16 167 0 131 259), good := (rows 419 419 430 56 60 160 0 160 256) }] }

theorem u28509 : Upper (D 7) (R 7) [96,257,10,48,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28510 : Route 9 := (fun mask => (mask,id))

def c28510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28510 : Upper (D 7) (R 7) [96,257,10,48,129,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,129,2] 13 (by decide) (choices 1) [4,128] r28510 c28510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10748
  · exact u10749

def b28511 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 259 14 56 145 36 194 194 450), lower := (rows 97 259 14 56 145 36 64 128 256), losses := [{ target := 5, region := (rows 1 19 12 8 19 0 95 159 287), good := (rows 467 467 478 478 467 452 64 128 256) }] }

theorem u28511 : Upper (D 7) (R 7) [96,257,10,48,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28511 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28512 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 56 145 96 198 134 390), lower := (rows 97 259 14 56 145 96 64 128 256), losses := [] }

theorem u28512 : Upper (D 7) (R 7) [96,257,10,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28513 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 259 14 56 145 160 70 198 326), lower := (rows 97 259 14 56 145 160 64 128 256), losses := [] }

theorem u28513 : Upper (D 7) (R 7) [96,257,10,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28514 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 259 14 56 146 33 196 196 452), lower := (rows 97 259 14 56 146 33 64 128 256), losses := [] }

theorem u28514 : Upper (D 7) (R 7) [96,257,10,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28515 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 259 14 56 146 36 193 193 449), lower := (rows 97 259 14 56 146 36 64 128 256), losses := [] }

theorem u28515 : Upper (D 7) (R 7) [96,257,10,48,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28515 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28516 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 56 146 96 197 133 389), lower := (rows 97 259 14 56 146 96 64 128 256), losses := [] }

theorem u28516 : Upper (D 7) (R 7) [96,257,10,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28517 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 259 14 56 146 160 69 197 325), lower := (rows 97 259 14 56 146 160 64 128 256), losses := [] }

theorem u28517 : Upper (D 7) (R 7) [96,257,10,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28518 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 259 14 56 148 33 194 194 450), lower := (rows 97 259 14 56 148 33 64 128 256), losses := [] }

theorem u28518 : Upper (D 7) (R 7) [96,257,10,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28519 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(1,5),(3,0),(4,1)], upper := (rows 97 259 14 56 148 34 193 193 449), lower := (rows 97 259 14 56 148 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 38 64 128 256), good := (rows 96 290 46 56 188 34 64 128 256) },{ target := 1, region := (rows 41 0 4 8 20 32 111 175 303), good := (rows 481 449 477 505 468 481 64 128 256) }] }

theorem u28519 : Upper (D 7) (R 7) [96,257,10,48,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28520 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 56 148 96 195 131 387), lower := (rows 97 259 14 56 148 96 64 128 256), losses := [] }

theorem u28520 : Upper (D 7) (R 7) [96,257,10,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28521 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 259 14 56 148 160 67 195 323), lower := (rows 97 259 14 56 148 160 64 128 256), losses := [] }

theorem u28521 : Upper (D 7) (R 7) [96,257,10,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28522 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 259 14 56 208 33 198 134 390), lower := (rows 97 259 14 56 208 33 64 128 256), losses := [] }

theorem u28522 : Upper (D 7) (R 7) [96,257,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28523 : Route 9 := (fun mask => (mask,id))

def c28523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28523 : Upper (D 7) (R 7) [96,257,10,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,192,2] 13 (by decide) (choices 1) [1,4,128] r28523 c28523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10750
  · exact u10751
  · exact u10752

def b28524 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 97 259 14 56 208 36 195 131 387), lower := (rows 97 259 14 56 208 36 64 128 256), losses := [] }

theorem u28524 : Upper (D 7) (R 7) [96,257,10,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28524 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28525 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 259 14 56 208 160 71 135 263), lower := (rows 97 259 14 56 208 160 64 128 256), losses := [] }

theorem u28525 : Upper (D 7) (R 7) [96,257,10,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28526 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 48, targets := 192 },{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(4,6),(4,7)], upper := (rows 97 259 14 137 50 36 208 208 464), lower := (rows 97 259 14 137 50 36 64 128 256), losses := [] }

theorem u28526 : Upper (D 7) (R 7) [96,257,10,129,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28526 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28527 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 137 50 48 196 196 452), lower := (rows 97 259 14 137 50 48 64 128 256), losses := [] }

theorem u28527 : Upper (D 7) (R 7) [96,257,10,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28527 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28528 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 137 50 96 212 148 404), lower := (rows 97 259 14 137 50 96 64 128 256), losses := [] }

theorem u28528 : Upper (D 7) (R 7) [96,257,10,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28529 : Route 9 := (fun mask => (mask,id))

def c28529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28529 : Upper (D 7) (R 7) [96,257,10,129,34,128] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,34,128] 13 (by decide) (choices 1) [4,16] r28529 c28529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10753
  · exact u10754

def b28530 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 48, targets := 192 },{ cop := 4, region := 201, targets := 2 }], pairs := [(0,1),(3,1),(4,6),(4,7)], upper := (rows 97 259 14 137 52 34 208 208 464), lower := (rows 97 259 14 137 52 34 64 128 256), losses := [] }

theorem u28530 : Upper (D 7) (R 7) [96,257,10,129,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28531 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 137 52 48 194 194 450), lower := (rows 97 259 14 137 52 48 64 128 256), losses := [] }

theorem u28531 : Upper (D 7) (R 7) [96,257,10,129,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28531 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28532 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 137 52 96 210 146 402), lower := (rows 97 259 14 137 52 96 64 128 256), losses := [] }

theorem u28532 : Upper (D 7) (R 7) [96,257,10,129,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28533 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 2, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 97 259 14 137 52 160 82 210 338), lower := (rows 97 259 14 137 52 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 97 257 60 169 52 160 64 160 256) }] }

theorem u28533 : Upper (D 7) (R 7) [96,257,10,129,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28534 : Route 9 := (fun mask => (mask,id))

def c28534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28534 : Upper (D 7) (R 7) [96,257,10,129,130,4] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,130,4] 13 (by decide) (choices 1) [16,32] r28534 c28534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10755
  · exact u10756

theorem m28535_4 : Upper (D 7) (R 7) [96,257,10,129,130,16,4] 13 :=
  permutation_upper _ _ _ [96,257,10,129,130,4,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10755

def r28535 : Route 9 := (fun mask => (mask,id))

def c28535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28535 : Upper (D 7) (R 7) [96,257,10,129,130,16] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,130,16] 13 (by decide) (choices 1) [4,32] r28535 c28535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28535_4
  · exact u10757

def b28536 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 137 146 96 116 180 308), lower := (rows 97 259 14 137 146 96 64 128 256), losses := [] }

theorem u28536 : Upper (D 7) (R 7) [96,257,10,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28537 : Route 9 := (fun mask => (mask,id))

def c28537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28537 : Upper (D 7) (R 7) [96,257,10,129,132,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,132,2] 13 (by decide) (choices 1) [16,32] r28537 c28537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10758
  · exact u10759

def b28538 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 2, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(4,0)], upper := (rows 97 259 14 137 148 48 98 226 354), lower := (rows 97 259 14 137 148 48 64 128 256), losses := [] }

theorem u28538 : Upper (D 7) (R 7) [96,257,10,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28538 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28539 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 137 148 96 114 178 306), lower := (rows 97 259 14 137 148 96 64 128 256), losses := [] }

theorem u28539 : Upper (D 7) (R 7) [96,257,10,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28540 : Route 9 := (fun mask => (mask,id))

def c28540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28540 : Upper (D 7) (R 7) [96,257,10,129,160,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,129,160,2] 13 (by decide) (choices 1) [4,16] r28540 c28540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10760
  · exact u10761

def b28541 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 2, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(4,0)], upper := (rows 97 259 14 137 176 36 82 210 338), lower := (rows 97 259 14 137 176 36 64 128 256), losses := [] }

theorem u28541 : Upper (D 7) (R 7) [96,257,10,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28541 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28542 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 137 176 48 70 198 326), lower := (rows 97 259 14 137 176 48 64 128 256), losses := [] }

theorem u28542 : Upper (D 7) (R 7) [96,257,10,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28542 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28543 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 137 176 96 86 150 278), lower := (rows 97 259 14 137 176 96 64 128 256), losses := [] }

theorem u28543 : Upper (D 7) (R 7) [96,257,10,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28544 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 259 14 140 50 33 208 208 464), lower := (rows 97 259 14 140 50 33 64 128 256), losses := [] }

theorem u28544 : Upper (D 7) (R 7) [96,257,10,132,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28545 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 140 50 48 193 193 449), lower := (rows 97 259 14 140 50 48 64 128 256), losses := [] }

theorem u28545 : Upper (D 7) (R 7) [96,257,10,132,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28545 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28546 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 140 50 96 209 145 401), lower := (rows 97 259 14 140 50 96 64 128 256), losses := [] }

theorem u28546 : Upper (D 7) (R 7) [96,257,10,132,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28547 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 4, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 97 259 14 140 50 160 81 209 337), lower := (rows 97 259 14 140 50 160 64 128 256), losses := [] }

theorem u28547 : Upper (D 7) (R 7) [96,257,10,132,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28548 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 259 14 140 145 34 112 240 368), lower := (rows 97 259 14 140 145 34 64 128 256), losses := [] }

theorem u28548 : Upper (D 7) (R 7) [96,257,10,132,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28549_2 : Upper (D 7) (R 7) [96,257,10,132,129,16,2] 13 :=
  permutation_upper _ _ _ [96,257,10,132,129,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10762

def r28549 : Route 9 := (fun mask => (mask,id))

def c28549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28549 : Upper (D 7) (R 7) [96,257,10,132,129,16] 13 := by
  apply FastRouting.sound _ _ [96,257,10,132,129,16] 13 (by decide) (choices 1) [2,32] r28549 c28549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28549_2
  · exact u10763

def b28550 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 140 145 96 114 178 306), lower := (rows 97 259 14 140 145 96 64 128 256), losses := [] }

theorem u28550 : Upper (D 7) (R 7) [96,257,10,132,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28551 : Route 9 := (fun mask => (mask,id))

def c28551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28551 : Upper (D 7) (R 7) [96,257,10,132,160,1] 13 := by
  apply FastRouting.sound _ _ [96,257,10,132,160,1] 13 (by decide) (choices 1) [2,16] r28551 c28551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10764
  · exact u10765

def b28552 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 259 14 140 176 34 81 209 337), lower := (rows 97 259 14 140 176 34 64 128 256), losses := [] }

theorem u28552 : Upper (D 7) (R 7) [96,257,10,132,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28553 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 140 176 48 67 195 323), lower := (rows 97 259 14 140 176 48 64 128 256), losses := [] }

theorem u28553 : Upper (D 7) (R 7) [96,257,10,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28553 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28554 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 140 176 96 83 147 275), lower := (rows 97 259 14 140 176 96 64 128 256), losses := [] }

theorem u28554 : Upper (D 7) (R 7) [96,257,10,132,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28555 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 204, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 259 14 152 50 33 196 196 452), lower := (rows 97 259 14 152 50 33 64 128 256), losses := [] }

theorem u28555 : Upper (D 7) (R 7) [96,257,10,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28556 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 48, targets := 193 }], pairs := [(4,0),(4,6),(4,7)], upper := (rows 97 259 14 152 50 36 193 193 449), lower := (rows 97 259 14 152 50 36 64 128 256), losses := [] }

theorem u28556 : Upper (D 7) (R 7) [96,257,10,144,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28556 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28557 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 152 50 96 197 133 389), lower := (rows 97 259 14 152 50 96 64 128 256), losses := [] }

theorem u28557 : Upper (D 7) (R 7) [96,257,10,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28558 : Route 9 := (fun mask => (mask,id))

def c28558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28558 : Upper (D 7) (R 7) [96,257,10,144,34,128] 13 := by
  apply FastRouting.sound _ _ [96,257,10,144,34,128] 13 (by decide) (choices 1) [1,4] r28558 c28558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10766
  · exact u10767

def b28559 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(3,0)], upper := (rows 97 259 14 152 52 33 194 194 450), lower := (rows 97 259 14 152 52 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 70 134 262), good := (rows 96 450 462 152 508 32 64 128 256) }] }

theorem u28559 : Upper (D 7) (R 7) [96,257,10,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28559
end Delivery.IrregularNine14.P07
