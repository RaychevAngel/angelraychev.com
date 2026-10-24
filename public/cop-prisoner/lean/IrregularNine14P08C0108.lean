import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0013

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6480 : Route 9 := (fun mask => (mask,id))

def c6480 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6480 : Upper (D 8) (R 8) [288,12,65,160,129,64] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160,129,64] 13 (by decide) (choices 1) [2,16,32] r6480 c6480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u824
  · exact u825
  · exact u826

def b6481 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 168 208 33 114 178 306), lower := (rows 289 14 69 168 208 33 64 128 256), losses := [] }

theorem u6481 : Upper (D 8) (R 8) [288,12,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6482 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 14 69 168 208 34 113 177 305), lower := (rows 289 14 69 168 208 34 64 128 256), losses := [] }

theorem u6482 : Upper (D 8) (R 8) [288,12,65,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6482 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6483 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 289 14 69 168 208 48 99 163 291), lower := (rows 289 14 69 168 208 48 64 128 256), losses := [] }

theorem u6483 : Upper (D 8) (R 8) [288,12,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6483 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6484 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 50 33 193 193 449), lower := (rows 289 14 84 168 50 33 64 128 256), losses := [] }

theorem u6484 : Upper (D 8) (R 8) [288,12,80,160,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6485 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 50 96 193 129 385), lower := (rows 289 14 84 168 50 96 64 128 256), losses := [] }

theorem u6485 : Upper (D 8) (R 8) [288,12,80,160,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6486 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 84 168 50 160 65 193 321), lower := (rows 289 14 84 168 50 160 64 128 256), losses := [] }

theorem u6486 : Upper (D 8) (R 8) [288,12,80,160,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6487 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 168 81 33 210 146 402), lower := (rows 289 14 100 168 81 33 64 128 256), losses := [] }

theorem u6487 : Upper (D 8) (R 8) [288,12,96,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6488 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 14 100 168 81 34 209 145 401), lower := (rows 289 14 100 168 81 34 64 128 256), losses := [] }

theorem u6488 : Upper (D 8) (R 8) [288,12,96,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6488 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6489 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 14 100 168 81 48 195 131 387), lower := (rows 289 14 100 168 81 48 64 128 256), losses := [] }

theorem u6489 : Upper (D 8) (R 8) [288,12,96,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6489 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6490 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 100 168 81 160 83 147 275), lower := (rows 289 14 100 168 81 160 64 128 256), losses := [] }

theorem u6490 : Upper (D 8) (R 8) [288,12,96,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6491 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 168 208 33 83 147 275), lower := (rows 289 14 100 168 208 33 64 128 256), losses := [] }

theorem u6491 : Upper (D 8) (R 8) [288,12,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6492 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 14 100 168 208 34 81 145 273), lower := (rows 289 14 100 168 208 34 64 128 256), losses := [] }

theorem u6492 : Upper (D 8) (R 8) [288,12,96,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6492 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6493 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 14 100 168 208 48 67 131 259), lower := (rows 289 14 100 168 208 48 64 128 256), losses := [] }

theorem u6493 : Upper (D 8) (R 8) [288,12,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6493 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6494 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 289 38 69 56 145 34 200 200 456), lower := (rows 289 38 69 56 145 34 64 128 256), losses := [] }

theorem u6494 : Upper (D 8) (R 8) [288,36,65,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6494 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6495 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 56 145 96 202 138 394), lower := (rows 289 38 69 56 145 96 64 128 256), losses := [] }

theorem u6495 : Upper (D 8) (R 8) [288,36,65,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6496 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 56 146 33 200 200 456), lower := (rows 289 38 69 56 146 33 64 128 256), losses := [] }

theorem u6496 : Upper (D 8) (R 8) [288,36,65,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6497 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 38 69 56 146 40 193 193 449), lower := (rows 289 38 69 56 146 40 64 128 256), losses := [] }

theorem u6497 : Upper (D 8) (R 8) [288,36,65,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6497 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6498 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 56 146 96 201 137 393), lower := (rows 289 38 69 56 146 96 64 128 256), losses := [] }

theorem u6498 : Upper (D 8) (R 8) [288,36,65,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6499 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 69 56 146 160 73 201 329), lower := (rows 289 38 69 56 146 160 64 128 256), losses := [] }

theorem u6499 : Upper (D 8) (R 8) [288,36,65,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6500 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 56 152 33 194 194 450), lower := (rows 289 38 69 56 152 33 64 128 256), losses := [] }

theorem u6500 : Upper (D 8) (R 8) [288,36,65,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6501 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 38 69 56 152 34 193 193 449), lower := (rows 289 38 69 56 152 34 64 128 256), losses := [] }

theorem u6501 : Upper (D 8) (R 8) [288,36,65,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6501 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6502 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 56 152 96 195 131 387), lower := (rows 289 38 69 56 152 96 64 128 256), losses := [] }

theorem u6502 : Upper (D 8) (R 8) [288,36,65,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6503 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 56 152 160 67 195 323), lower := (rows 289 38 69 56 152 160 64 128 256), losses := [] }

theorem u6503 : Upper (D 8) (R 8) [288,36,65,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6504 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 56 208 33 202 138 394), lower := (rows 289 38 69 56 208 33 64 128 256), losses := [] }

theorem u6504 : Upper (D 8) (R 8) [288,36,65,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6505 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 38 69 56 208 34 201 137 393), lower := (rows 289 38 69 56 208 34 64 128 256), losses := [] }

theorem u6505 : Upper (D 8) (R 8) [288,36,65,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6505 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6506 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 38 69 56 208 40 195 131 387), lower := (rows 289 38 69 56 208 40 64 128 256), losses := [] }

theorem u6506 : Upper (D 8) (R 8) [288,36,65,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6506 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6507 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 69 56 208 160 75 139 267), lower := (rows 289 38 69 56 208 160 64 128 256), losses := [] }

theorem u6507 : Upper (D 8) (R 8) [288,36,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6508 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 289 38 69 88 145 34 232 168 424), lower := (rows 289 38 69 88 145 34 64 128 256), losses := [] }

theorem u6508 : Upper (D 8) (R 8) [288,36,65,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6508 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6509 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 38 69 88 145 40 226 162 418), lower := (rows 289 38 69 88 145 40 64 128 256), losses := [] }

theorem u6509 : Upper (D 8) (R 8) [288,36,65,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6509 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6510 : Route 9 := (fun mask => (mask,id))

def c6510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6510 : Upper (D 8) (R 8) [288,36,65,80,129,128] 13 := by
  apply FastRouting.sound _ _ [288,36,65,80,129,128] 13 (by decide) (choices 1) [2,8,32] r6510 c6510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u827
  · exact u828
  · exact u829

def b6511 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 88 176 33 202 138 394), lower := (rows 289 38 69 88 176 33 64 128 256), losses := [] }

theorem u6511 : Upper (D 8) (R 8) [288,36,65,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6512 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 38 69 88 176 34 201 137 393), lower := (rows 289 38 69 88 176 34 64 128 256), losses := [] }

theorem u6512 : Upper (D 8) (R 8) [288,36,65,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6512 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6513 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 38 69 88 176 40 195 131 387), lower := (rows 289 38 69 88 176 40 64 128 256), losses := [] }

theorem u6513 : Upper (D 8) (R 8) [288,36,65,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6513 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6514 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 69 88 176 160 75 139 267), lower := (rows 289 38 69 88 176 160 64 128 256), losses := [] }

theorem u6514 : Upper (D 8) (R 8) [288,36,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6515 : PairBound 9 := { available := 152, camps := [], pairs := [], upper := (rows 289 38 69 104 145 34 216 152 408), lower := (rows 289 38 69 104 145 34 64 128 256), losses := [] }

theorem u6515 : Upper (D 8) (R 8) [288,36,65,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6515 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6516 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 289 38 69 104 145 40 210 146 402), lower := (rows 289 38 69 104 145 40 64 128 256), losses := [] }

theorem u6516 : Upper (D 8) (R 8) [288,36,65,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6516 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6517 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 289 38 69 104 145 48 202 138 394), lower := (rows 289 38 69 104 145 48 64 128 256), losses := [] }

theorem u6517 : Upper (D 8) (R 8) [288,36,65,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6517 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6518 : Route 9 := (fun mask => (mask,id))

def c6518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6518 : Upper (D 8) (R 8) [288,36,65,96,129,128] 13 := by
  apply FastRouting.sound _ _ [288,36,65,96,129,128] 13 (by decide) (choices 1) [2,8,16] r6518 c6518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u830
  · exact u831
  · exact u832

def b6519 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 104 146 33 216 152 408), lower := (rows 289 38 69 104 146 33 64 128 256), losses := [] }

theorem u6519 : Upper (D 8) (R 8) [288,36,65,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6520 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 38 69 104 146 40 209 145 401), lower := (rows 289 38 69 104 146 40 64 128 256), losses := [] }

theorem u6520 : Upper (D 8) (R 8) [288,36,65,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6520 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6521 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 38 69 104 146 48 201 137 393), lower := (rows 289 38 69 104 146 48 64 128 256), losses := [] }

theorem u6521 : Upper (D 8) (R 8) [288,36,65,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6521 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6522 : Route 9 := (fun mask => (mask,id))

def c6522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6522 : Upper (D 8) (R 8) [288,36,65,96,130,128] 13 := by
  apply FastRouting.sound _ _ [288,36,65,96,130,128] 13 (by decide) (choices 1) [1,8,16] r6522 c6522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u833
  · exact u834
  · exact u835

def b6523 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 104 152 33 210 146 402), lower := (rows 289 38 69 104 152 33 64 128 256), losses := [] }

theorem u6523 : Upper (D 8) (R 8) [288,36,65,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6524 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 38 69 104 152 34 209 145 401), lower := (rows 289 38 69 104 152 34 64 128 256), losses := [] }

theorem u6524 : Upper (D 8) (R 8) [288,36,65,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6524 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6525 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 38 69 104 152 48 195 131 387), lower := (rows 289 38 69 104 152 48 64 128 256), losses := [] }

theorem u6525 : Upper (D 8) (R 8) [288,36,65,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6525 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6526 : Route 9 := (fun mask => (mask,id))

def c6526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6526 : Upper (D 8) (R 8) [288,36,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [288,36,65,96,136,128] 13 (by decide) (choices 1) [1,2,16] r6526 c6526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u836
  · exact u837
  · exact u838

def b6527 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 289 38 69 137 146 40 112 240 368), lower := (rows 289 38 69 137 146 40 64 128 256), losses := [] }

theorem u6527 : Upper (D 8) (R 8) [288,36,65,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6527 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6528 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 289 38 69 137 146 48 104 232 360), lower := (rows 289 38 69 137 146 48 64 128 256), losses := [] }

theorem u6528 : Upper (D 8) (R 8) [288,36,65,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6528 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6529 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 137 146 96 120 184 312), lower := (rows 289 38 69 137 146 96 64 128 256), losses := [] }

theorem u6529 : Upper (D 8) (R 8) [288,36,65,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6530 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 289 38 69 137 176 34 88 216 344), lower := (rows 289 38 69 137 176 34 64 128 256), losses := [] }

theorem u6530 : Upper (D 8) (R 8) [288,36,65,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6530 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6531 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 289 38 69 137 176 40 82 210 338), lower := (rows 289 38 69 137 176 40 64 128 256), losses := [] }

theorem u6531 : Upper (D 8) (R 8) [288,36,65,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6531 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6532 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 289 38 69 137 176 48 74 202 330), lower := (rows 289 38 69 137 176 48 64 128 256), losses := [] }

theorem u6532 : Upper (D 8) (R 8) [288,36,65,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6532 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6533 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 137 176 96 90 154 282), lower := (rows 289 38 69 137 176 96 64 128 256), losses := [] }

theorem u6533 : Upper (D 8) (R 8) [288,36,65,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6534 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 289 38 69 137 208 34 120 184 312), lower := (rows 289 38 69 137 208 34 64 128 256), losses := [] }

theorem u6534 : Upper (D 8) (R 8) [288,36,65,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6534 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6535 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 289 38 69 137 208 40 114 178 306), lower := (rows 289 38 69 137 208 40 64 128 256), losses := [] }

theorem u6535 : Upper (D 8) (R 8) [288,36,65,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6535 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6536 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 289 38 69 137 208 48 106 170 298), lower := (rows 289 38 69 137 208 48 64 128 256), losses := [] }

theorem u6536 : Upper (D 8) (R 8) [288,36,65,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6536 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6537 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 138 176 33 88 216 344), lower := (rows 289 38 69 138 176 33 64 128 256), losses := [] }

theorem u6537 : Upper (D 8) (R 8) [288,36,65,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6538 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 38 69 138 176 40 81 209 337), lower := (rows 289 38 69 138 176 40 64 128 256), losses := [] }

theorem u6538 : Upper (D 8) (R 8) [288,36,65,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6538 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6539 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 289 38 69 138 176 48 73 201 329), lower := (rows 289 38 69 138 176 48 64 128 256), losses := [] }

theorem u6539 : Upper (D 8) (R 8) [288,36,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6539 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6539
end Delivery.IrregularNine14.P08
