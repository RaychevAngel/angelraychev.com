import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0080
import IrregularNine14P08C0081

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14520 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 137 280 178 242 178 434), lower := (rows 97 38 69 137 280 32 64 128 256), losses := [] }

theorem u14520 : Upper (D 8) (R 8) [96,36,65,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14521 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 137 304 186 218 154 410), lower := (rows 97 38 69 137 304 32 64 128 256), losses := [] }

theorem u14521 : Upper (D 8) (R 8) [96,36,65,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14522 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 137 400 58 122 186 314), lower := (rows 97 38 69 137 400 32 64 128 256), losses := [] }

theorem u14522 : Upper (D 8) (R 8) [96,36,65,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14523 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 138 176 313 345 409 281), lower := (rows 97 38 69 138 176 32 64 128 256), losses := [] }

theorem u14523 : Upper (D 8) (R 8) [96,36,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14524 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 138 273 184 248 184 440), lower := (rows 97 38 69 138 273 32 64 128 256), losses := [] }

theorem u14524 : Upper (D 8) (R 8) [96,36,65,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14525 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 138 280 177 241 177 433), lower := (rows 97 38 69 138 280 32 64 128 256), losses := [] }

theorem u14525 : Upper (D 8) (R 8) [96,36,65,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14526 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 138 304 185 217 153 409), lower := (rows 97 38 69 138 304 32 64 128 256), losses := [] }

theorem u14526 : Upper (D 8) (R 8) [96,36,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14527 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 138 400 57 121 185 313), lower := (rows 97 38 69 138 400 32 64 128 256), losses := [] }

theorem u14527 : Upper (D 8) (R 8) [96,36,65,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14528 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 152 273 170 234 170 426), lower := (rows 97 38 69 152 273 32 64 128 256), losses := [] }

theorem u14528 : Upper (D 8) (R 8) [96,36,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14529 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 152 274 169 233 169 425), lower := (rows 97 38 69 152 274 32 64 128 256), losses := [] }

theorem u14529 : Upper (D 8) (R 8) [96,36,65,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14530 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 152 280 163 227 163 419), lower := (rows 97 38 69 152 280 32 64 128 256), losses := [] }

theorem u14530 : Upper (D 8) (R 8) [96,36,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14531 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 152 304 171 203 139 395), lower := (rows 97 38 69 152 304 32 64 128 256), losses := [] }

theorem u14531 : Upper (D 8) (R 8) [96,36,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14532 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 168 273 186 218 154 410), lower := (rows 97 38 69 168 273 32 64 128 256), losses := [] }

theorem u14532 : Upper (D 8) (R 8) [96,36,65,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14533 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 168 274 185 217 153 409), lower := (rows 97 38 69 168 274 32 64 128 256), losses := [] }

theorem u14533 : Upper (D 8) (R 8) [96,36,65,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14534 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 168 280 179 211 147 403), lower := (rows 97 38 69 168 280 32 64 128 256), losses := [] }

theorem u14534 : Upper (D 8) (R 8) [96,36,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14535 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 168 400 59 91 155 283), lower := (rows 97 38 69 168 400 32 64 128 256), losses := [] }

theorem u14535 : Upper (D 8) (R 8) [96,36,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14536 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 56 145 425 457 393 393), lower := (rows 97 38 70 56 145 32 64 128 256), losses := [] }

theorem u14536 : Upper (D 8) (R 8) [96,36,66,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14537 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 56 152 417 449 385 385), lower := (rows 97 38 70 56 152 32 64 128 256), losses := [] }

theorem u14537 : Upper (D 8) (R 8) [96,36,66,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14538 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 56 273 169 201 137 393), lower := (rows 97 38 70 56 273 32 64 128 256), losses := [] }

theorem u14538 : Upper (D 8) (R 8) [96,36,66,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14539 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 56 280 161 193 129 385), lower := (rows 97 38 70 56 280 32 64 128 256), losses := [] }

theorem u14539 : Upper (D 8) (R 8) [96,36,66,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14540 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 56 400 169 201 137 393), lower := (rows 97 38 70 56 400 32 64 128 256), losses := [] }

theorem u14540 : Upper (D 8) (R 8) [96,36,66,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14541 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 176 313 345 409 281), lower := (rows 97 38 70 137 176 32 64 128 256), losses := [] }

theorem u14541 : Upper (D 8) (R 8) [96,36,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14542 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 273 184 248 184 440), lower := (rows 97 38 70 137 273 32 64 128 256), losses := [] }

theorem u14542 : Upper (D 8) (R 8) [96,36,66,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14543 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 280 177 241 177 433), lower := (rows 97 38 70 137 280 32 64 128 256), losses := [] }

theorem u14543 : Upper (D 8) (R 8) [96,36,66,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14544 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 304 185 217 153 409), lower := (rows 97 38 70 137 304 32 64 128 256), losses := [] }

theorem u14544 : Upper (D 8) (R 8) [96,36,66,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14545 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 400 57 121 185 313), lower := (rows 97 38 70 137 400 32 64 128 256), losses := [] }

theorem u14545 : Upper (D 8) (R 8) [96,36,66,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14546 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 152 273 169 233 169 425), lower := (rows 97 38 70 152 273 32 64 128 256), losses := [] }

theorem u14546 : Upper (D 8) (R 8) [96,36,66,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14547 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 152 280 161 225 161 417), lower := (rows 97 38 70 152 280 32 64 128 256), losses := [] }

theorem u14547 : Upper (D 8) (R 8) [96,36,66,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14548 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 152 304 169 201 137 393), lower := (rows 97 38 70 152 304 32 64 128 256), losses := [] }

theorem u14548 : Upper (D 8) (R 8) [96,36,66,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14549 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 168 273 185 217 153 409), lower := (rows 97 38 70 168 273 32 64 128 256), losses := [] }

theorem u14549 : Upper (D 8) (R 8) [96,36,66,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14550 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 168 280 177 209 145 401), lower := (rows 97 38 70 168 280 32 64 128 256), losses := [] }

theorem u14550 : Upper (D 8) (R 8) [96,36,66,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14551 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 168 400 57 89 153 281), lower := (rows 97 38 70 168 400 32 64 128 256), losses := [] }

theorem u14551 : Upper (D 8) (R 8) [96,36,66,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14552 : Route 9 := (fun mask => (mask,id))

def c14552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u14552 : Upper (D 8) (R 8) [96,36,72,48,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,48,129] 13 (by decide) (choices 1) [1,2,128,256] r14552 c14552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4852
  · exact u4853
  · exact u4854
  · exact u4855

def r14553 : Route 9 := (fun mask => (mask,id))

def c14553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u14553 : Upper (D 8) (R 8) [96,36,72,48,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,48,130] 13 (by decide) (choices 1) [1,128,256] r14553 c14553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4856
  · exact u4857
  · exact u4858

def r14554 : Route 9 := (fun mask => (mask,id))

def c14554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14554 : Upper (D 8) (R 8) [96,36,72,48,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,48,257] 13 (by decide) (choices 1) [1,2,128] r14554 c14554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4859
  · exact u4860
  · exact u4861

def r14555 : Route 9 := (fun mask => (mask,id))

def c14555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14555 : Upper (D 8) (R 8) [96,36,72,48,258] 13 := by
  apply FastRouting.sound _ _ [96,36,72,48,258] 13 (by decide) (choices 1) [1,128] r14555 c14555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4862
  · exact u4863

def r14556 : Route 9 := (fun mask => (mask,id))

def c14556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14556 : Upper (D 8) (R 8) [96,36,72,48,384] 13 := by
  apply FastRouting.sound _ _ [96,36,72,48,384] 13 (by decide) (choices 1) [1,2,128] r14556 c14556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4864
  · exact u4865
  · exact u4866

def b14557 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 76 137 145 306 370 434 306), lower := (rows 97 38 76 137 145 32 64 128 256), losses := [] }

theorem u14557 : Upper (D 8) (R 8) [96,36,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14558 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 146 305 369 433 305), lower := (rows 97 38 76 137 146 32 64 128 256), losses := [] }

theorem u14558 : Upper (D 8) (R 8) [96,36,72,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14559 : Route 9 := (fun mask => (mask,id))

def c14559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u14559 : Upper (D 8) (R 8) [96,36,72,129,160] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,160] 13 (by decide) (choices 1) [1,2,16,256] r14559 c14559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4867
  · exact u4868
  · exact u4869
  · exact u4870

def r14560 : Route 9 := (fun mask => (mask,id))

def c14560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14560 : Upper (D 8) (R 8) [96,36,72,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,257] 13 (by decide) (choices 1) [2,16,128] r14560 c14560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4871
  · exact u4872
  · exact u4873

def r14561 : Route 9 := (fun mask => (mask,id))

def c14561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14561 : Upper (D 8) (R 8) [96,36,72,129,258] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,258] 13 (by decide) (choices 1) [1,16,128] r14561 c14561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4874
  · exact u4875
  · exact u4876

def r14562 : Route 9 := (fun mask => (mask,id))

def c14562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14562 : Upper (D 8) (R 8) [96,36,72,129,288] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,288] 13 (by decide) (choices 1) [1,2,16,128] r14562 c14562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4877
  · exact u4878
  · exact u4879
  · exact u4880

def r14563 : Route 9 := (fun mask => (mask,id))

def c14563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14563 : Upper (D 8) (R 8) [96,36,72,129,384] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,384] 13 (by decide) (choices 1) [1,2,16] r14563 c14563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4881
  · exact u4882
  · exact u4883

def b14564 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 76 138 145 305 369 433 305), lower := (rows 97 38 76 138 145 32 64 128 256), losses := [] }

theorem u14564 : Upper (D 8) (R 8) [96,36,72,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14565 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 76 138 176 305 337 401 273), lower := (rows 97 38 76 138 176 32 64 128 256), losses := [] }

theorem u14565 : Upper (D 8) (R 8) [96,36,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14566 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 76 138 273 177 241 177 433), lower := (rows 97 38 76 138 273 32 64 128 256), losses := [] }

theorem u14566 : Upper (D 8) (R 8) [96,36,72,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14567 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 76 138 304 177 209 145 401), lower := (rows 97 38 76 138 304 32 64 128 256), losses := [] }

theorem u14567 : Upper (D 8) (R 8) [96,36,72,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14568 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 76 138 400 49 113 177 305), lower := (rows 97 38 76 138 400 32 64 128 256), losses := [] }

theorem u14568 : Upper (D 8) (R 8) [96,36,72,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14569 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 145 291 355 419 291), lower := (rows 97 38 76 152 145 32 64 128 256), losses := [] }

theorem u14569 : Upper (D 8) (R 8) [96,36,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14570 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 146 289 353 417 289), lower := (rows 97 38 76 152 146 32 64 128 256), losses := [] }

theorem u14570 : Upper (D 8) (R 8) [96,36,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14571 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 176 291 323 387 259), lower := (rows 97 38 76 152 176 32 64 128 256), losses := [] }

theorem u14571 : Upper (D 8) (R 8) [96,36,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14572 : Route 9 := (fun mask => (mask,id))

def c14572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14572 : Upper (D 8) (R 8) [96,36,72,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,257] 13 (by decide) (choices 1) [1,2,128] r14572 c14572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4884
  · exact u4885
  · exact u4886

def r14573 : Route 9 := (fun mask => (mask,id))

def c14573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14573 : Upper (D 8) (R 8) [96,36,72,144,258] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,258] 13 (by decide) (choices 1) [1,128] r14573 c14573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4887
  · exact u4888

def r14574 : Route 9 := (fun mask => (mask,id))

def c14574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14574 : Upper (D 8) (R 8) [96,36,72,144,288] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,288] 13 (by decide) (choices 1) [1,2,128] r14574 c14574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4889
  · exact u4890
  · exact u4891

def b14575 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 400 35 99 163 291), lower := (rows 97 38 76 152 400 32 64 128 256), losses := [] }

theorem u14575 : Upper (D 8) (R 8) [96,36,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14576 : Route 9 := (fun mask => (mask,id))

def c14576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u14576 : Upper (D 8) (R 8) [96,36,72,160,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,160,129] 13 (by decide) (choices 1) [1,2,16,256] r14576 c14576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4892
  · exact u4893
  · exact u4894
  · exact u4895

def b14577 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 168 146 305 337 401 273), lower := (rows 97 38 76 168 146 32 64 128 256), losses := [] }

theorem u14577 : Upper (D 8) (R 8) [96,36,72,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14578 : Route 9 := (fun mask => (mask,id))

def c14578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14578 : Upper (D 8) (R 8) [96,36,72,160,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,160,257] 13 (by decide) (choices 1) [1,2,16,128] r14578 c14578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4896
  · exact u4897
  · exact u4898
  · exact u4899

def r14579 : Route 9 := (fun mask => (mask,id))

def c14579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14579 : Upper (D 8) (R 8) [96,36,72,160,258] 13 := by
  apply FastRouting.sound _ _ [96,36,72,160,258] 13 (by decide) (choices 1) [1,16,128] r14579 c14579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4900
  · exact u4901
  · exact u4902

#print axioms u14579
end Delivery.IrregularNine14.P08
