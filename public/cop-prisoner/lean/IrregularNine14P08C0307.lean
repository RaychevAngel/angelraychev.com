import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0113

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18420 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 14 84 137 145 34 98 162 290), lower := (rows 321 14 84 137 145 32 64 128 256), losses := [] }

theorem u18420 : Upper (D 8) (R 8) [320,12,80,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18421 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 84 137 146 33 97 161 289), lower := (rows 321 14 84 137 146 32 64 128 256), losses := [] }

theorem u18421 : Upper (D 8) (R 8) [320,12,80,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18422 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 84 137 176 35 99 163 291), lower := (rows 321 14 84 137 176 32 64 128 256), losses := [] }

theorem u18422 : Upper (D 8) (R 8) [320,12,80,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18423 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 84 138 49 161 225 161 417), lower := (rows 321 14 84 138 49 32 64 128 256), losses := [] }

theorem u18423 : Upper (D 8) (R 8) [320,12,80,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18424 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 84 138 145 33 97 161 289), lower := (rows 321 14 84 138 145 32 64 128 256), losses := [] }

theorem u18424 : Upper (D 8) (R 8) [320,12,80,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18425 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 84 138 176 33 97 161 289), lower := (rows 321 14 84 138 176 32 64 128 256), losses := [] }

theorem u18425 : Upper (D 8) (R 8) [320,12,80,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18426 : Route 9 := (fun mask => (mask,id))

def c18426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18426 : Upper (D 8) (R 8) [320,12,80,160,33] 13 := by
  apply FastRouting.sound _ _ [320,12,80,160,33] 13 (by decide) (choices 1) [1,2,128] r18426 c18426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6806
  · exact u6807
  · exact u6808

def b18427 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 84 168 50 161 225 161 417), lower := (rows 321 14 84 168 50 32 64 128 256), losses := [] }

theorem u18427 : Upper (D 8) (R 8) [320,12,80,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18428 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 84 168 145 35 99 163 291), lower := (rows 321 14 84 168 145 32 64 128 256), losses := [] }

theorem u18428 : Upper (D 8) (R 8) [320,12,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18429 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 84 168 146 33 97 161 289), lower := (rows 321 14 84 168 146 32 64 128 256), losses := [] }

theorem u18429 : Upper (D 8) (R 8) [320,12,80,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18430 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 84 168 176 35 99 163 291), lower := (rows 321 14 84 168 176 32 64 128 256), losses := [] }

theorem u18430 : Upper (D 8) (R 8) [320,12,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18431 : Route 9 := (fun mask => (mask,id))

def c18431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18431 : Upper (D 8) (R 8) [320,12,96,129,33] 13 := by
  apply FastRouting.sound _ _ [320,12,96,129,33] 13 (by decide) (choices 1) [2,16,128] r18431 c18431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6809
  · exact u6810
  · exact u6811

def r18432 : Route 9 := (fun mask => (mask,id))

def c18432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18432 : Upper (D 8) (R 8) [320,12,96,129,34] 13 := by
  apply FastRouting.sound _ _ [320,12,96,129,34] 13 (by decide) (choices 1) [1,16,128] r18432 c18432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6812
  · exact u6813
  · exact u6814

def b18433 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 14 100 137 145 50 114 178 306), lower := (rows 321 14 100 137 145 32 64 128 256), losses := [] }

theorem u18433 : Upper (D 8) (R 8) [320,12,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18434 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 137 146 49 113 177 305), lower := (rows 321 14 100 137 146 32 64 128 256), losses := [] }

theorem u18434 : Upper (D 8) (R 8) [320,12,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18435 : Route 9 := (fun mask => (mask,id))

def c18435 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18435 : Upper (D 8) (R 8) [320,12,96,129,160] 13 := by
  apply FastRouting.sound _ _ [320,12,96,129,160] 13 (by decide) (choices 1) [1,2,16] r18435 c18435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6815
  · exact u6816
  · exact u6817

def b18436 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 100 138 49 177 241 177 433), lower := (rows 321 14 100 138 49 32 64 128 256), losses := [] }

theorem u18436 : Upper (D 8) (R 8) [320,12,96,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18437 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 138 145 49 113 177 305), lower := (rows 321 14 100 138 145 32 64 128 256), losses := [] }

theorem u18437 : Upper (D 8) (R 8) [320,12,96,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18438 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 138 176 49 113 177 305), lower := (rows 321 14 100 138 176 32 64 128 256), losses := [] }

theorem u18438 : Upper (D 8) (R 8) [320,12,96,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18439 : Route 9 := (fun mask => (mask,id))

def c18439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18439 : Upper (D 8) (R 8) [320,12,96,144,33] 13 := by
  apply FastRouting.sound _ _ [320,12,96,144,33] 13 (by decide) (choices 1) [1,2,128] r18439 c18439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6818
  · exact u6819
  · exact u6820

def r18440 : Route 9 := (fun mask => (mask,id))

def c18440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18440 : Upper (D 8) (R 8) [320,12,96,144,34] 13 := by
  apply FastRouting.sound _ _ [320,12,96,144,34] 13 (by decide) (choices 1) [1,128] r18440 c18440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6821
  · exact u6822

def b18441 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 152 145 35 99 163 291), lower := (rows 321 14 100 152 145 32 64 128 256), losses := [] }

theorem u18441 : Upper (D 8) (R 8) [320,12,96,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18442 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 152 146 33 97 161 289), lower := (rows 321 14 100 152 146 32 64 128 256), losses := [] }

theorem u18442 : Upper (D 8) (R 8) [320,12,96,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18443 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 152 176 35 99 163 291), lower := (rows 321 14 100 152 176 32 64 128 256), losses := [] }

theorem u18443 : Upper (D 8) (R 8) [320,12,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18444 : Route 9 := (fun mask => (mask,id))

def c18444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18444 : Upper (D 8) (R 8) [320,12,96,160,33] 13 := by
  apply FastRouting.sound _ _ [320,12,96,160,33] 13 (by decide) (choices 1) [1,2,16,128] r18444 c18444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6823
  · exact u6824
  · exact u6825
  · exact u6826

def b18445 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 321 14 100 168 50 177 209 145 401), lower := (rows 321 14 100 168 50 32 64 128 256), losses := [] }

theorem u18445 : Upper (D 8) (R 8) [320,12,96,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18446 : Route 9 := (fun mask => (mask,id))

def c18446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18446 : Upper (D 8) (R 8) [320,12,96,160,129] 13 := by
  apply FastRouting.sound _ _ [320,12,96,160,129] 13 (by decide) (choices 1) [1,2,16] r18446 c18446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6827
  · exact u6828
  · exact u6829

def b18447 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 168 146 49 113 177 305), lower := (rows 321 14 100 168 146 32 64 128 256), losses := [] }

theorem u18447 : Upper (D 8) (R 8) [320,12,96,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18448 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 100 168 176 51 83 147 275), lower := (rows 321 14 100 168 176 32 64 128 256), losses := [] }

theorem u18448 : Upper (D 8) (R 8) [320,12,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18449 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 321 14 133 137 50 112 112 240 368), lower := (rows 321 14 133 137 50 32 64 128 256), losses := [] }

theorem u18449 : Upper (D 8) (R 8) [320,12,129,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18450 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 321 14 133 137 82 48 112 176 304), lower := (rows 321 14 133 137 82 32 64 128 256), losses := [] }

theorem u18450 : Upper (D 8) (R 8) [320,12,129,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18451 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 321 14 133 137 112 50 114 178 306), lower := (rows 321 14 133 137 112 32 64 128 256), losses := [] }

theorem u18451 : Upper (D 8) (R 8) [320,12,129,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18452 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 133 138 49 112 112 240 368), lower := (rows 321 14 133 138 49 32 64 128 256), losses := [] }

theorem u18452 : Upper (D 8) (R 8) [320,12,129,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18453 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 133 138 112 49 113 177 305), lower := (rows 321 14 133 138 112 32 64 128 256), losses := [] }

theorem u18453 : Upper (D 8) (R 8) [320,12,129,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18454 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 152 49 98 98 226 354), lower := (rows 321 14 133 152 49 32 64 128 256), losses := [] }

theorem u18454 : Upper (D 8) (R 8) [320,12,129,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18455 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 152 50 97 97 225 353), lower := (rows 321 14 133 152 50 32 64 128 256), losses := [] }

theorem u18455 : Upper (D 8) (R 8) [320,12,129,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18456 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 152 82 33 97 161 289), lower := (rows 321 14 133 152 82 32 64 128 256), losses := [] }

theorem u18456 : Upper (D 8) (R 8) [320,12,129,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18457 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 152 112 35 99 163 291), lower := (rows 321 14 133 152 112 32 64 128 256), losses := [] }

theorem u18457 : Upper (D 8) (R 8) [320,12,129,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18458 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 168 49 114 114 242 370), lower := (rows 321 14 133 168 49 32 64 128 256), losses := [] }

theorem u18458 : Upper (D 8) (R 8) [320,12,129,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18459 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 168 50 113 113 241 369), lower := (rows 321 14 133 168 50 32 64 128 256), losses := [] }

theorem u18459 : Upper (D 8) (R 8) [320,12,129,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18460 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 168 82 49 113 177 305), lower := (rows 321 14 133 168 82 32 64 128 256), losses := [] }

theorem u18460 : Upper (D 8) (R 8) [320,12,129,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18461 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 168 112 51 115 179 307), lower := (rows 321 14 133 168 112 32 64 128 256), losses := [] }

theorem u18461 : Upper (D 8) (R 8) [320,12,129,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18462 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 200 49 50 114 178 306), lower := (rows 321 14 133 200 49 32 64 128 256), losses := [] }

theorem u18462 : Upper (D 8) (R 8) [320,12,129,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18463 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 200 50 49 113 177 305), lower := (rows 321 14 133 200 50 32 64 128 256), losses := [] }

theorem u18463 : Upper (D 8) (R 8) [320,12,129,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18464 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 134 152 49 97 97 225 353), lower := (rows 321 14 134 152 49 32 64 128 256), losses := [] }

theorem u18464 : Upper (D 8) (R 8) [320,12,130,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18465 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 134 152 112 33 97 161 289), lower := (rows 321 14 134 152 112 32 64 128 256), losses := [] }

theorem u18465 : Upper (D 8) (R 8) [320,12,130,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18466 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 134 168 49 113 113 241 369), lower := (rows 321 14 134 168 49 32 64 128 256), losses := [] }

theorem u18466 : Upper (D 8) (R 8) [320,12,130,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18467 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 134 168 112 49 113 177 305), lower := (rows 321 14 134 168 112 32 64 128 256), losses := [] }

theorem u18467 : Upper (D 8) (R 8) [320,12,130,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18468 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 134 200 49 49 113 177 305), lower := (rows 321 14 134 200 49 32 64 128 256), losses := [] }

theorem u18468 : Upper (D 8) (R 8) [320,12,130,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18469 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 148 168 49 99 99 227 355), lower := (rows 321 14 148 168 49 32 64 128 256), losses := [] }

theorem u18469 : Upper (D 8) (R 8) [320,12,144,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18470 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 148 168 50 97 97 225 353), lower := (rows 321 14 148 168 50 32 64 128 256), losses := [] }

theorem u18470 : Upper (D 8) (R 8) [320,12,144,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18471 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 148 168 82 33 97 161 289), lower := (rows 321 14 148 168 82 32 64 128 256), losses := [] }

theorem u18471 : Upper (D 8) (R 8) [320,12,144,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18472 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 148 168 112 35 99 163 291), lower := (rows 321 14 148 168 112 32 64 128 256), losses := [] }

theorem u18472 : Upper (D 8) (R 8) [320,12,144,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18473 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 148 200 49 35 99 163 291), lower := (rows 321 14 148 200 49 32 64 128 256), losses := [] }

theorem u18473 : Upper (D 8) (R 8) [320,12,144,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18474 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 148 200 50 33 97 161 289), lower := (rows 321 14 148 200 50 32 64 128 256), losses := [] }

theorem u18474 : Upper (D 8) (R 8) [320,12,144,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18475 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 164 168 49 115 83 211 339), lower := (rows 321 14 164 168 49 32 64 128 256), losses := [] }

theorem u18475 : Upper (D 8) (R 8) [320,12,160,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18476 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 164 168 50 113 81 209 337), lower := (rows 321 14 164 168 50 32 64 128 256), losses := [] }

theorem u18476 : Upper (D 8) (R 8) [320,12,160,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18477 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 164 168 82 49 113 177 305), lower := (rows 321 14 164 168 82 32 64 128 256), losses := [] }

theorem u18477 : Upper (D 8) (R 8) [320,12,160,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18478 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 164 168 112 51 83 147 275), lower := (rows 321 14 164 168 112 32 64 128 256), losses := [] }

theorem u18478 : Upper (D 8) (R 8) [320,12,160,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18479 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 164 200 49 51 115 179 307), lower := (rows 321 14 164 200 49 32 64 128 256), losses := [] }

theorem u18479 : Upper (D 8) (R 8) [320,12,160,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18479
end Delivery.IrregularNine14.P08
