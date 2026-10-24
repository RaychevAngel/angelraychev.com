import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0091

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15600 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 37 265 82 176 240 176 432), lower := (rows 193 14 37 265 82 32 64 128 256), losses := [] }

theorem u15600 : Upper (D 8) (R 8) [192,12,33,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15601 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 37 265 112 178 242 178 434), lower := (rows 193 14 37 265 112 32 64 128 256), losses := [] }

theorem u15601 : Upper (D 8) (R 8) [192,12,33,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15602 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 37 266 49 240 240 240 496), lower := (rows 193 14 37 266 49 32 64 128 256), losses := [] }

theorem u15602 : Upper (D 8) (R 8) [192,12,33,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15603 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 266 81 176 240 176 432), lower := (rows 193 14 37 266 81 32 64 128 256), losses := [] }

theorem u15603 : Upper (D 8) (R 8) [192,12,33,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15604 : Route 9 := (fun mask => (mask,id))

def c15604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15604 : Upper (D 8) (R 8) [192,12,33,258,96] 13 := by
  apply FastRouting.sound _ _ [192,12,33,258,96] 13 (by decide) (choices 1) [1,16,128] r15604 c15604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5465
  · exact u5466
  · exact u5467

def b15605 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 37 266 208 49 113 177 305), lower := (rows 193 14 37 266 208 32 64 128 256), losses := [] }

theorem u15605 : Upper (D 8) (R 8) [192,12,33,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15606 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 37 280 49 226 226 226 482), lower := (rows 193 14 37 280 49 32 64 128 256), losses := [] }

theorem u15606 : Upper (D 8) (R 8) [192,12,33,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15607 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15607 : Upper (D 8) (R 8) [192,12,33,272,34] 13 := by
  apply FastRouting.sound _ _ [192,12,33,272,34] 13 (by decide) (choices 1) [1,64] r15607 c15607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5468
  · exact u5469

def b15608 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 280 81 162 226 162 418), lower := (rows 193 14 37 280 81 32 64 128 256), losses := [] }

theorem u15608 : Upper (D 8) (R 8) [192,12,33,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15609 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 280 82 161 225 161 417), lower := (rows 193 14 37 280 82 32 64 128 256), losses := [] }

theorem u15609 : Upper (D 8) (R 8) [192,12,33,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15610 : Route 9 := (fun mask => (mask,id))

def c15610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15610 : Upper (D 8) (R 8) [192,12,33,272,96] 13 := by
  apply FastRouting.sound _ _ [192,12,33,272,96] 13 (by decide) (choices 1) [1,2,128] r15610 c15610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5470
  · exact u5471
  · exact u5472

def b15611 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 37 280 208 35 99 163 291), lower := (rows 193 14 37 280 208 32 64 128 256), losses := [] }

theorem u15611 : Upper (D 8) (R 8) [192,12,33,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15612 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 37 296 49 242 210 210 466), lower := (rows 193 14 37 296 49 32 64 128 256), losses := [] }

theorem u15612 : Upper (D 8) (R 8) [192,12,33,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15613 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 193, targets := 32 }], pairs := [(0,5)], upper := (rows 193 14 37 296 50 241 209 209 465), lower := (rows 193 14 37 296 50 32 64 128 256), losses := [] }

theorem u15613 : Upper (D 8) (R 8) [192,12,33,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15614 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 296 81 178 242 178 434), lower := (rows 193 14 37 296 81 32 64 128 256), losses := [] }

theorem u15614 : Upper (D 8) (R 8) [192,12,33,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15615 : Route 9 := (fun mask => (mask,id))

def c15615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15615 : Upper (D 8) (R 8) [192,12,33,288,66] 13 := by
  apply FastRouting.sound _ _ [192,12,33,288,66] 13 (by decide) (choices 1) [1,16,128] r15615 c15615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5473
  · exact u5474
  · exact u5475

def r15616 : Route 9 := (fun mask => (mask,id))

def c15616 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15616 : Upper (D 8) (R 8) [192,12,33,288,96] 13 := by
  apply FastRouting.sound _ _ [192,12,33,288,96] 13 (by decide) (choices 1) [1,2,16,128] r15616 c15616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5476
  · exact u5477
  · exact u5478
  · exact u5479

def b15617 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 37 296 208 51 115 179 307), lower := (rows 193 14 37 296 208 32 64 128 256), losses := [] }

theorem u15617 : Upper (D 8) (R 8) [192,12,33,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15618 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 37 328 49 178 242 178 434), lower := (rows 193 14 37 328 49 32 64 128 256), losses := [] }

theorem u15618 : Upper (D 8) (R 8) [192,12,33,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15619 : Route 9 := (fun mask => (mask,id))

def c15619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15619 : Upper (D 8) (R 8) [192,12,33,320,34] 13 := by
  apply FastRouting.sound _ _ [192,12,33,320,34] 13 (by decide) (choices 1) [1,16,128] r15619 c15619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5480
  · exact u5481
  · exact u5482

def b15620 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 328 145 50 114 178 306), lower := (rows 193 14 37 328 145 32 64 128 256), losses := [] }

theorem u15620 : Upper (D 8) (R 8) [192,12,33,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15621 : Route 9 := (fun mask => (mask,id))

def c15621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15621 : Upper (D 8) (R 8) [192,12,33,320,130] 13 := by
  apply FastRouting.sound _ _ [192,12,33,320,130] 13 (by decide) (choices 1) [1,16] r15621 c15621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5483
  · exact u5484

def r15622 : Route 9 := (fun mask => (mask,id))

def c15622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15622 : Upper (D 8) (R 8) [192,12,33,320,160] 13 := by
  apply FastRouting.sound _ _ [192,12,33,320,160] 13 (by decide) (choices 1) [1,2,16] r15622 c15622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5485
  · exact u5486
  · exact u5487

def b15623 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 56 49 481 449 449 449), lower := (rows 193 14 38 56 49 32 64 128 256), losses := [] }

theorem u15623 : Upper (D 8) (R 8) [192,12,34,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15624 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 56 112 417 449 385 385), lower := (rows 193 14 38 56 112 32 64 128 256), losses := [] }

theorem u15624 : Upper (D 8) (R 8) [192,12,34,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15625 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 56 273 225 225 225 481), lower := (rows 193 14 38 56 273 32 64 128 256), losses := [] }

theorem u15625 : Upper (D 8) (R 8) [192,12,34,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15626 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 56 304 225 193 193 449), lower := (rows 193 14 38 56 304 32 64 128 256), losses := [] }

theorem u15626 : Upper (D 8) (R 8) [192,12,34,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15627 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 56 336 161 225 161 417), lower := (rows 193 14 38 56 336 32 64 128 256), losses := [] }

theorem u15627 : Upper (D 8) (R 8) [192,12,34,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15628 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 73 49 432 496 432 432), lower := (rows 193 14 38 73 49 32 64 128 256), losses := [] }

theorem u15628 : Upper (D 8) (R 8) [192,12,34,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15629 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 73 176 305 369 433 305), lower := (rows 193 14 38 73 176 32 64 128 256), losses := [] }

theorem u15629 : Upper (D 8) (R 8) [192,12,34,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15630 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 73 273 176 240 176 432), lower := (rows 193 14 38 73 273 32 64 128 256), losses := [] }

theorem u15630 : Upper (D 8) (R 8) [192,12,34,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15631 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 73 304 177 241 177 433), lower := (rows 193 14 38 73 304 32 64 128 256), losses := [] }

theorem u15631 : Upper (D 8) (R 8) [192,12,34,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15632 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 73 400 49 113 177 305), lower := (rows 193 14 38 73 400 32 64 128 256), losses := [] }

theorem u15632 : Upper (D 8) (R 8) [192,12,34,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15633 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 88 49 417 481 417 417), lower := (rows 193 14 38 88 49 32 64 128 256), losses := [] }

theorem u15633 : Upper (D 8) (R 8) [192,12,34,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15634 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 88 176 289 353 417 289), lower := (rows 193 14 38 88 176 32 64 128 256), losses := [] }

theorem u15634 : Upper (D 8) (R 8) [192,12,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15635 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 88 273 161 225 161 417), lower := (rows 193 14 38 88 273 32 64 128 256), losses := [] }

theorem u15635 : Upper (D 8) (R 8) [192,12,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15636 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 88 304 161 225 161 417), lower := (rows 193 14 38 88 304 32 64 128 256), losses := [] }

theorem u15636 : Upper (D 8) (R 8) [192,12,34,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15637 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 88 400 33 97 161 289), lower := (rows 193 14 38 88 400 32 64 128 256), losses := [] }

theorem u15637 : Upper (D 8) (R 8) [192,12,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15638 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 104 49 433 465 401 401), lower := (rows 193 14 38 104 49 32 64 128 256), losses := [] }

theorem u15638 : Upper (D 8) (R 8) [192,12,34,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15639 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 104 176 305 337 401 273), lower := (rows 193 14 38 104 176 32 64 128 256), losses := [] }

theorem u15639 : Upper (D 8) (R 8) [192,12,34,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15640 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 104 273 177 241 177 433), lower := (rows 193 14 38 104 273 32 64 128 256), losses := [] }

theorem u15640 : Upper (D 8) (R 8) [192,12,34,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15641 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 104 304 177 209 145 401), lower := (rows 193 14 38 104 304 32 64 128 256), losses := [] }

theorem u15641 : Upper (D 8) (R 8) [192,12,34,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15642 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 104 400 49 113 177 305), lower := (rows 193 14 38 104 400 32 64 128 256), losses := [] }

theorem u15642 : Upper (D 8) (R 8) [192,12,34,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15643 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 38 200 49 305 369 433 305), lower := (rows 193 14 38 200 49 32 64 128 256), losses := [] }

theorem u15643 : Upper (D 8) (R 8) [192,12,34,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15644 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 38 200 273 49 113 177 305), lower := (rows 193 14 38 200 273 32 64 128 256), losses := [] }

theorem u15644 : Upper (D 8) (R 8) [192,12,34,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15645 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 38 200 304 49 113 177 305), lower := (rows 193 14 38 200 304 32 64 128 256), losses := [] }

theorem u15645 : Upper (D 8) (R 8) [192,12,34,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15646 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u15646 : Upper (D 8) (R 8) [192,12,34,257,33] 13 := by
  apply FastRouting.sound _ _ [192,12,34,257,33] 13 (by decide) (choices 1) [16,64] r15646 c15646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5488
  · exact u5489

def b15647 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 265 81 176 240 176 432), lower := (rows 193 14 38 265 81 32 64 128 256), losses := [] }

theorem u15647 : Upper (D 8) (R 8) [192,12,34,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15648 : Route 9 := (fun mask => (mask,id))

def c15648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15648 : Upper (D 8) (R 8) [192,12,34,257,96] 13 := by
  apply FastRouting.sound _ _ [192,12,34,257,96] 13 (by decide) (choices 1) [1,16,128] r15648 c15648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5490
  · exact u5491
  · exact u5492

def b15649 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 38 265 208 49 113 177 305), lower := (rows 193 14 38 265 208 32 64 128 256), losses := [] }

theorem u15649 : Upper (D 8) (R 8) [192,12,34,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15650 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15650 : Upper (D 8) (R 8) [192,12,34,272,33] 13 := by
  apply FastRouting.sound _ _ [192,12,34,272,33] 13 (by decide) (choices 1) [1,64] r15650 c15650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5493
  · exact u5494

def b15651 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 280 81 161 225 161 417), lower := (rows 193 14 38 280 81 32 64 128 256), losses := [] }

theorem u15651 : Upper (D 8) (R 8) [192,12,34,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15652 : Route 9 := (fun mask => (mask,id))

def c15652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15652 : Upper (D 8) (R 8) [192,12,34,272,96] 13 := by
  apply FastRouting.sound _ _ [192,12,34,272,96] 13 (by decide) (choices 1) [1,128] r15652 c15652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5495
  · exact u5496

def b15653 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 38 280 208 33 97 161 289), lower := (rows 193 14 38 280 208 32 64 128 256), losses := [] }

theorem u15653 : Upper (D 8) (R 8) [192,12,34,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15654 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 296 49 241 209 209 465), lower := (rows 193 14 38 296 49 32 64 128 256), losses := [] }

theorem u15654 : Upper (D 8) (R 8) [192,12,34,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15655 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 296 112 177 209 145 401), lower := (rows 193 14 38 296 112 32 64 128 256), losses := [] }

theorem u15655 : Upper (D 8) (R 8) [192,12,34,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15656 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 328 49 177 241 177 433), lower := (rows 193 14 38 328 49 32 64 128 256), losses := [] }

theorem u15656 : Upper (D 8) (R 8) [192,12,34,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15657 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 328 176 49 113 177 305), lower := (rows 193 14 38 328 176 32 64 128 256), losses := [] }

theorem u15657 : Upper (D 8) (R 8) [192,12,34,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15658 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 52 73 273 162 226 162 418), lower := (rows 193 14 52 73 273 32 64 128 256), losses := [] }

theorem u15658 : Upper (D 8) (R 8) [192,12,48,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15659 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 52 73 274 161 225 161 417), lower := (rows 193 14 52 73 274 32 64 128 256), losses := [] }

theorem u15659 : Upper (D 8) (R 8) [192,12,48,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15659
end Delivery.IrregularNine14.P08
