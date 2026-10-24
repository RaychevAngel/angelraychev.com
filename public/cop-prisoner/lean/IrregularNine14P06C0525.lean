import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0228
import IrregularNine14P06C0229

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31500 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 148 73 22 353 353 481 353), lower := (rows 11 38 148 73 22 32 64 128 256), losses := [] }

theorem u31500 : Upper (D 6) (R 6) [10,36,144,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31501 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 4, region := 454, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 73 49 358 326 454 326), lower := (rows 11 38 148 73 49 32 64 128 256), losses := [] }

theorem u31501 : Upper (D 6) (R 6) [10,36,144,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31502 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 148 73 50 357 325 453 325), lower := (rows 11 38 148 73 50 32 64 128 256), losses := [] }

theorem u31502 : Upper (D 6) (R 6) [10,36,144,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31503 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 148 73 52 355 323 451 323), lower := (rows 11 38 148 73 52 32 64 128 256), losses := [] }

theorem u31503 : Upper (D 6) (R 6) [10,36,144,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31504 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 38 148 73 81 294 358 422 294), lower := (rows 11 38 148 73 81 32 64 128 256), losses := [] }

theorem u31504 : Upper (D 6) (R 6) [10,36,144,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31505 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 38 148 73 82 293 357 421 293), lower := (rows 11 38 148 73 82 32 64 128 256), losses := [] }

theorem u31505 : Upper (D 6) (R 6) [10,36,144,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31506 : Route 9 := (fun mask => (mask,id))

def c31506 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31506 : Upper (D 6) (R 6) [10,36,144,65,68] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,68] 13 (by decide) (choices 1) [1,2,256] r31506 c31506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13696
  · exact u13697
  · exact u13698

def r31507 : Route 9 := (fun mask => (mask,id))

def c31507 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31507 : Upper (D 6) (R 6) [10,36,144,65,96] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,96] 13 (by decide) (choices 1) [1,2,4,256] r31507 c31507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13699
  · exact u13700
  · exact u13701
  · exact u13702

def r31508 : Route 9 := (fun mask => (mask,id))

def c31508 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31508 : Upper (D 6) (R 6) [10,36,144,65,257] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,257] 13 (by decide) (choices 1) [2,4,64] r31508 c31508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13703
  · exact u13704
  · exact u13705

def r31509 : Route 9 := (fun mask => (mask,id))

def c31509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31509 : Upper (D 6) (R 6) [10,36,144,65,258] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,258] 13 (by decide) (choices 1) [1,4,64] r31509 c31509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13706
  · exact u13707
  · exact u13708

def r31510 : Route 9 := (fun mask => (mask,id))

def c31510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31510 : Upper (D 6) (R 6) [10,36,144,65,260] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,260] 13 (by decide) (choices 1) [1,2,64] r31510 c31510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13709
  · exact u13710
  · exact u13711

def r31511 : Route 9 := (fun mask => (mask,id))

def c31511 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31511 : Upper (D 6) (R 6) [10,36,144,65,288] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,288] 13 (by decide) (choices 1) [1,2,4,64] r31511 c31511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13712
  · exact u13713
  · exact u13714
  · exact u13715

def r31512 : Route 9 := (fun mask => (mask,id))

def c31512 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31512 : Upper (D 6) (R 6) [10,36,144,65,320] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65,320] 13 (by decide) (choices 1) [1,2,4] r31512 c31512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13716
  · exact u13717
  · exact u13718

def b31513 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 38 148 76 19 353 353 481 353), lower := (rows 11 38 148 76 19 32 64 128 256), losses := [] }

theorem u31513 : Upper (D 6) (R 6) [10,36,144,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31514 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 38 148 76 49 355 323 451 323), lower := (rows 11 38 148 76 49 32 64 128 256), losses := [] }

theorem u31514 : Upper (D 6) (R 6) [10,36,144,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31515 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 148 76 50 353 321 449 321), lower := (rows 11 38 148 76 50 32 64 128 256), losses := [] }

theorem u31515 : Upper (D 6) (R 6) [10,36,144,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31516 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 148 76 81 291 355 419 291), lower := (rows 11 38 148 76 81 32 64 128 256), losses := [] }

theorem u31516 : Upper (D 6) (R 6) [10,36,144,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31517 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 148 76 82 289 353 417 289), lower := (rows 11 38 148 76 82 32 64 128 256), losses := [] }

theorem u31517 : Upper (D 6) (R 6) [10,36,144,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31518 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 3, region := 291, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 148 76 112 291 323 387 259), lower := (rows 11 38 148 76 112 32 64 128 256), losses := [] }

theorem u31518 : Upper (D 6) (R 6) [10,36,144,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31519 : Route 9 := (fun mask => (mask,id))

def c31519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31519 : Upper (D 6) (R 6) [10,36,144,68,257] 13 := by
  apply FastRouting.sound _ _ [10,36,144,68,257] 13 (by decide) (choices 1) [1,2,64] r31519 c31519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13719
  · exact u13720
  · exact u13721

def r31520 : Route 9 := (fun mask => (mask,id))

def c31520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31520 : Upper (D 6) (R 6) [10,36,144,68,258] 13 := by
  apply FastRouting.sound _ _ [10,36,144,68,258] 13 (by decide) (choices 1) [1,64] r31520 c31520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13722
  · exact u13723

def b31521 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 38 148 76 304 99 67 195 323), lower := (rows 11 38 148 76 304 32 64 128 256), losses := [] }

theorem u31521 : Upper (D 6) (R 6) [10,36,144,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31522 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 148 76 336 35 99 163 291), lower := (rows 11 38 148 76 336 32 64 128 256), losses := [] }

theorem u31522 : Upper (D 6) (R 6) [10,36,144,68,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31523 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 148 104 19 357 325 453 325), lower := (rows 11 38 148 104 19 32 64 128 256), losses := [] }

theorem u31523 : Upper (D 6) (R 6) [10,36,144,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31524 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 148 104 21 355 323 451 323), lower := (rows 11 38 148 104 21 32 64 128 256), losses := [] }

theorem u31524 : Upper (D 6) (R 6) [10,36,144,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31525 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 148 104 22 353 321 449 321), lower := (rows 11 38 148 104 22 32 64 128 256), losses := [] }

theorem u31525 : Upper (D 6) (R 6) [10,36,144,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31526 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 148 104 81 295 327 391 263), lower := (rows 11 38 148 104 81 32 64 128 256), losses := [] }

theorem u31526 : Upper (D 6) (R 6) [10,36,144,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31527 : Route 9 := (fun mask => (mask,id))

def c31527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31527 : Upper (D 6) (R 6) [10,36,144,96,66] 13 := by
  apply FastRouting.sound _ _ [10,36,144,96,66] 13 (by decide) (choices 1) [1,4,256] r31527 c31527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13724
  · exact u13725
  · exact u13726

def b31528 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 148 104 84 291 323 387 259), lower := (rows 11 38 148 104 84 32 64 128 256), losses := [] }

theorem u31528 : Upper (D 6) (R 6) [10,36,144,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31529 : Route 9 := (fun mask => (mask,id))

def c31529 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31529 : Upper (D 6) (R 6) [10,36,144,96,257] 13 := by
  apply FastRouting.sound _ _ [10,36,144,96,257] 13 (by decide) (choices 1) [1,2,4,64] r31529 c31529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13727
  · exact u13728
  · exact u13729
  · exact u13730

def r31530 : Route 9 := (fun mask => (mask,id))

def c31530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31530 : Upper (D 6) (R 6) [10,36,144,96,258] 13 := by
  apply FastRouting.sound _ _ [10,36,144,96,258] 13 (by decide) (choices 1) [1,4,64] r31530 c31530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13731
  · exact u13732
  · exact u13733

def b31531 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 148 104 276 99 67 195 323), lower := (rows 11 38 148 104 276 32 64 128 256), losses := [] }

theorem u31531 : Upper (D 6) (R 6) [10,36,144,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31532 : Route 9 := (fun mask => (mask,id))

def c31532 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31532 : Upper (D 6) (R 6) [10,36,144,96,320] 13 := by
  apply FastRouting.sound _ _ [10,36,144,96,320] 13 (by decide) (choices 1) [1,2,4] r31532 c31532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13734
  · exact u13735
  · exact u13736

def b31533 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 148 265 19 100 100 228 356), lower := (rows 11 38 148 265 19 32 64 128 256), losses := [] }

theorem u31533 : Upper (D 6) (R 6) [10,36,144,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31534 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 148 265 21 98 98 226 354), lower := (rows 11 38 148 265 21 32 64 128 256), losses := [] }

theorem u31534 : Upper (D 6) (R 6) [10,36,144,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31535 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 148 265 22 97 97 225 353), lower := (rows 11 38 148 265 22 32 64 128 256), losses := [] }

theorem u31535 : Upper (D 6) (R 6) [10,36,144,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31536 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 4, region := 198, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 265 49 102 70 198 326), lower := (rows 11 38 148 265 49 32 64 128 256), losses := [] }

theorem u31536 : Upper (D 6) (R 6) [10,36,144,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31537 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 148 265 50 101 69 197 325), lower := (rows 11 38 148 265 50 32 64 128 256), losses := [] }

theorem u31537 : Upper (D 6) (R 6) [10,36,144,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31538 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 148 265 52 99 67 195 323), lower := (rows 11 38 148 265 52 32 64 128 256), losses := [] }

theorem u31538 : Upper (D 6) (R 6) [10,36,144,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31539 : Route 9 := (fun mask => (mask,id))

def c31539 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31539 : Upper (D 6) (R 6) [10,36,144,257,65] 13 := by
  apply FastRouting.sound _ _ [10,36,144,257,65] 13 (by decide) (choices 1) [2,4,64] r31539 c31539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13737
  · exact u13738
  · exact u13739

def r31540 : Route 9 := (fun mask => (mask,id))

def c31540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31540 : Upper (D 6) (R 6) [10,36,144,257,66] 13 := by
  apply FastRouting.sound _ _ [10,36,144,257,66] 13 (by decide) (choices 1) [1,4,64] r31540 c31540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13740
  · exact u13741
  · exact u13742

def r31541 : Route 9 := (fun mask => (mask,id))

def c31541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31541 : Upper (D 6) (R 6) [10,36,144,257,68] 13 := by
  apply FastRouting.sound _ _ [10,36,144,257,68] 13 (by decide) (choices 1) [1,2,64] r31541 c31541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13743
  · exact u13744
  · exact u13745

def r31542 : Route 9 := (fun mask => (mask,id))

def c31542 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31542 : Upper (D 6) (R 6) [10,36,144,257,96] 13 := by
  apply FastRouting.sound _ _ [10,36,144,257,96] 13 (by decide) (choices 1) [1,2,4,64] r31542 c31542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13746
  · exact u13747
  · exact u13748
  · exact u13749

def b31543 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 38 148 268 19 97 97 225 353), lower := (rows 11 38 148 268 19 32 64 128 256), losses := [] }

theorem u31543 : Upper (D 6) (R 6) [10,36,144,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31544 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 38 148 268 49 99 67 195 323), lower := (rows 11 38 148 268 49 32 64 128 256), losses := [] }

theorem u31544 : Upper (D 6) (R 6) [10,36,144,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31545 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 148 268 50 97 65 193 321), lower := (rows 11 38 148 268 50 32 64 128 256), losses := [] }

theorem u31545 : Upper (D 6) (R 6) [10,36,144,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31546 : Route 9 := (fun mask => (mask,id))

def c31546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31546 : Upper (D 6) (R 6) [10,36,144,260,65] 13 := by
  apply FastRouting.sound _ _ [10,36,144,260,65] 13 (by decide) (choices 1) [1,2,64] r31546 c31546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13750
  · exact u13751
  · exact u13752

def r31547 : Route 9 := (fun mask => (mask,id))

def c31547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31547 : Upper (D 6) (R 6) [10,36,144,260,66] 13 := by
  apply FastRouting.sound _ _ [10,36,144,260,66] 13 (by decide) (choices 1) [1,64] r31547 c31547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13753
  · exact u13754

def b31548 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 38 148 268 112 99 67 195 323), lower := (rows 11 38 148 268 112 32 64 128 256), losses := [] }

theorem u31548 : Upper (D 6) (R 6) [10,36,144,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31549 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 148 296 19 101 69 197 325), lower := (rows 11 38 148 296 19 32 64 128 256), losses := [] }

theorem u31549 : Upper (D 6) (R 6) [10,36,144,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31550 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 148 296 21 99 67 195 323), lower := (rows 11 38 148 296 21 32 64 128 256), losses := [] }

theorem u31550 : Upper (D 6) (R 6) [10,36,144,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31551 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 148 296 22 97 65 193 321), lower := (rows 11 38 148 296 22 32 64 128 256), losses := [] }

theorem u31551 : Upper (D 6) (R 6) [10,36,144,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31552 : Route 9 := (fun mask => (mask,id))

def c31552 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31552 : Upper (D 6) (R 6) [10,36,144,288,65] 13 := by
  apply FastRouting.sound _ _ [10,36,144,288,65] 13 (by decide) (choices 1) [1,2,4,64] r31552 c31552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13755
  · exact u13756
  · exact u13757
  · exact u13758

def r31553 : Route 9 := (fun mask => (mask,id))

def c31553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31553 : Upper (D 6) (R 6) [10,36,144,288,66] 13 := by
  apply FastRouting.sound _ _ [10,36,144,288,66] 13 (by decide) (choices 1) [1,4,64] r31553 c31553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13759
  · exact u13760
  · exact u13761

def b31554 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 148 296 84 99 67 195 323), lower := (rows 11 38 148 296 84 32 64 128 256), losses := [] }

theorem u31554 : Upper (D 6) (R 6) [10,36,144,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31555 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 148 328 19 101 101 229 357), lower := (rows 11 38 148 328 19 32 64 128 256), losses := [] }

theorem u31555 : Upper (D 6) (R 6) [10,36,144,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31556 : Route 9 := (fun mask => (mask,id))

def c31556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31556 : Upper (D 6) (R 6) [10,36,144,320,5] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,5] 13 (by decide) (choices 1) [1,2,64] r31556 c31556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13762
  · exact u13763
  · exact u13764

def b31557 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 148 328 22 97 97 225 353), lower := (rows 11 38 148 328 22 32 64 128 256), losses := [] }

theorem u31557 : Upper (D 6) (R 6) [10,36,144,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31558 : Route 9 := (fun mask => (mask,id))

def c31558 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31558 : Upper (D 6) (R 6) [10,36,144,320,33] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,33] 13 (by decide) (choices 1) [1,2,4,64] r31558 c31558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13765
  · exact u13766
  · exact u13767
  · exact u13768

def b31559 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 148 328 50 101 69 197 325), lower := (rows 11 38 148 328 50 32 64 128 256), losses := [] }

theorem u31559 : Upper (D 6) (R 6) [10,36,144,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u31559
end Delivery.IrregularNine14.P06
