import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0161
import IrregularNine14P06C0162

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28500 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 35 140 56 21 354 322 450 322), lower := (rows 7 35 140 56 21 32 64 128 256), losses := [] }

theorem u28500 : Upper (D 6) (R 6) [6,33,136,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28500
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28501 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 354, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(4,0),(4,5)], upper := (rows 7 35 140 56 22 353 321 449 321), lower := (rows 7 35 140 56 22 32 64 128 256), losses := [] }

theorem u28501 : Upper (D 6) (R 6) [6,33,136,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28501
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28502 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 35 140 56 81 358 326 454 326), lower := (rows 7 35 140 56 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 33 65 129 257), good := (rows 486 482 140 60 508 32 64 128 256) }] }

theorem u28502 : Upper (D 6) (R 6) [6,33,136,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28502
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28503 : Route 9 := (fun mask => (mask,id))

def c28503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28503 : Upper (D 6) (R 6) [6,33,136,48,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,66] 13 (by decide) (choices 1) [1,4,64,256] r28503 c28503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9677
  · exact u9678
  · exact u9679
  · exact u9680

def r28504 : Route 9 := (fun mask => (mask,id))

def c28504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28504 : Upper (D 6) (R 6) [6,33,136,48,68] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,68] 13 (by decide) (choices 1) [1,2,64,256] r28504 c28504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9681
  · exact u9682
  · exact u9683
  · exact u9684

def b28505 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 35 140 56 273 102 70 198 326), lower := (rows 7 35 140 56 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 33 65 129 257), good := (rows 486 482 140 60 508 32 64 128 256) }] }

theorem u28505 : Upper (D 6) (R 6) [6,33,136,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28505
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28506 : Route 9 := (fun mask => (mask,id))

def c28506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28506 : Upper (D 6) (R 6) [6,33,136,48,258] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,258] 13 (by decide) (choices 1) [1,4,64] r28506 c28506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9685
  · exact u9686
  · exact u9687

def r28507 : Route 9 := (fun mask => (mask,id))

def c28507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28507 : Upper (D 6) (R 6) [6,33,136,48,260] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,260] 13 (by decide) (choices 1) [1,2,64] r28507 c28507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9688
  · exact u9689
  · exact u9690

def r28508 : Route 9 := (fun mask => (mask,id))

def c28508 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28508 : Upper (D 6) (R 6) [6,33,136,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,320] 13 (by decide) (choices 1) [1,2,4,64] r28508 c28508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9691
  · exact u9692
  · exact u9693
  · exact u9694

def b28509 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 35 140 73 22 368 368 496 368), lower := (rows 7 35 140 73 22 32 64 128 256), losses := [] }

theorem u28509 : Upper (D 6) (R 6) [6,33,136,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28509
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28510 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 140 73 50 372 340 468 340), lower := (rows 7 35 140 73 50 32 64 128 256), losses := [] }

theorem u28510 : Upper (D 6) (R 6) [6,33,136,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28510
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28511 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 7 35 140 73 52 370 338 466 338), lower := (rows 7 35 140 73 52 32 64 128 256), losses := [] }

theorem u28511 : Upper (D 6) (R 6) [6,33,136,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28511
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28512 : Route 9 := (fun mask => (mask,id))

def c28512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28512 : Upper (D 6) (R 6) [6,33,136,65,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,65,66] 13 (by decide) (choices 1) [4,16,256] r28512 c28512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9695
  · exact u9696
  · exact u9697

def b28513 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 7 35 140 73 84 306 370 434 306), lower := (rows 7 35 140 73 84 32 64 128 256), losses := [] }

theorem u28513 : Upper (D 6) (R 6) [6,33,136,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28513
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28514 : Route 9 := (fun mask => (mask,id))

def c28514 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28514 : Upper (D 6) (R 6) [6,33,136,65,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,65,96] 13 (by decide) (choices 1) [2,4,16,256] r28514 c28514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9698
  · exact u9699
  · exact u9700
  · exact u9701

def r28515 : Route 9 := (fun mask => (mask,id))

def c28515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28515 : Upper (D 6) (R 6) [6,33,136,65,258] 13 := by
  apply FastRouting.sound _ _ [6,33,136,65,258] 13 (by decide) (choices 1) [4,16,64] r28515 c28515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9702
  · exact u9703
  · exact u9704

def r28516 : Route 9 := (fun mask => (mask,id))

def c28516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28516 : Upper (D 6) (R 6) [6,33,136,65,260] 13 := by
  apply FastRouting.sound _ _ [6,33,136,65,260] 13 (by decide) (choices 1) [2,16,64] r28516 c28516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9705
  · exact u9706
  · exact u9707

def r28517 : Route 9 := (fun mask => (mask,id))

def c28517 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28517 : Upper (D 6) (R 6) [6,33,136,65,288] 13 := by
  apply FastRouting.sound _ _ [6,33,136,65,288] 13 (by decide) (choices 1) [2,4,16,64] r28517 c28517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9708
  · exact u9709
  · exact u9710
  · exact u9711

def r28518 : Route 9 := (fun mask => (mask,id))

def c28518 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28518 : Upper (D 6) (R 6) [6,33,136,65,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,65,320] 13 (by decide) (choices 1) [2,4,16] r28518 c28518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9712
  · exact u9713
  · exact u9714

def b28519 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 35 140 74 21 368 368 496 368), lower := (rows 7 35 140 74 21 32 64 128 256), losses := [] }

theorem u28519 : Upper (D 6) (R 6) [6,33,136,66,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28519
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28520 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 140 74 49 372 340 468 340), lower := (rows 7 35 140 74 49 32 64 128 256), losses := [] }

theorem u28520 : Upper (D 6) (R 6) [6,33,136,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28520
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28521 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 368, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 7 35 140 74 52 369 337 465 337), lower := (rows 7 35 140 74 52 32 64 128 256), losses := [] }

theorem u28521 : Upper (D 6) (R 6) [6,33,136,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28521
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28522 : Route 9 := (fun mask => (mask,id))

def c28522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28522 : Upper (D 6) (R 6) [6,33,136,66,65] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,65] 13 (by decide) (choices 1) [4,16,256] r28522 c28522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9715
  · exact u9716
  · exact u9717

def b28523 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 7 35 140 74 84 305 369 433 305), lower := (rows 7 35 140 74 84 32 64 128 256), losses := [] }

theorem u28523 : Upper (D 6) (R 6) [6,33,136,66,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28523
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28524 : Route 9 := (fun mask => (mask,id))

def c28524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28524 : Upper (D 6) (R 6) [6,33,136,66,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,96] 13 (by decide) (choices 1) [1,4,16,256] r28524 c28524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9718
  · exact u9719
  · exact u9720
  · exact u9721

def r28525 : Route 9 := (fun mask => (mask,id))

def c28525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28525 : Upper (D 6) (R 6) [6,33,136,66,257] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,257] 13 (by decide) (choices 1) [4,16,64] r28525 c28525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9722
  · exact u9723
  · exact u9724

def r28526 : Route 9 := (fun mask => (mask,id))

def c28526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28526 : Upper (D 6) (R 6) [6,33,136,66,260] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,260] 13 (by decide) (choices 1) [1,16,64] r28526 c28526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9725
  · exact u9726
  · exact u9727

def r28527 : Route 9 := (fun mask => (mask,id))

def c28527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28527 : Upper (D 6) (R 6) [6,33,136,66,288] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,288] 13 (by decide) (choices 1) [1,4,16,64] r28527 c28527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9728
  · exact u9729
  · exact u9730
  · exact u9731

def r28528 : Route 9 := (fun mask => (mask,id))

def c28528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28528 : Upper (D 6) (R 6) [6,33,136,66,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66,320] 13 (by decide) (choices 1) [1,4,16] r28528 c28528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9732
  · exact u9733
  · exact u9734

def b28529 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 76 19 368 368 496 368), lower := (rows 7 35 140 76 19 32 64 128 256), losses := [] }

theorem u28529 : Upper (D 6) (R 6) [6,33,136,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28529
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28530 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,2),(4,1),(4,2)], upper := (rows 7 35 140 76 49 370 338 466 338), lower := (rows 7 35 140 76 49 32 64 128 256), losses := [] }

theorem u28530 : Upper (D 6) (R 6) [6,33,136,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28530
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28531 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 140 76 50 369 337 465 337), lower := (rows 7 35 140 76 50 32 64 128 256), losses := [] }

theorem u28531 : Upper (D 6) (R 6) [6,33,136,68,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28531
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28532 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 7 35 140 76 81 306 370 434 306), lower := (rows 7 35 140 76 81 32 64 128 256), losses := [] }

theorem u28532 : Upper (D 6) (R 6) [6,33,136,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28532
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28533 : Route 9 := (fun mask => (mask,id))

def c28533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28533 : Upper (D 6) (R 6) [6,33,136,68,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,68,66] 13 (by decide) (choices 1) [1,16,256] r28533 c28533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9735
  · exact u9736
  · exact u9737

def r28534 : Route 9 := (fun mask => (mask,id))

def c28534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28534 : Upper (D 6) (R 6) [6,33,136,68,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,68,96] 13 (by decide) (choices 1) [1,2,16,256] r28534 c28534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9738
  · exact u9739
  · exact u9740
  · exact u9741

def r28535 : Route 9 := (fun mask => (mask,id))

def c28535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28535 : Upper (D 6) (R 6) [6,33,136,68,257] 13 := by
  apply FastRouting.sound _ _ [6,33,136,68,257] 13 (by decide) (choices 1) [2,16,64] r28535 c28535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9742
  · exact u9743
  · exact u9744

def r28536 : Route 9 := (fun mask => (mask,id))

def c28536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28536 : Upper (D 6) (R 6) [6,33,136,68,258] 13 := by
  apply FastRouting.sound _ _ [6,33,136,68,258] 13 (by decide) (choices 1) [1,16,64] r28536 c28536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9745
  · exact u9746
  · exact u9747

def r28537 : Route 9 := (fun mask => (mask,id))

def c28537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28537 : Upper (D 6) (R 6) [6,33,136,68,288] 13 := by
  apply FastRouting.sound _ _ [6,33,136,68,288] 13 (by decide) (choices 1) [1,2,16,64] r28537 c28537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9748
  · exact u9749
  · exact u9750
  · exact u9751

def r28538 : Route 9 := (fun mask => (mask,id))

def c28538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28538 : Upper (D 6) (R 6) [6,33,136,68,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,68,320] 13 (by decide) (choices 1) [1,2,16] r28538 c28538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9752
  · exact u9753
  · exact u9754

def b28539 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 88 19 356 356 484 356), lower := (rows 7 35 140 88 19 32 64 128 256), losses := [] }

theorem u28539 : Upper (D 6) (R 6) [6,33,136,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28539
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28540 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 35 140 88 21 354 354 482 354), lower := (rows 7 35 140 88 21 32 64 128 256), losses := [] }

theorem u28540 : Upper (D 6) (R 6) [6,33,136,80,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28540
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28541 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 35 140 88 22 353 353 481 353), lower := (rows 7 35 140 88 22 32 64 128 256), losses := [] }

theorem u28541 : Upper (D 6) (R 6) [6,33,136,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28541
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28542 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 140 88 49 358 326 454 326), lower := (rows 7 35 140 88 49 32 64 128 256), losses := [] }

theorem u28542 : Upper (D 6) (R 6) [6,33,136,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28542
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28543 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 140 88 50 357 325 453 325), lower := (rows 7 35 140 88 50 32 64 128 256), losses := [] }

theorem u28543 : Upper (D 6) (R 6) [6,33,136,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28543
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28544 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 354, targets := 4 }], pairs := [(0,6),(1,2),(1,6)], upper := (rows 7 35 140 88 52 355 323 451 323), lower := (rows 7 35 140 88 52 32 64 128 256), losses := [] }

theorem u28544 : Upper (D 6) (R 6) [6,33,136,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28544
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28545 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 140 88 81 294 358 422 294), lower := (rows 7 35 140 88 81 32 64 128 256), losses := [] }

theorem u28545 : Upper (D 6) (R 6) [6,33,136,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28545
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28546 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 140 88 82 293 357 421 293), lower := (rows 7 35 140 88 82 32 64 128 256), losses := [] }

theorem u28546 : Upper (D 6) (R 6) [6,33,136,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28546
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28547 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 140 88 84 291 355 419 291), lower := (rows 7 35 140 88 84 32 64 128 256), losses := [] }

theorem u28547 : Upper (D 6) (R 6) [6,33,136,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28547
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28548 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 140 88 112 295 327 391 263), lower := (rows 7 35 140 88 112 32 64 128 256), losses := [] }

theorem u28548 : Upper (D 6) (R 6) [6,33,136,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28548
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28549 : Route 9 := (fun mask => (mask,id))

def c28549 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28549 : Upper (D 6) (R 6) [6,33,136,80,257] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,257] 13 (by decide) (choices 1) [2,4,64] r28549 c28549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9755
  · exact u9756
  · exact u9757

def r28550 : Route 9 := (fun mask => (mask,id))

def c28550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28550 : Upper (D 6) (R 6) [6,33,136,80,258] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,258] 13 (by decide) (choices 1) [1,4,64] r28550 c28550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9758
  · exact u9759
  · exact u9760

def r28551 : Route 9 := (fun mask => (mask,id))

def c28551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28551 : Upper (D 6) (R 6) [6,33,136,80,260] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,260] 13 (by decide) (choices 1) [1,2,64] r28551 c28551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9761
  · exact u9762
  · exact u9763

def r28552 : Route 9 := (fun mask => (mask,id))

def c28552 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28552 : Upper (D 6) (R 6) [6,33,136,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,288] 13 (by decide) (choices 1) [1,2,4,64] r28552 c28552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9764
  · exact u9765
  · exact u9766
  · exact u9767

def b28553 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 140 88 336 39 103 167 295), lower := (rows 7 35 140 88 336 32 64 128 256), losses := [] }

theorem u28553 : Upper (D 6) (R 6) [6,33,136,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28553
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28554 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 104 19 372 340 468 340), lower := (rows 7 35 140 104 19 32 64 128 256), losses := [] }

theorem u28554 : Upper (D 6) (R 6) [6,33,136,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28554
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28555 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 35 140 104 21 370 338 466 338), lower := (rows 7 35 140 104 21 32 64 128 256), losses := [] }

theorem u28555 : Upper (D 6) (R 6) [6,33,136,96,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28555
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28556 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 35 140 104 22 369 337 465 337), lower := (rows 7 35 140 104 22 32 64 128 256), losses := [] }

theorem u28556 : Upper (D 6) (R 6) [6,33,136,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28556
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28557 : Route 9 := (fun mask => (mask,id))

def c28557 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28557 : Upper (D 6) (R 6) [6,33,136,96,65] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96,65] 13 (by decide) (choices 1) [2,4,16,256] r28557 c28557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9768
  · exact u9769
  · exact u9770
  · exact u9771

def r28558 : Route 9 := (fun mask => (mask,id))

def c28558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28558 : Upper (D 6) (R 6) [6,33,136,96,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96,66] 13 (by decide) (choices 1) [1,4,16,256] r28558 c28558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9772
  · exact u9773
  · exact u9774
  · exact u9775

def b28559 : PairBound 9 := { available := 275, camps := [{ cop := 4, region := 291, targets := 64 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,6),(1,6),(4,5)], upper := (rows 7 35 140 104 84 307 339 403 275), lower := (rows 7 35 140 104 84 32 64 128 256), losses := [] }

theorem u28559 : Upper (D 6) (R 6) [6,33,136,96,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28559
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28559
end Delivery.IrregularNine14.P06
