import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0092
import IrregularNine14P01C0093

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8580 : Route 9 := (fun mask => (mask,id))

def c8580 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8580 : Upper (D 1) (R 1) [304,68,144,34] 13 := by
  apply FastRouting.sound _ _ [304,68,144,34] 13 (by decide) (choices 1) [1,2,8,64,128] r8580 c8580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5532
  · exact u5533
  · exact u5534
  · exact u5535
  · exact u5536

def r8581 : Route 9 := (fun mask => (mask,id))

def c8581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8581 : Upper (D 1) (R 1) [304,68,144,65] 13 := by
  apply FastRouting.sound _ _ [304,68,144,65] 13 (by decide) (choices 1) [2,8,32,128] r8581 c8581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5537
  · exact u5538
  · exact u5539
  · exact u5540

def b8582 : PairBound 9 := { available := 171, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 148 74 187 171 235 171 427), lower := (rows 305 70 148 74 16 32 64 128 256), losses := [] }

theorem u8582 : Upper (D 1) (R 1) [304,68,144,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8583 : Route 9 := (fun mask => (mask,id))

def c8583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8583 : Upper (D 1) (R 1) [304,68,144,96] 13 := by
  apply FastRouting.sound _ _ [304,68,144,96] 13 (by decide) (choices 1) [1,2,8,128] r8583 c8583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5541
  · exact u5542
  · exact u5543
  · exact u5544

def r8584 : Route 9 := (fun mask => (mask,id))

def c8584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8584 : Upper (D 1) (R 1) [304,68,144,129] 13 := by
  apply FastRouting.sound _ _ [304,68,144,129] 13 (by decide) (choices 1) [2,8,32,64] r8584 c8584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5545
  · exact u5546
  · exact u5547
  · exact u5548

def b8585 : PairBound 9 := { available := 107, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 138 123 107 107 235 363), lower := (rows 305 70 148 138 16 32 64 128 256), losses := [] }

theorem u8585 : Upper (D 1) (R 1) [304,68,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8585
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8586 : Route 9 := (fun mask => (mask,id))

def c8586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8586 : Upper (D 1) (R 1) [304,68,144,160] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160] 13 (by decide) (choices 1) [1,2,8,64] r8586 c8586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5549
  · exact u5550
  · exact u5551
  · exact u5552

def r8587 : Route 9 := (fun mask => (mask,id))

def c8587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8587 : Upper (D 1) (R 1) [304,68,144,192] 13 := by
  apply FastRouting.sound _ _ [304,68,144,192] 13 (by decide) (choices 1) [1,2,8,32] r8587 c8587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5553
  · exact u5554
  · exact u5555
  · exact u5556

def b8588 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 305 82 7 14 248 232 232 232 488), lower := (rows 305 82 7 14 16 32 64 128 256), losses := [] }

theorem u8588 : Upper (D 1) (R 1) [304,80,3,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8588
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8589 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 42 220 236 204 204 460), lower := (rows 305 82 7 42 16 32 64 128 256), losses := [] }

theorem u8589 : Upper (D 1) (R 1) [304,80,3,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8590 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 44 218 234 202 202 458), lower := (rows 305 82 7 44 16 32 64 128 256), losses := [] }

theorem u8590 : Upper (D 1) (R 1) [304,80,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8590
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8591 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 76 186 170 234 170 426), lower := (rows 305 82 7 76 16 32 64 128 256), losses := [] }

theorem u8591 : Upper (D 1) (R 1) [304,80,3,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8591
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8592 : PairBound 9 := { available := 142, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 104 158 174 206 142 398), lower := (rows 305 82 7 104 16 32 64 128 256), losses := [] }

theorem u8592 : Upper (D 1) (R 1) [304,80,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8592
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8593 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 138 252 236 236 236 492), lower := (rows 305 82 7 138 16 32 64 128 256), losses := [] }

theorem u8593 : Upper (D 1) (R 1) [304,80,3,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8593
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8594 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 140 250 234 234 234 490), lower := (rows 305 82 7 140 16 32 64 128 256), losses := [] }

theorem u8594 : Upper (D 1) (R 1) [304,80,3,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8594
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8595 : PairBound 9 := { available := 206, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 168 222 238 206 206 462), lower := (rows 305 82 7 168 16 32 64 128 256), losses := [] }

theorem u8595 : Upper (D 1) (R 1) [304,80,3,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8595
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8596 : PairBound 9 := { available := 174, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 200 190 174 238 174 430), lower := (rows 305 82 7 200 16 32 64 128 256), losses := [] }

theorem u8596 : Upper (D 1) (R 1) [304,80,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8596
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8597 : Route 9 := (fun mask => (mask,id))

def c8597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8597 : Upper (D 1) (R 1) [304,80,9,6] 13 := by
  apply FastRouting.sound _ _ [304,80,9,6] 13 (by decide) (choices 1) [2,32,64,128] r8597 c8597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5557
  · exact u5558
  · exact u5559
  · exact u5560

def b8598 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 42 214 230 198 198 454), lower := (rows 305 82 13 42 16 32 64 128 256), losses := [] }

theorem u8598 : Upper (D 1) (R 1) [304,80,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8598
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8599 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 13 44 210 226 194 194 450), lower := (rows 305 82 13 44 16 32 64 128 256), losses := [] }

theorem u8599 : Upper (D 1) (R 1) [304,80,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8599
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8600 : PairBound 9 := { available := 166, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 13 74 182 166 230 166 422), lower := (rows 305 82 13 74 16 32 64 128 256), losses := [] }

theorem u8600 : Upper (D 1) (R 1) [304,80,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8600
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8601 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 13 76 178 162 226 162 418), lower := (rows 305 82 13 76 16 32 64 128 256), losses := [] }

theorem u8601 : Upper (D 1) (R 1) [304,80,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8601
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8602 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 104 150 166 198 134 390), lower := (rows 305 82 13 104 16 32 64 128 256), losses := [] }

theorem u8602 : Upper (D 1) (R 1) [304,80,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8602
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8603 : Route 9 := (fun mask => (mask,id))

def c8603 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u8603 : Upper (D 1) (R 1) [304,80,9,130] 13 := by
  apply FastRouting.sound _ _ [304,80,9,130] 13 (by decide) (choices 1) [2,4,32,64,128] r8603 c8603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5561
  · exact u5562
  · exact u5563
  · exact u5564
  · exact u5565

def r8604 : Route 9 := (fun mask => (mask,id))

def c8604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8604 : Upper (D 1) (R 1) [304,80,9,132] 13 := by
  apply FastRouting.sound _ _ [304,80,9,132] 13 (by decide) (choices 1) [2,32,64,128] r8604 c8604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5566
  · exact u5567
  · exact u5568
  · exact u5569

def b8605 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 168 214 230 198 198 454), lower := (rows 305 82 13 168 16 32 64 128 256), losses := [] }

theorem u8605 : Upper (D 1) (R 1) [304,80,9,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8605
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8606 : Route 9 := (fun mask => (mask,id))

def c8606 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8606 : Upper (D 1) (R 1) [304,80,9,192] 13 := by
  apply FastRouting.sound _ _ [304,80,9,192] 13 (by decide) (choices 1) [2,4,32,128] r8606 c8606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5570
  · exact u5571
  · exact u5572
  · exact u5573

def b8607 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 14 14 241 225 225 225 481), lower := (rows 305 82 14 14 16 32 64 128 256), losses := [] }

theorem u8607 : Upper (D 1) (R 1) [304,80,10,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8607
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8608 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 82 14 41 214 230 198 198 454), lower := (rows 305 82 14 41 16 32 64 128 256), losses := [] }

theorem u8608 : Upper (D 1) (R 1) [304,80,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8608
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8609 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 14 42 213 229 197 197 453), lower := (rows 305 82 14 42 16 32 64 128 256), losses := [] }

theorem u8609 : Upper (D 1) (R 1) [304,80,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8610 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 14 44 211 227 195 195 451), lower := (rows 305 82 14 44 16 32 64 128 256), losses := [] }

theorem u8610 : Upper (D 1) (R 1) [304,80,10,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8610
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8611 : PairBound 9 := { available := 166, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 14 73 182 166 230 166 422), lower := (rows 305 82 14 73 16 32 64 128 256), losses := [] }

theorem u8611 : Upper (D 1) (R 1) [304,80,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8611
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8612 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 14 74 181 165 229 165 421), lower := (rows 305 82 14 74 16 32 64 128 256), losses := [] }

theorem u8612 : Upper (D 1) (R 1) [304,80,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8612
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8613 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 14 76 179 163 227 163 419), lower := (rows 305 82 14 76 16 32 64 128 256), losses := [] }

theorem u8613 : Upper (D 1) (R 1) [304,80,10,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8613
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8614 : PairBound 9 := { available := 135, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 14 104 151 167 199 135 391), lower := (rows 305 82 14 104 16 32 64 128 256), losses := [] }

theorem u8614 : Upper (D 1) (R 1) [304,80,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8614
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8615 : Route 9 := (fun mask => (mask,id))

def c8615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u8615 : Upper (D 1) (R 1) [304,80,10,129] 13 := by
  apply FastRouting.sound _ _ [304,80,10,129] 13 (by decide) (choices 1) [2,4,32,64,128] r8615 c8615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5574
  · exact u5575
  · exact u5576
  · exact u5577
  · exact u5578

def b8616 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 14 138 245 229 229 229 485), lower := (rows 305 82 14 138 16 32 64 128 256), losses := [] }

theorem u8616 : Upper (D 1) (R 1) [304,80,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8617 : Route 9 := (fun mask => (mask,id))

def c8617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8617 : Upper (D 1) (R 1) [304,80,10,132] 13 := by
  apply FastRouting.sound _ _ [304,80,10,132] 13 (by decide) (choices 1) [1,2,32,64,128] r8617 c8617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5579
  · exact u5580
  · exact u5581
  · exact u5582
  · exact u5583

def r8618 : Route 9 := (fun mask => (mask,id))

def c8618 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8618 : Upper (D 1) (R 1) [304,80,10,160] 13 := by
  apply FastRouting.sound _ _ [304,80,10,160] 13 (by decide) (choices 1) [1,2,4,64,128] r8618 c8618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5584
  · exact u5585
  · exact u5586
  · exact u5587
  · exact u5588

def b8619 : PairBound 9 := { available := 167, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 14 200 183 167 231 167 423), lower := (rows 305 82 14 200 16 32 64 128 256), losses := [] }

theorem u8619 : Upper (D 1) (R 1) [304,80,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8619
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8620 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 37 76 154 170 202 138 394), lower := (rows 305 82 37 76 16 32 64 128 256), losses := [] }

theorem u8620 : Upper (D 1) (R 1) [304,80,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8620
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8621 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 37 138 222 238 206 206 462), lower := (rows 305 82 37 138 16 32 64 128 256), losses := [] }

theorem u8621 : Upper (D 1) (R 1) [304,80,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8621
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8622 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 37 140 218 234 202 202 458), lower := (rows 305 82 37 140 16 32 64 128 256), losses := [] }

theorem u8622 : Upper (D 1) (R 1) [304,80,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8622
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8623 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 37 200 158 174 206 142 398), lower := (rows 305 82 37 200 16 32 64 128 256), losses := [] }

theorem u8623 : Upper (D 1) (R 1) [304,80,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8623
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8624 : Route 9 := (fun mask => (mask,id))

def c8624 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8624 : Upper (D 1) (R 1) [304,80,34,65] 13 := by
  apply FastRouting.sound _ _ [304,80,34,65] 13 (by decide) (choices 1) [2,4,8,128] r8624 c8624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5589
  · exact u5590
  · exact u5591
  · exact u5592

def b8625 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 38 74 157 173 205 141 397), lower := (rows 305 82 38 74 16 32 64 128 256), losses := [] }

theorem u8625 : Upper (D 1) (R 1) [304,80,34,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8625
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8626 : Route 9 := (fun mask => (mask,id))

def c8626 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8626 : Upper (D 1) (R 1) [304,80,34,68] 13 := by
  apply FastRouting.sound _ _ [304,80,34,68] 13 (by decide) (choices 1) [1,2,8,128] r8626 c8626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5593
  · exact u5594
  · exact u5595
  · exact u5596

def r8627 : Route 9 := (fun mask => (mask,id))

def c8627 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u8627 : Upper (D 1) (R 1) [304,80,34,129] 13 := by
  apply FastRouting.sound _ _ [304,80,34,129] 13 (by decide) (choices 1) [2,4,8,64,128] r8627 c8627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5597
  · exact u5598
  · exact u5599
  · exact u5600
  · exact u5601

def r8628 : Route 9 := (fun mask => (mask,id))

def c8628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8628 : Upper (D 1) (R 1) [304,80,34,130] 13 := by
  apply FastRouting.sound _ _ [304,80,34,130] 13 (by decide) (choices 1) [1,4,8,64,128] r8628 c8628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5602
  · exact u5603
  · exact u5604
  · exact u5605
  · exact u5606

def r8629 : Route 9 := (fun mask => (mask,id))

def c8629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8629 : Upper (D 1) (R 1) [304,80,34,132] 13 := by
  apply FastRouting.sound _ _ [304,80,34,132] 13 (by decide) (choices 1) [1,2,8,64,128] r8629 c8629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5607
  · exact u5608
  · exact u5609
  · exact u5610
  · exact u5611

def r8630 : Route 9 := (fun mask => (mask,id))

def c8630 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8630 : Upper (D 1) (R 1) [304,80,34,192] 13 := by
  apply FastRouting.sound _ _ [304,80,34,192] 13 (by decide) (choices 1) [1,2,4,8,128] r8630 c8630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5612
  · exact u5613
  · exact u5614
  · exact u5615
  · exact u5616

def b8631 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 44 73 150 166 198 134 390), lower := (rows 305 82 44 73 16 32 64 128 256), losses := [] }

theorem u8631 : Upper (D 1) (R 1) [304,80,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8631
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8632 : PairBound 9 := { available := 135, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 44 74 151 167 199 135 391), lower := (rows 305 82 44 74 16 32 64 128 256), losses := [] }

theorem u8632 : Upper (D 1) (R 1) [304,80,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8632
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8633 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 44 76 147 163 195 131 387), lower := (rows 305 82 44 76 16 32 64 128 256), losses := [] }

theorem u8633 : Upper (D 1) (R 1) [304,80,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8633
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8634 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 44 137 214 230 198 198 454), lower := (rows 305 82 44 137 16 32 64 128 256), losses := [] }

theorem u8634 : Upper (D 1) (R 1) [304,80,40,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8634
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8635 : Route 9 := (fun mask => (mask,id))

def c8635 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8635 : Upper (D 1) (R 1) [304,80,40,130] 13 := by
  apply FastRouting.sound _ _ [304,80,40,130] 13 (by decide) (choices 1) [1,2,4,64,128] r8635 c8635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5617
  · exact u5618
  · exact u5619
  · exact u5620
  · exact u5621

def b8636 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 44 140 211 227 195 195 451), lower := (rows 305 82 44 140 16 32 64 128 256), losses := [] }

theorem u8636 : Upper (D 1) (R 1) [304,80,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8636
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8637 : Route 9 := (fun mask => (mask,id))

def c8637 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8637 : Upper (D 1) (R 1) [304,80,40,192] 13 := by
  apply FastRouting.sound _ _ [304,80,40,192] 13 (by decide) (choices 1) [1,2,4,128] r8637 c8637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5622
  · exact u5623
  · exact u5624
  · exact u5625

def r8638 : Route 9 := (fun mask => (mask,id))

def c8638 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u8638 : Upper (D 1) (R 1) [304,80,65,130] 13 := by
  apply FastRouting.sound _ _ [304,80,65,130] 13 (by decide) (choices 1) [2,4,8,32,128] r8638 c8638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5626
  · exact u5627
  · exact u5628
  · exact u5629
  · exact u5630

def r8639 : Route 9 := (fun mask => (mask,id))

def c8639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8639 : Upper (D 1) (R 1) [304,80,65,132] 13 := by
  apply FastRouting.sound _ _ [304,80,65,132] 13 (by decide) (choices 1) [2,8,32,128] r8639 c8639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5631
  · exact u5632
  · exact u5633
  · exact u5634

#print axioms u8639
end Delivery.IrregularNine14.P01
