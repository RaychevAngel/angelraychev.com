import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0075
import IrregularNine14P08C0076

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13560 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 152 81 162 226 162 418), lower := (rows 97 7 268 152 81 32 64 128 256), losses := [] }

theorem u13560 : Upper (D 8) (R 8) [96,5,264,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13561 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 97 7 268 152 82 161 225 161 417), lower := (rows 97 7 268 152 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 268 156 446 32 0 128 256) }] }

theorem u13561 : Upper (D 8) (R 8) [96,5,264,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13562 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 152 112 163 227 163 419), lower := (rows 97 7 268 152 112 32 64 128 256), losses := [] }

theorem u13562 : Upper (D 8) (R 8) [96,5,264,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13563 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 152 145 98 98 226 354), lower := (rows 97 7 268 152 145 32 64 128 256), losses := [] }

theorem u13563 : Upper (D 8) (R 8) [96,5,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13564 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 152 146 97 97 225 353), lower := (rows 97 7 268 152 146 32 64 128 256), losses := [] }

theorem u13564 : Upper (D 8) (R 8) [96,5,264,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13565 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 152 176 99 99 227 355), lower := (rows 97 7 268 152 176 32 64 128 256), losses := [] }

theorem u13565 : Upper (D 8) (R 8) [96,5,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13566 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 152 208 35 99 163 291), lower := (rows 97 7 268 152 208 32 64 128 256), losses := [] }

theorem u13566 : Upper (D 8) (R 8) [96,5,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13567 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 168 49 242 210 210 466), lower := (rows 97 7 268 168 49 32 64 128 256), losses := [] }

theorem u13567 : Upper (D 8) (R 8) [96,5,264,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13568 : Route 9 := (fun mask => (mask,id))

def c13568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13568 : Upper (D 8) (R 8) [96,5,264,160,34] 13 := by
  apply FastRouting.sound _ _ [96,5,264,160,34] 13 (by decide) (choices 1) [1,16,64,128] r13568 c13568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4507
  · exact u4508
  · exact u4509
  · exact u4510

def b13569 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 168 81 178 242 178 434), lower := (rows 97 7 268 168 81 32 64 128 256), losses := [] }

theorem u13569 : Upper (D 8) (R 8) [96,5,264,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13570 : Route 9 := (fun mask => (mask,id))

def c13570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13570 : Upper (D 8) (R 8) [96,5,264,160,66] 13 := by
  apply FastRouting.sound _ _ [96,5,264,160,66] 13 (by decide) (choices 1) [1,16,128] r13570 c13570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4511
  · exact u4512
  · exact u4513

def b13571 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 168 112 179 211 147 403), lower := (rows 97 7 268 168 112 32 64 128 256), losses := [] }

theorem u13571 : Upper (D 8) (R 8) [96,5,264,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13572 : Route 9 := (fun mask => (mask,id))

def c13572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13572 : Upper (D 8) (R 8) [96,5,264,160,129] 13 := by
  apply FastRouting.sound _ _ [96,5,264,160,129] 13 (by decide) (choices 1) [2,16,64] r13572 c13572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4514
  · exact u4515
  · exact u4516

def b13573 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 168 146 113 113 241 369), lower := (rows 97 7 268 168 146 32 64 128 256), losses := [] }

theorem u13573 : Upper (D 8) (R 8) [96,5,264,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13574 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 168 176 115 83 211 339), lower := (rows 97 7 268 168 176 32 64 128 256), losses := [] }

theorem u13574 : Upper (D 8) (R 8) [96,5,264,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13575 : Route 9 := (fun mask => (mask,id))

def c13575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13575 : Upper (D 8) (R 8) [96,5,264,160,192] 13 := by
  apply FastRouting.sound _ _ [96,5,264,160,192] 13 (by decide) (choices 1) [1,2,16] r13575 c13575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4517
  · exact u4518
  · exact u4519

def b13576 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 200 50 177 241 177 433), lower := (rows 97 7 268 200 50 32 64 128 256), losses := [] }

theorem u13576 : Upper (D 8) (R 8) [96,5,264,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13577 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 200 145 50 114 178 306), lower := (rows 97 7 268 200 145 32 64 128 256), losses := [] }

theorem u13577 : Upper (D 8) (R 8) [96,5,264,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13578 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 200 146 49 113 177 305), lower := (rows 97 7 268 200 146 32 64 128 256), losses := [] }

theorem u13578 : Upper (D 8) (R 8) [96,5,264,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13579 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 200 176 51 115 179 307), lower := (rows 97 7 268 200 176 32 64 128 256), losses := [] }

theorem u13579 : Upper (D 8) (R 8) [96,5,264,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13580 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 292 26 49 232 200 200 456), lower := (rows 97 7 292 26 49 32 64 128 256), losses := [] }

theorem u13580 : Upper (D 8) (R 8) [96,5,288,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13581 : Route 9 := (fun mask => (mask,id))

def c13581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13581 : Upper (D 8) (R 8) [96,5,288,18,40] 13 := by
  apply FastRouting.sound _ _ [96,5,288,18,40] 13 (by decide) (choices 1) [1,64,128] r13581 c13581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4520
  · exact u4521
  · exact u4522

def b13582 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 26 81 168 232 168 424), lower := (rows 97 7 292 26 81 32 64 128 256), losses := [] }

theorem u13582 : Upper (D 8) (R 8) [96,5,288,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13583 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 26 88 161 225 161 417), lower := (rows 97 7 292 26 88 32 64 128 256), losses := [] }

theorem u13583 : Upper (D 8) (R 8) [96,5,288,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13584 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 292 26 112 169 201 137 393), lower := (rows 97 7 292 26 112 32 64 128 256), losses := [] }

theorem u13584 : Upper (D 8) (R 8) [96,5,288,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13585 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 292 26 145 232 232 232 488), lower := (rows 97 7 292 26 145 32 64 128 256), losses := [] }

theorem u13585 : Upper (D 8) (R 8) [96,5,288,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13586 : Route 9 := (fun mask => (mask,id))

def c13586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13586 : Upper (D 8) (R 8) [96,5,288,18,136] 13 := by
  apply FastRouting.sound _ _ [96,5,288,18,136] 13 (by decide) (choices 1) [1,64,128] r13586 c13586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4523
  · exact u4524
  · exact u4525

def r13587 : Route 9 := (fun mask => (mask,id))

def c13587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13587 : Upper (D 8) (R 8) [96,5,288,18,160] 13 := by
  apply FastRouting.sound _ _ [96,5,288,18,160] 13 (by decide) (choices 1) [1,8,64,128] r13587 c13587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4526
  · exact u4527
  · exact u4528
  · exact u4529

def r13588 : Route 9 := (fun mask => (mask,id))

def c13588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13588 : Upper (D 8) (R 8) [96,5,288,18,192] 13 := by
  apply FastRouting.sound _ _ [96,5,288,18,192] 13 (by decide) (choices 1) [1,8,128] r13588 c13588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4530
  · exact u4531
  · exact u4532

def b13589 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 292 41 82 184 216 152 408), lower := (rows 97 7 292 41 82 32 64 128 256), losses := [] }

theorem u13589 : Upper (D 8) (R 8) [96,5,288,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13590 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 128 }], pairs := [(3,7)], upper := (rows 97 7 292 41 88 178 210 146 402), lower := (rows 97 7 292 41 88 32 64 128 256), losses := [] }

theorem u13590 : Upper (D 8) (R 8) [96,5,288,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13591 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 292 41 146 248 216 216 472), lower := (rows 97 7 292 41 146 32 64 128 256), losses := [] }

theorem u13591 : Upper (D 8) (R 8) [96,5,288,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13592 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 292 41 152 242 210 210 466), lower := (rows 97 7 292 41 152 32 64 128 256), losses := [] }

theorem u13592 : Upper (D 8) (R 8) [96,5,288,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13593 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 292 41 208 186 218 154 410), lower := (rows 97 7 292 41 208 32 64 128 256), losses := [] }

theorem u13593 : Upper (D 8) (R 8) [96,5,288,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13594 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 42 81 184 216 152 408), lower := (rows 97 7 292 42 81 32 64 128 256), losses := [] }

theorem u13594 : Upper (D 8) (R 8) [96,5,288,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13595 : Route 9 := (fun mask => (mask,id))

def c13595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13595 : Upper (D 8) (R 8) [96,5,288,34,72] 13 := by
  apply FastRouting.sound _ _ [96,5,288,34,72] 13 (by decide) (choices 1) [1,16,128] r13595 c13595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4533
  · exact u4534
  · exact u4535

def r13596 : Route 9 := (fun mask => (mask,id))

def c13596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u13596 : Upper (D 8) (R 8) [96,5,288,34,129] 13 := by
  apply FastRouting.sound _ _ [96,5,288,34,129] 13 (by decide) (choices 1) [8,16,64,128] r13596 c13596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4536
  · exact u4537
  · exact u4538
  · exact u4539

def r13597 : Route 9 := (fun mask => (mask,id))

def c13597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13597 : Upper (D 8) (R 8) [96,5,288,34,136] 13 := by
  apply FastRouting.sound _ _ [96,5,288,34,136] 13 (by decide) (choices 1) [1,16,64,128] r13597 c13597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4540
  · exact u4541
  · exact u4542
  · exact u4543

def r13598 : Route 9 := (fun mask => (mask,id))

def c13598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13598 : Upper (D 8) (R 8) [96,5,288,34,192] 13 := by
  apply FastRouting.sound _ _ [96,5,288,34,192] 13 (by decide) (choices 1) [1,8,16,128] r13598 c13598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4544
  · exact u4545
  · exact u4546
  · exact u4547

def b13599 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 56 81 170 202 138 394), lower := (rows 97 7 292 56 81 32 64 128 256), losses := [] }

theorem u13599 : Upper (D 8) (R 8) [96,5,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13600 : Route 9 := (fun mask => (mask,id))

def c13600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13600 : Upper (D 8) (R 8) [96,5,288,48,66] 13 := by
  apply FastRouting.sound _ _ [96,5,288,48,66] 13 (by decide) (choices 1) [1,8,128] r13600 c13600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4548
  · exact u4549
  · exact u4550

def b13601 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 292 56 88 163 195 131 387), lower := (rows 97 7 292 56 88 32 64 128 256), losses := [] }

theorem u13601 : Upper (D 8) (R 8) [96,5,288,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13602 : Route 9 := (fun mask => (mask,id))

def c13602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13602 : Upper (D 8) (R 8) [96,5,288,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,288,48,129] 13 (by decide) (choices 1) [2,8,64,128] r13602 c13602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4551
  · exact u4552
  · exact u4553
  · exact u4554

def r13603 : Route 9 := (fun mask => (mask,id))

def c13603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13603 : Upper (D 8) (R 8) [96,5,288,48,130] 13 := by
  apply FastRouting.sound _ _ [96,5,288,48,130] 13 (by decide) (choices 1) [1,8,64,128] r13603 c13603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4555
  · exact u4556
  · exact u4557
  · exact u4558

def r13604 : Route 9 := (fun mask => (mask,id))

def c13604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13604 : Upper (D 8) (R 8) [96,5,288,48,136] 13 := by
  apply FastRouting.sound _ _ [96,5,288,48,136] 13 (by decide) (choices 1) [1,2,64,128] r13604 c13604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4559
  · exact u4560
  · exact u4561
  · exact u4562

def r13605 : Route 9 := (fun mask => (mask,id))

def c13605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13605 : Upper (D 8) (R 8) [96,5,288,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,288,48,192] 13 (by decide) (choices 1) [1,2,8,128] r13605 c13605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4563
  · exact u4564
  · exact u4565
  · exact u4566

def b13606 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 73 146 184 248 184 440), lower := (rows 97 7 292 73 146 32 64 128 256), losses := [] }

theorem u13606 : Upper (D 8) (R 8) [96,5,288,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13607 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 73 152 178 242 178 434), lower := (rows 97 7 292 73 152 32 64 128 256), losses := [] }

theorem u13607 : Upper (D 8) (R 8) [96,5,288,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13608 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 73 176 186 218 154 410), lower := (rows 97 7 292 73 176 32 64 128 256), losses := [] }

theorem u13608 : Upper (D 8) (R 8) [96,5,288,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13609 : Route 9 := (fun mask => (mask,id))

def c13609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13609 : Upper (D 8) (R 8) [96,5,288,66,129] 13 := by
  apply FastRouting.sound _ _ [96,5,288,66,129] 13 (by decide) (choices 1) [8,16,128] r13609 c13609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4567
  · exact u4568
  · exact u4569

def r13610 : Route 9 := (fun mask => (mask,id))

def c13610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13610 : Upper (D 8) (R 8) [96,5,288,66,136] 13 := by
  apply FastRouting.sound _ _ [96,5,288,66,136] 13 (by decide) (choices 1) [1,16,128] r13610 c13610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4570
  · exact u4571
  · exact u4572

def r13611 : Route 9 := (fun mask => (mask,id))

def c13611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13611 : Upper (D 8) (R 8) [96,5,288,66,160] 13 := by
  apply FastRouting.sound _ _ [96,5,288,66,160] 13 (by decide) (choices 1) [1,8,16,128] r13611 c13611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4573
  · exact u4574
  · exact u4575
  · exact u4576

def r13612 : Route 9 := (fun mask => (mask,id))

def c13612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13612 : Upper (D 8) (R 8) [96,5,288,80,129] 13 := by
  apply FastRouting.sound _ _ [96,5,288,80,129] 13 (by decide) (choices 1) [2,8,128] r13612 c13612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4577
  · exact u4578
  · exact u4579

def r13613 : Route 9 := (fun mask => (mask,id))

def c13613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13613 : Upper (D 8) (R 8) [96,5,288,80,130] 13 := by
  apply FastRouting.sound _ _ [96,5,288,80,130] 13 (by decide) (choices 1) [1,8,128] r13613 c13613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4580
  · exact u4581
  · exact u4582

def b13614 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 88 152 163 227 163 419), lower := (rows 97 7 292 88 152 32 64 128 256), losses := [] }

theorem u13614 : Upper (D 8) (R 8) [96,5,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13615 : Route 9 := (fun mask => (mask,id))

def c13615 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13615 : Upper (D 8) (R 8) [96,5,288,80,160] 13 := by
  apply FastRouting.sound _ _ [96,5,288,80,160] 13 (by decide) (choices 1) [1,2,8,128] r13615 c13615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4583
  · exact u4584
  · exact u4585
  · exact u4586

def b13616 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 292 104 145 186 218 154 410), lower := (rows 97 7 292 104 145 32 64 128 256), losses := [] }

theorem u13616 : Upper (D 8) (R 8) [96,5,288,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13617 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 292 104 146 185 217 153 409), lower := (rows 97 7 292 104 146 32 64 128 256), losses := [] }

theorem u13617 : Upper (D 8) (R 8) [96,5,288,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13618 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 292 104 152 179 211 147 403), lower := (rows 97 7 292 104 152 32 64 128 256), losses := [] }

theorem u13618 : Upper (D 8) (R 8) [96,5,288,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13619 : Route 9 := (fun mask => (mask,id))

def c13619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13619 : Upper (D 8) (R 8) [96,5,288,129,130] 13 := by
  apply FastRouting.sound _ _ [96,5,288,129,130] 13 (by decide) (choices 1) [8,16,64] r13619 c13619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4587
  · exact u4588
  · exact u4589

#print axioms u13619
end Delivery.IrregularNine14.P08
