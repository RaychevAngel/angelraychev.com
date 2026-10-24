import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0376
import IrregularNine14P06C0377
import IrregularNine14P06C0378

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37380 : Route 9 := (fun mask => (mask,id))

def c37380 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37380 : Upper (D 6) (R 6) [34,129,264,36,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,36,65] 13 (by decide) (choices 1) [2,4,16,64] r37380 c37380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22561
  · exact u22562
  · exact u22563
  · exact u22564

def r37381 : Route 9 := (fun mask => (mask,id))

def c37381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37381 : Upper (D 6) (R 6) [34,129,264,36,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,36,66] 13 (by decide) (choices 1) [1,4,16,64] r37381 c37381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22565
  · exact u22566
  · exact u22567
  · exact u22568

def r37382 : Route 9 := (fun mask => (mask,id))

def c37382 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37382 : Upper (D 6) (R 6) [34,129,264,36,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,36,68] 13 (by decide) (choices 1) [1,2,16,64] r37382 c37382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22569
  · exact u22570
  · exact u22571
  · exact u22572

def b37383 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 268 56 19 100 68 196 324), lower := (rows 35 131 268 56 19 32 64 128 256), losses := [] }

theorem u37383 : Upper (D 6) (R 6) [34,129,264,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37384 : Route 9 := (fun mask => (mask,id))

def c37384 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37384 : Upper (D 6) (R 6) [34,129,264,48,5] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,5] 13 (by decide) (choices 1) [2,4,64] r37384 c37384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22573
  · exact u22574
  · exact u22575

def r37385 : Route 9 := (fun mask => (mask,id))

def c37385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37385 : Upper (D 6) (R 6) [34,129,264,48,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,6] 13 (by decide) (choices 1) [1,4,64] r37385 c37385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22576
  · exact u22577
  · exact u22578

def r37386 : Route 9 := (fun mask => (mask,id))

def c37386 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37386 : Upper (D 6) (R 6) [34,129,264,48,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,65] 13 (by decide) (choices 1) [2,4,64] r37386 c37386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22579
  · exact u22580
  · exact u22581

def r37387 : Route 9 := (fun mask => (mask,id))

def c37387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37387 : Upper (D 6) (R 6) [34,129,264,48,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,66] 13 (by decide) (choices 1) [1,4,64] r37387 c37387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22582
  · exact u22583
  · exact u22584

def r37388 : Route 9 := (fun mask => (mask,id))

def c37388 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37388 : Upper (D 6) (R 6) [34,129,264,48,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,68] 13 (by decide) (choices 1) [1,2,4,64] r37388 c37388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22585
  · exact u22586
  · exact u22587
  · exact u22588

def r37389 : Route 9 := (fun mask => (mask,id))

def c37389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37389 : Upper (D 6) (R 6) [34,129,264,65,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,6] 13 (by decide) (choices 1) [4,16,64] r37389 c37389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22589
  · exact u22590
  · exact u22591

def b37390 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 268 73 50 116 84 212 340), lower := (rows 35 131 268 73 50 32 64 128 256), losses := [] }

theorem u37390 : Upper (D 6) (R 6) [34,129,264,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37391 : Route 9 := (fun mask => (mask,id))

def c37391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37391 : Upper (D 6) (R 6) [34,129,264,65,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,36] 13 (by decide) (choices 1) [2,4,16,64] r37391 c37391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22592
  · exact u22593
  · exact u22594
  · exact u22595

def r37392 : Route 9 := (fun mask => (mask,id))

def c37392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37392 : Upper (D 6) (R 6) [34,129,264,65,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,66] 13 (by decide) (choices 1) [4,16] r37392 c37392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22596
  · exact u22597

def r37393 : Route 9 := (fun mask => (mask,id))

def c37393 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37393 : Upper (D 6) (R 6) [34,129,264,65,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,68] 13 (by decide) (choices 1) [2,4,16] r37393 c37393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22598
  · exact u22599
  · exact u22600

def r37394 : Route 9 := (fun mask => (mask,id))

def c37394 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37394 : Upper (D 6) (R 6) [34,129,264,65,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,96] 13 (by decide) (choices 1) [2,4,16] r37394 c37394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22601
  · exact u22602
  · exact u22603

def r37395 : Route 9 := (fun mask => (mask,id))

def c37395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37395 : Upper (D 6) (R 6) [34,129,264,66,5] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,5] 13 (by decide) (choices 1) [4,16,64] r37395 c37395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22604
  · exact u22605
  · exact u22606

def b37396 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 268 74 49 116 84 212 340), lower := (rows 35 131 268 74 49 32 64 128 256), losses := [] }

theorem u37396 : Upper (D 6) (R 6) [34,129,264,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37397 : Route 9 := (fun mask => (mask,id))

def c37397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37397 : Upper (D 6) (R 6) [34,129,264,66,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,36] 13 (by decide) (choices 1) [1,4,16,64] r37397 c37397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22607
  · exact u22608
  · exact u22609
  · exact u22610

def r37398 : Route 9 := (fun mask => (mask,id))

def c37398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37398 : Upper (D 6) (R 6) [34,129,264,66,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,65] 13 (by decide) (choices 1) [4,16] r37398 c37398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22611
  · exact u22612

def r37399 : Route 9 := (fun mask => (mask,id))

def c37399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37399 : Upper (D 6) (R 6) [34,129,264,66,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,68] 13 (by decide) (choices 1) [1,4,16] r37399 c37399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22613
  · exact u22614
  · exact u22615

def r37400 : Route 9 := (fun mask => (mask,id))

def c37400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37400 : Upper (D 6) (R 6) [34,129,264,66,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,96] 13 (by decide) (choices 1) [1,4,16] r37400 c37400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22616
  · exact u22617
  · exact u22618

def b37401 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 76 19 116 116 244 372), lower := (rows 35 131 268 76 19 32 64 128 256), losses := [] }

theorem u37401 : Upper (D 6) (R 6) [34,129,264,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37402 : Route 9 := (fun mask => (mask,id))

def c37402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37402 : Upper (D 6) (R 6) [34,129,264,68,5] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68,5] 13 (by decide) (choices 1) [2,16,64] r37402 c37402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22619
  · exact u22620
  · exact u22621

def r37403 : Route 9 := (fun mask => (mask,id))

def c37403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37403 : Upper (D 6) (R 6) [34,129,264,68,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68,6] 13 (by decide) (choices 1) [1,16,64] r37403 c37403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22622
  · exact u22623
  · exact u22624

def b37404 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 268 76 49 118 86 214 342), lower := (rows 35 131 268 76 49 32 64 128 256), losses := [] }

theorem u37404 : Upper (D 6) (R 6) [34,129,264,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37405 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 268 76 50 117 85 213 341), lower := (rows 35 131 268 76 50 32 64 128 256), losses := [] }

theorem u37405 : Upper (D 6) (R 6) [34,129,264,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37406 : Route 9 := (fun mask => (mask,id))

def c37406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37406 : Upper (D 6) (R 6) [34,129,264,68,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68,36] 13 (by decide) (choices 1) [1,2,16,64] r37406 c37406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22625
  · exact u22626
  · exact u22627
  · exact u22628

def r37407 : Route 9 := (fun mask => (mask,id))

def c37407 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37407 : Upper (D 6) (R 6) [34,129,264,68,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68,65] 13 (by decide) (choices 1) [2,4,16] r37407 c37407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22629
  · exact u22630
  · exact u22631

def r37408 : Route 9 := (fun mask => (mask,id))

def c37408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37408 : Upper (D 6) (R 6) [34,129,264,68,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68,66] 13 (by decide) (choices 1) [1,4,16] r37408 c37408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22632
  · exact u22633
  · exact u22634

def b37409 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 268 76 84 51 115 179 307), lower := (rows 35 131 268 76 84 32 64 128 256), losses := [] }

theorem u37409 : Upper (D 6) (R 6) [34,129,264,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37410 : Route 9 := (fun mask => (mask,id))

def c37410 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37410 : Upper (D 6) (R 6) [34,129,264,68,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68,96] 13 (by decide) (choices 1) [1,2,4,16] r37410 c37410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22635
  · exact u22636
  · exact u22637
  · exact u22638

def b37411 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 88 19 100 100 228 356), lower := (rows 35 131 268 88 19 32 64 128 256), losses := [] }

theorem u37411 : Upper (D 6) (R 6) [34,129,264,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37412 : Route 9 := (fun mask => (mask,id))

def c37412 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37412 : Upper (D 6) (R 6) [34,129,264,80,5] 13 := by
  apply FastRouting.sound _ _ [34,129,264,80,5] 13 (by decide) (choices 1) [2,4,64] r37412 c37412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22639
  · exact u22640
  · exact u22641

def r37413 : Route 9 := (fun mask => (mask,id))

def c37413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37413 : Upper (D 6) (R 6) [34,129,264,80,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,80,6] 13 (by decide) (choices 1) [1,4,64] r37413 c37413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22642
  · exact u22643
  · exact u22644

def b37414 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 268 88 49 102 70 198 326), lower := (rows 35 131 268 88 49 32 64 128 256), losses := [] }

theorem u37414 : Upper (D 6) (R 6) [34,129,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37415 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 268 88 50 101 69 197 325), lower := (rows 35 131 268 88 50 32 64 128 256), losses := [] }

theorem u37415 : Upper (D 6) (R 6) [34,129,264,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37416 : Route 9 := (fun mask => (mask,id))

def c37416 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37416 : Upper (D 6) (R 6) [34,129,264,80,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,80,36] 13 (by decide) (choices 1) [1,2,4,64] r37416 c37416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22645
  · exact u22646
  · exact u22647
  · exact u22648

def b37417 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 268 88 81 38 102 166 294), lower := (rows 35 131 268 88 81 32 64 128 256), losses := [] }

theorem u37417 : Upper (D 6) (R 6) [34,129,264,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37418 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 268 88 82 37 101 165 293), lower := (rows 35 131 268 88 82 32 64 128 256), losses := [] }

theorem u37418 : Upper (D 6) (R 6) [34,129,264,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37419 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 268 88 84 39 103 167 295), lower := (rows 35 131 268 88 84 32 64 128 256), losses := [] }

theorem u37419 : Upper (D 6) (R 6) [34,129,264,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37420 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 268 88 112 39 71 135 263), lower := (rows 35 131 268 88 112 32 64 128 256), losses := [] }

theorem u37420 : Upper (D 6) (R 6) [34,129,264,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37421 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 104 19 116 84 212 340), lower := (rows 35 131 268 104 19 32 64 128 256), losses := [] }

theorem u37421 : Upper (D 6) (R 6) [34,129,264,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37422 : Route 9 := (fun mask => (mask,id))

def c37422 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37422 : Upper (D 6) (R 6) [34,129,264,96,5] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,5] 13 (by decide) (choices 1) [2,4,16,64] r37422 c37422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22649
  · exact u22650
  · exact u22651
  · exact u22652

def r37423 : Route 9 := (fun mask => (mask,id))

def c37423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37423 : Upper (D 6) (R 6) [34,129,264,96,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,6] 13 (by decide) (choices 1) [1,4,16,64] r37423 c37423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22653
  · exact u22654
  · exact u22655
  · exact u22656

def r37424 : Route 9 := (fun mask => (mask,id))

def c37424 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37424 : Upper (D 6) (R 6) [34,129,264,96,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,65] 13 (by decide) (choices 1) [2,4,16] r37424 c37424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22657
  · exact u22658
  · exact u22659

def r37425 : Route 9 := (fun mask => (mask,id))

def c37425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37425 : Upper (D 6) (R 6) [34,129,264,96,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,66] 13 (by decide) (choices 1) [1,4,16] r37425 c37425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22660
  · exact u22661
  · exact u22662

def r37426 : Route 9 := (fun mask => (mask,id))

def c37426 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37426 : Upper (D 6) (R 6) [34,129,264,96,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96,68] 13 (by decide) (choices 1) [1,2,4,16] r37426 c37426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22663
  · exact u22664
  · exact u22665
  · exact u22666

def b37427 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 292 11 28 116 84 212 340), lower := (rows 35 131 292 11 28 32 64 128 256), losses := [] }

theorem u37427 : Upper (D 6) (R 6) [34,129,288,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37428 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 292 11 84 124 92 220 348), lower := (rows 35 131 292 11 84 32 64 128 256), losses := [] }

theorem u37428 : Upper (D 6) (R 6) [34,129,288,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37429 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 292 11 88 116 84 212 340), lower := (rows 35 131 292 11 88 32 64 128 256), losses := [] }

theorem u37429 : Upper (D 6) (R 6) [34,129,288,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37430 : Route 9 := (fun mask => (mask,id))

def c37430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37430 : Upper (D 6) (R 6) [34,129,288,5,6] 13 := by
  apply FastRouting.sound _ _ [34,129,288,5,6] 13 (by decide) (choices 1) [8,16,64] r37430 c37430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22667
  · exact u22668
  · exact u22669

def b37431 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 35 131 292 13 26 116 84 212 340), lower := (rows 35 131 292 13 26 32 64 128 256), losses := [] }

theorem u37431 : Upper (D 6) (R 6) [34,129,288,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37432 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 292 13 28 114 82 210 338), lower := (rows 35 131 292 13 28 32 64 128 256), losses := [] }

theorem u37432 : Upper (D 6) (R 6) [34,129,288,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37433 : Route 9 := (fun mask => (mask,id))

def c37433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37433 : Upper (D 6) (R 6) [34,129,288,5,66] 13 := by
  apply FastRouting.sound _ _ [34,129,288,5,66] 13 (by decide) (choices 1) [4,8,16,64] r37433 c37433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22670
  · exact u22671
  · exact u22672
  · exact u22673

def r37434 : Route 9 := (fun mask => (mask,id))

def c37434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37434 : Upper (D 6) (R 6) [34,129,288,5,68] 13 := by
  apply FastRouting.sound _ _ [34,129,288,5,68] 13 (by decide) (choices 1) [2,8,16,64] r37434 c37434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22674
  · exact u22675
  · exact u22676
  · exact u22677

def r37435 : Route 9 := (fun mask => (mask,id))

def c37435 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37435 : Upper (D 6) (R 6) [34,129,288,5,72] 13 := by
  apply FastRouting.sound _ _ [34,129,288,5,72] 13 (by decide) (choices 1) [2,4,16,64] r37435 c37435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22678
  · exact u22679
  · exact u22680
  · exact u22681

def r37436 : Route 9 := (fun mask => (mask,id))

def c37436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37436 : Upper (D 6) (R 6) [34,129,288,6,9] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,9] 13 (by decide) (choices 1) [4,16,64] r37436 c37436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22682
  · exact u22683
  · exact u22684

def b37437 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 292 14 28 113 81 209 337), lower := (rows 35 131 292 14 28 32 64 128 256), losses := [] }

theorem u37437 : Upper (D 6) (R 6) [34,129,288,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37438 : Route 9 := (fun mask => (mask,id))

def c37438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37438 : Upper (D 6) (R 6) [34,129,288,6,65] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,65] 13 (by decide) (choices 1) [4,8,16,64] r37438 c37438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22685
  · exact u22686
  · exact u22687
  · exact u22688

def r37439 : Route 9 := (fun mask => (mask,id))

def c37439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37439 : Upper (D 6) (R 6) [34,129,288,6,68] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,68] 13 (by decide) (choices 1) [1,8,16,64] r37439 c37439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22689
  · exact u22690
  · exact u22691
  · exact u22692

#print axioms u37439
end Delivery.IrregularNine14.P06
