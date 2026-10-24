import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0077
import IrregularNine14P09C0078
import IrregularNine14P09C0079

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7560 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 70 140 73 49 432 464 400 400), lower := (rows 35 70 140 73 49 32 64 128 256), losses := [] }

theorem u7560 : Upper (D 9) (R 9) [34,68,136,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7560 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7561 : Route 9 := (fun mask => (mask,id))

def c7561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7561 : Upper (D 9) (R 9) [34,68,136,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,129] 13 (by decide) (choices 1) [16,256] r7561 c7561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4660
  · exact u4661

def r7562 : Route 9 := (fun mask => (mask,id))

def c7562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7562 : Upper (D 9) (R 9) [34,68,136,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,160] 13 (by decide) (choices 1) [1,16,256] r7562 c7562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4662
  · exact u4663
  · exact u4664

def r7563 : Route 9 := (fun mask => (mask,id))

def c7563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7563 : Upper (D 9) (R 9) [34,68,136,65,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,257] 13 (by decide) (choices 1) [16,128,256] r7563 c7563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4665
  · exact u4666
  · exact u4667

def r7564 : Route 9 := (fun mask => (mask,id))

def c7564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7564 : Upper (D 9) (R 9) [34,68,136,65,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,288] 13 (by decide) (choices 1) [1,16,128,256] r7564 c7564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4668
  · exact u4669
  · exact u4670
  · exact u4671

def r7565 : Route 9 := (fun mask => (mask,id))

def c7565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7565 : Upper (D 9) (R 9) [34,68,136,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,384] 13 (by decide) (choices 1) [1,16,256] r7565 c7565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4672
  · exact u4673
  · exact u4674

def b7566 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 70 140 88 49 417 449 385 385), lower := (rows 35 70 140 88 49 32 64 128 256), losses := [] }

theorem u7566 : Upper (D 9) (R 9) [34,68,136,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7566 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7567 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,7),(4,6)], upper := (rows 35 70 140 88 145 289 353 417 289), lower := (rows 35 70 140 88 145 32 64 128 256), losses := [] }

theorem u7567 : Upper (D 9) (R 9) [34,68,136,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7567 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7568 : Route 9 := (fun mask => (mask,id))

def c7568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7568 : Upper (D 9) (R 9) [34,68,136,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,160] 13 (by decide) (choices 1) [1,256] r7568 c7568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4675
  · exact u4676

def r7569 : Route 9 := (fun mask => (mask,id))

def c7569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7569 : Upper (D 9) (R 9) [34,68,136,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,257] 13 (by decide) (choices 1) [1,128,256] r7569 c7569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4677
  · exact u4678
  · exact u4679

def r7570 : Route 9 := (fun mask => (mask,id))

def c7570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7570 : Upper (D 9) (R 9) [34,68,136,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,288] 13 (by decide) (choices 1) [1,128,256] r7570 c7570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4680
  · exact u4681
  · exact u4682

def r7571 : Route 9 := (fun mask => (mask,id))

def c7571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7571 : Upper (D 9) (R 9) [34,68,136,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,384] 13 (by decide) (choices 1) [1,256] r7571 c7571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4683
  · exact u4684

def r7572 : Route 9 := (fun mask => (mask,id))

def c7572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7572 : Upper (D 9) (R 9) [34,68,136,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,129] 13 (by decide) (choices 1) [1,16,256] r7572 c7572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4685
  · exact u4686
  · exact u4687

def r7573 : Route 9 := (fun mask => (mask,id))

def c7573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7573 : Upper (D 9) (R 9) [34,68,136,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,257] 13 (by decide) (choices 1) [1,16,128,256] r7573 c7573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4688
  · exact u4689
  · exact u4690
  · exact u4691

def r7574 : Route 9 := (fun mask => (mask,id))

def c7574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7574 : Upper (D 9) (R 9) [34,68,136,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,384] 13 (by decide) (choices 1) [1,16,256] r7574 c7574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4692
  · exact u4693
  · exact u4694

def b7575 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 70 140 265 49 496 464 464 464), lower := (rows 35 70 140 265 49 32 64 128 256), losses := [] }

theorem u7575 : Upper (D 9) (R 9) [34,68,136,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7575 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7576 : Route 9 := (fun mask => (mask,id))

def c7576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7576 : Upper (D 9) (R 9) [34,68,136,257,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,65] 13 (by decide) (choices 1) [16,128,256] r7576 c7576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4695
  · exact u4696
  · exact u4697

def r7577 : Route 9 := (fun mask => (mask,id))

def c7577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7577 : Upper (D 9) (R 9) [34,68,136,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,96] 13 (by decide) (choices 1) [1,16,128,256] r7577 c7577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4698
  · exact u4699
  · exact u4700
  · exact u4701

def r7578 : Route 9 := (fun mask => (mask,id))

def c7578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7578 : Upper (D 9) (R 9) [34,68,136,257,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,129] 13 (by decide) (choices 1) [16,64,256] r7578 c7578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4702
  · exact u4703
  · exact u4704

def r7579 : Route 9 := (fun mask => (mask,id))

def c7579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7579 : Upper (D 9) (R 9) [34,68,136,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,160] 13 (by decide) (choices 1) [1,16,64,256] r7579 c7579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4705
  · exact u4706
  · exact u4707
  · exact u4708

def r7580 : Route 9 := (fun mask => (mask,id))

def c7580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7580 : Upper (D 9) (R 9) [34,68,136,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,192] 13 (by decide) (choices 1) [1,16,256] r7580 c7580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4709
  · exact u4710
  · exact u4711

def b7581 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 140 265 273 240 240 240 496), lower := (rows 35 70 140 265 273 32 64 128 256), losses := [] }

theorem u7581 : Upper (D 9) (R 9) [34,68,136,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7581 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7582 : Route 9 := (fun mask => (mask,id))

def c7582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7582 : Upper (D 9) (R 9) [34,68,136,257,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,288] 13 (by decide) (choices 1) [1,16,64,128] r7582 c7582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4712
  · exact u4713
  · exact u4714
  · exact u4715

def r7583 : Route 9 := (fun mask => (mask,id))

def c7583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7583 : Upper (D 9) (R 9) [34,68,136,257,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,320] 13 (by decide) (choices 1) [1,16,128] r7583 c7583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4716
  · exact u4717
  · exact u4718

def r7584 : Route 9 := (fun mask => (mask,id))

def c7584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7584 : Upper (D 9) (R 9) [34,68,136,257,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,384] 13 (by decide) (choices 1) [1,16,64] r7584 c7584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4719
  · exact u4720
  · exact u4721

def b7585 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 70 140 280 49 481 449 449 449), lower := (rows 35 70 140 280 49 32 64 128 256), losses := [] }

theorem u7585 : Upper (D 9) (R 9) [34,68,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7585 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7586 : Route 9 := (fun mask => (mask,id))

def c7586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7586 : Upper (D 9) (R 9) [34,68,136,272,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,65] 13 (by decide) (choices 1) [1,128,256] r7586 c7586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4722
  · exact u4723
  · exact u4724

def r7587 : Route 9 := (fun mask => (mask,id))

def c7587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7587 : Upper (D 9) (R 9) [34,68,136,272,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,96] 13 (by decide) (choices 1) [1,128,256] r7587 c7587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4725
  · exact u4726
  · exact u4727

def r7588 : Route 9 := (fun mask => (mask,id))

def c7588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7588 : Upper (D 9) (R 9) [34,68,136,272,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,129] 13 (by decide) (choices 1) [1,64,256] r7588 c7588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4728
  · exact u4729
  · exact u4730

def r7589 : Route 9 := (fun mask => (mask,id))

def c7589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7589 : Upper (D 9) (R 9) [34,68,136,272,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,160] 13 (by decide) (choices 1) [1,64,256] r7589 c7589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4731
  · exact u4732
  · exact u4733

def r7590 : Route 9 := (fun mask => (mask,id))

def c7590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7590 : Upper (D 9) (R 9) [34,68,136,272,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,192] 13 (by decide) (choices 1) [1,256] r7590 c7590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4734
  · exact u4735

def b7591 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 70 140 280 273 225 225 225 481), lower := (rows 35 70 140 280 273 32 64 128 256), losses := [] }

theorem u7591 : Upper (D 9) (R 9) [34,68,136,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7591 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7592 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 70 140 280 304 225 193 193 449), lower := (rows 35 70 140 280 304 32 64 128 256), losses := [] }

theorem u7592 : Upper (D 9) (R 9) [34,68,136,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7592 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7593 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 70 140 280 336 161 225 161 417), lower := (rows 35 70 140 280 336 32 64 128 256), losses := [] }

theorem u7593 : Upper (D 9) (R 9) [34,68,136,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7593 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7594 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0),(3,5)], upper := (rows 35 70 140 280 400 97 97 225 353), lower := (rows 35 70 140 280 400 32 64 128 256), losses := [] }

theorem u7594 : Upper (D 9) (R 9) [34,68,136,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7594 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7595 : Route 9 := (fun mask => (mask,id))

def c7595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7595 : Upper (D 9) (R 9) [34,68,136,288,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,65] 13 (by decide) (choices 1) [1,16,128,256] r7595 c7595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4736
  · exact u4737
  · exact u4738
  · exact u4739

def r7596 : Route 9 := (fun mask => (mask,id))

def c7596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7596 : Upper (D 9) (R 9) [34,68,136,288,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,129] 13 (by decide) (choices 1) [1,16,64,256] r7596 c7596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4740
  · exact u4741
  · exact u4742
  · exact u4743

def r7597 : Route 9 := (fun mask => (mask,id))

def c7597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7597 : Upper (D 9) (R 9) [34,68,136,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,192] 13 (by decide) (choices 1) [1,16,256] r7597 c7597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4744
  · exact u4745
  · exact u4746

def r7598 : Route 9 := (fun mask => (mask,id))

def c7598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7598 : Upper (D 9) (R 9) [34,68,136,288,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,257] 13 (by decide) (choices 1) [1,16,64,128] r7598 c7598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4747
  · exact u4748
  · exact u4749
  · exact u4750

def r7599 : Route 9 := (fun mask => (mask,id))

def c7599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7599 : Upper (D 9) (R 9) [34,68,136,288,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,320] 13 (by decide) (choices 1) [1,16,128] r7599 c7599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4751
  · exact u4752
  · exact u4753

def r7600 : Route 9 := (fun mask => (mask,id))

def c7600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7600 : Upper (D 9) (R 9) [34,68,136,288,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,384] 13 (by decide) (choices 1) [1,16,64] r7600 c7600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4754
  · exact u4755
  · exact u4756

def b7601 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 70 140 328 49 433 465 401 401), lower := (rows 35 70 140 328 49 32 64 128 256), losses := [] }

theorem u7601 : Upper (D 9) (R 9) [34,68,136,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7601 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7602 : Route 9 := (fun mask => (mask,id))

def c7602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7602 : Upper (D 9) (R 9) [34,68,136,320,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,129] 13 (by decide) (choices 1) [1,16,256] r7602 c7602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4757
  · exact u4758
  · exact u4759

def r7603 : Route 9 := (fun mask => (mask,id))

def c7603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7603 : Upper (D 9) (R 9) [34,68,136,320,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,160] 13 (by decide) (choices 1) [1,16,256] r7603 c7603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4760
  · exact u4761
  · exact u4762

def r7604 : Route 9 := (fun mask => (mask,id))

def c7604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7604 : Upper (D 9) (R 9) [34,68,136,320,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,257] 13 (by decide) (choices 1) [1,16,128] r7604 c7604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4763
  · exact u4764
  · exact u4765

def r7605 : Route 9 := (fun mask => (mask,id))

def c7605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7605 : Upper (D 9) (R 9) [34,68,136,320,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,288] 13 (by decide) (choices 1) [1,16,128] r7605 c7605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4766
  · exact u4767
  · exact u4768

def r7606 : Route 9 := (fun mask => (mask,id))

def c7606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7606 : Upper (D 9) (R 9) [34,68,136,320,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,384] 13 (by decide) (choices 1) [1,16] r7606 c7606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4769
  · exact u4770

def b7607 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 24, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 35 70 164 25 25 480 448 448 448), lower := (rows 35 70 164 25 25 32 64 128 256), losses := [] }

theorem u7607 : Upper (D 9) (R 9) [34,68,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7607 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7608 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 486, targets := 1 },{ cop := 4, region := 428, targets := 64 }], pairs := [(1,0),(2,0),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 25 81 424 456 392 392), lower := (rows 35 70 164 25 81 32 64 128 256), losses := [] }

theorem u7608 : Upper (D 9) (R 9) [34,68,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7608 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7609 : Route 9 := (fun mask => (mask,id))

def c7609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7609 : Upper (D 9) (R 9) [34,68,160,17,72] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,72] 13 (by decide) (choices 1) [1,128,256] r7609 c7609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4771
  · exact u4772
  · exact u4773

def b7610 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 486, targets := 1 },{ cop := 4, region := 8, targets := 64 }], pairs := [(1,0),(2,0),(3,5),(3,6),(4,5)], upper := (rows 35 70 164 25 145 360 328 456 328), lower := (rows 35 70 164 25 145 32 64 128 256), losses := [] }

theorem u7610 : Upper (D 9) (R 9) [34,68,160,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7610 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7611 : Route 9 := (fun mask => (mask,id))

def c7611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7611 : Upper (D 9) (R 9) [34,68,160,17,136] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,136] 13 (by decide) (choices 1) [1,64,256] r7611 c7611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4774
  · exact u4775
  · exact u4776

def r7612 : Route 9 := (fun mask => (mask,id))

def c7612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7612 : Upper (D 9) (R 9) [34,68,160,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,192] 13 (by decide) (choices 1) [1,8,256] r7612 c7612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4777
  · exact u4778
  · exact u4779

def b7613 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 8, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(3,6),(3,7),(3,8),(4,5)], upper := (rows 35 70 164 25 273 488 456 456 456), lower := (rows 35 70 164 25 273 32 64 128 256), losses := [] }

theorem u7613 : Upper (D 9) (R 9) [34,68,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7613 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7614 : Route 9 := (fun mask => (mask,id))

def c7614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7614 : Upper (D 9) (R 9) [34,68,160,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,264] 13 (by decide) (choices 1) [1,64,128,256] r7614 c7614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4780
  · exact u4781
  · exact u4782
  · exact u4783

def r7615 : Route 9 := (fun mask => (mask,id))

def c7615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7615 : Upper (D 9) (R 9) [34,68,160,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,320] 13 (by decide) (choices 1) [1,8,128,256] r7615 c7615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4784
  · exact u4785
  · exact u4786
  · exact u4787

def r7616 : Route 9 := (fun mask => (mask,id))

def c7616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7616 : Upper (D 9) (R 9) [34,68,160,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,384] 13 (by decide) (choices 1) [1,8,64,256] r7616 c7616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4788
  · exact u4789
  · exact u4790
  · exact u4791

def b7617 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 328, targets := 128 }], pairs := [(2,6),(3,5),(3,7),(4,5),(4,6)], upper := (rows 35 70 164 73 145 312 344 408 280), lower := (rows 35 70 164 73 145 32 64 128 256), losses := [] }

theorem u7617 : Upper (D 9) (R 9) [34,68,160,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7617 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7618 : Route 9 := (fun mask => (mask,id))

def c7618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7618 : Upper (D 9) (R 9) [34,68,160,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,136] 13 (by decide) (choices 1) [1,16,256] r7618 c7618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4792
  · exact u4793
  · exact u4794

def r7619 : Route 9 := (fun mask => (mask,id))

def c7619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u7619 : Upper (D 9) (R 9) [34,68,160,65,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,257] 13 (by decide) (choices 1) [8,16,128,256] r7619 c7619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4795
  · exact u4796
  · exact u4797
  · exact u4798

#print axioms u7619
end Delivery.IrregularNine14.P09
