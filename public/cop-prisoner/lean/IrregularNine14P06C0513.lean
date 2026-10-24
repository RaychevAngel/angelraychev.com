import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0209
import IrregularNine14P06C0210

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30780 : Route 9 := (fun mask => (mask,id))

def c30780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30780 : Upper (D 6) (R 6) [10,33,130,260,68] 13 := by
  apply FastRouting.sound _ _ [10,33,130,260,68] 13 (by decide) (choices 1) [1,16,64] r30780 c30780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12562
  · exact u12563
  · exact u12564

def r30781 : Route 9 := (fun mask => (mask,id))

def c30781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30781 : Upper (D 6) (R 6) [10,33,130,260,96] 13 := by
  apply FastRouting.sound _ _ [10,33,130,260,96] 13 (by decide) (choices 1) [1,4,16,64] r30781 c30781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12565
  · exact u12566
  · exact u12567
  · exact u12568

def b30782 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 134 280 21 100 100 228 356), lower := (rows 11 35 134 280 21 32 64 128 256), losses := [] }

theorem u30782 : Upper (D 6) (R 6) [10,33,130,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30783 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 134 280 49 100 68 196 324), lower := (rows 11 35 134 280 49 32 64 128 256), losses := [] }

theorem u30783 : Upper (D 6) (R 6) [10,33,130,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30784 : Route 9 := (fun mask => (mask,id))

def c30784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30784 : Upper (D 6) (R 6) [10,33,130,272,36] 13 := by
  apply FastRouting.sound _ _ [10,33,130,272,36] 13 (by decide) (choices 1) [1,4,64] r30784 c30784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12569
  · exact u12570
  · exact u12571

def r30785 : Route 9 := (fun mask => (mask,id))

def c30785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30785 : Upper (D 6) (R 6) [10,33,130,272,65] 13 := by
  apply FastRouting.sound _ _ [10,33,130,272,65] 13 (by decide) (choices 1) [4,64] r30785 c30785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12572
  · exact u12573

def r30786 : Route 9 := (fun mask => (mask,id))

def c30786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30786 : Upper (D 6) (R 6) [10,33,130,272,68] 13 := by
  apply FastRouting.sound _ _ [10,33,130,272,68] 13 (by decide) (choices 1) [1,4,64] r30786 c30786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12574
  · exact u12575
  · exact u12576

def r30787 : Route 9 := (fun mask => (mask,id))

def c30787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30787 : Upper (D 6) (R 6) [10,33,130,272,96] 13 := by
  apply FastRouting.sound _ _ [10,33,130,272,96] 13 (by decide) (choices 1) [1,4,64] r30787 c30787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12577
  · exact u12578
  · exact u12579

def r30788 : Route 9 := (fun mask => (mask,id))

def c30788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30788 : Upper (D 6) (R 6) [10,33,130,320,5] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,5] 13 (by decide) (choices 1) [4,16,64] r30788 c30788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12580
  · exact u12581
  · exact u12582

def b30789 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 134 328 49 116 84 212 340), lower := (rows 11 35 134 328 49 32 64 128 256), losses := [] }

theorem u30789 : Upper (D 6) (R 6) [10,33,130,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30790 : Route 9 := (fun mask => (mask,id))

def c30790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30790 : Upper (D 6) (R 6) [10,33,130,320,36] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,36] 13 (by decide) (choices 1) [1,4,16,64] r30790 c30790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12583
  · exact u12584
  · exact u12585
  · exact u12586

def r30791 : Route 9 := (fun mask => (mask,id))

def c30791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30791 : Upper (D 6) (R 6) [10,33,130,320,65] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,65] 13 (by decide) (choices 1) [4,16] r30791 c30791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12587
  · exact u12588

def r30792 : Route 9 := (fun mask => (mask,id))

def c30792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30792 : Upper (D 6) (R 6) [10,33,130,320,68] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,68] 13 (by decide) (choices 1) [1,4,16] r30792 c30792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12589
  · exact u12590
  · exact u12591

def r30793 : Route 9 := (fun mask => (mask,id))

def c30793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30793 : Upper (D 6) (R 6) [10,33,130,320,96] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,96] 13 (by decide) (choices 1) [1,4,16] r30793 c30793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12592
  · exact u12593
  · exact u12594

def b30794 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 148 13 22 352 352 480 352), lower := (rows 11 35 148 13 22 32 64 128 256), losses := [] }

theorem u30794 : Upper (D 6) (R 6) [10,33,144,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30795 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 148 13 50 356 324 452 324), lower := (rows 11 35 148 13 50 32 64 128 256), losses := [] }

theorem u30795 : Upper (D 6) (R 6) [10,33,144,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30796 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 148 13 52 354 322 450 322), lower := (rows 11 35 148 13 52 32 64 128 256), losses := [] }

theorem u30796 : Upper (D 6) (R 6) [10,33,144,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30797 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 420, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 13 82 356 356 484 356), lower := (rows 11 35 148 13 82 32 64 128 256), losses := [] }

theorem u30797 : Upper (D 6) (R 6) [10,33,144,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30798 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 148 13 84 354 354 482 354), lower := (rows 11 35 148 13 84 32 64 128 256), losses := [] }

theorem u30798 : Upper (D 6) (R 6) [10,33,144,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30799 : Route 9 := (fun mask => (mask,id))

def c30799 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30799 : Upper (D 6) (R 6) [10,33,144,5,96] 13 := by
  apply FastRouting.sound _ _ [10,33,144,5,96] 13 (by decide) (choices 1) [2,4,64,256] r30799 c30799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12595
  · exact u12596
  · exact u12597
  · exact u12598

def b30800 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 13 274 100 100 228 356), lower := (rows 11 35 148 13 274 32 64 128 256), losses := [] }

theorem u30800 : Upper (D 6) (R 6) [10,33,144,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30801 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 148 13 276 98 98 226 354), lower := (rows 11 35 148 13 276 32 64 128 256), losses := [] }

theorem u30801 : Upper (D 6) (R 6) [10,33,144,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30802 : Route 9 := (fun mask => (mask,id))

def c30802 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30802 : Upper (D 6) (R 6) [10,33,144,5,288] 13 := by
  apply FastRouting.sound _ _ [10,33,144,5,288] 13 (by decide) (choices 1) [2,4,64] r30802 c30802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12599
  · exact u12600
  · exact u12601

def r30803 : Route 9 := (fun mask => (mask,id))

def c30803 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30803 : Upper (D 6) (R 6) [10,33,144,5,320] 13 := by
  apply FastRouting.sound _ _ [10,33,144,5,320] 13 (by decide) (choices 1) [2,4,64] r30803 c30803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12602
  · exact u12603
  · exact u12604

def b30804 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 73 22 356 356 484 356), lower := (rows 11 35 148 73 22 32 64 128 256), losses := [] }

theorem u30804 : Upper (D 6) (R 6) [10,33,144,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30805 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 148 73 50 356 324 452 324), lower := (rows 11 35 148 73 50 32 64 128 256), losses := [] }

theorem u30805 : Upper (D 6) (R 6) [10,33,144,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30806 : Route 9 := (fun mask => (mask,id))

def c30806 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30806 : Upper (D 6) (R 6) [10,33,144,65,36] 13 := by
  apply FastRouting.sound _ _ [10,33,144,65,36] 13 (by decide) (choices 1) [2,4,64,256] r30806 c30806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12605
  · exact u12606
  · exact u12607
  · exact u12608

def b30807 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 148 73 82 292 356 420 292), lower := (rows 11 35 148 73 82 32 64 128 256), losses := [] }

theorem u30807 : Upper (D 6) (R 6) [10,33,144,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30808 : Route 9 := (fun mask => (mask,id))

def c30808 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30808 : Upper (D 6) (R 6) [10,33,144,65,68] 13 := by
  apply FastRouting.sound _ _ [10,33,144,65,68] 13 (by decide) (choices 1) [2,4,256] r30808 c30808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12609
  · exact u12610
  · exact u12611

def b30809 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 73 112 294 326 390 262), lower := (rows 11 35 148 73 112 32 64 128 256), losses := [] }

theorem u30809 : Upper (D 6) (R 6) [10,33,144,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30810 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 73 274 100 100 228 356), lower := (rows 11 35 148 73 274 32 64 128 256), losses := [] }

theorem u30810 : Upper (D 6) (R 6) [10,33,144,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30811 : Route 9 := (fun mask => (mask,id))

def c30811 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30811 : Upper (D 6) (R 6) [10,33,144,65,260] 13 := by
  apply FastRouting.sound _ _ [10,33,144,65,260] 13 (by decide) (choices 1) [2,4,64] r30811 c30811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12612
  · exact u12613
  · exact u12614

def r30812 : Route 9 := (fun mask => (mask,id))

def c30812 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30812 : Upper (D 6) (R 6) [10,33,144,65,288] 13 := by
  apply FastRouting.sound _ _ [10,33,144,65,288] 13 (by decide) (choices 1) [2,4,64] r30812 c30812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12615
  · exact u12616
  · exact u12617

def r30813 : Route 9 := (fun mask => (mask,id))

def c30813 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30813 : Upper (D 6) (R 6) [10,33,144,65,320] 13 := by
  apply FastRouting.sound _ _ [10,33,144,65,320] 13 (by decide) (choices 1) [2,4] r30813 c30813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12618
  · exact u12619

def b30814 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 148 76 19 356 356 484 356), lower := (rows 11 35 148 76 19 32 64 128 256), losses := [] }

theorem u30814 : Upper (D 6) (R 6) [10,33,144,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30815 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 291, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 148 76 21 354 354 482 354), lower := (rows 11 35 148 76 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 490 482 156 76 508 32 64 128 256) }] }

theorem u30815 : Upper (D 6) (R 6) [10,33,144,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30816 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 291, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 148 76 22 353 353 481 353), lower := (rows 11 35 148 76 22 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 489 481 156 76 508 32 64 128 256) }] }

theorem u30816 : Upper (D 6) (R 6) [10,33,144,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30817 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 148 76 49 358 326 454 326), lower := (rows 11 35 148 76 49 32 64 128 256), losses := [] }

theorem u30817 : Upper (D 6) (R 6) [10,33,144,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30818 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 148 76 50 357 325 453 325), lower := (rows 11 35 148 76 50 32 64 128 256), losses := [] }

theorem u30818 : Upper (D 6) (R 6) [10,33,144,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30819 : Route 9 := (fun mask => (mask,id))

def c30819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30819 : Upper (D 6) (R 6) [10,33,144,68,36] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68,36] 13 (by decide) (choices 1) [1,2,64,256] r30819 c30819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12620
  · exact u12621
  · exact u12622
  · exact u12623

def b30820 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 148 76 81 294 358 422 294), lower := (rows 11 35 148 76 81 32 64 128 256), losses := [] }

theorem u30820 : Upper (D 6) (R 6) [10,33,144,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30821 : Route 9 := (fun mask => (mask,id))

def c30821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30821 : Upper (D 6) (R 6) [10,33,144,68,66] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68,66] 13 (by decide) (choices 1) [1,4,256] r30821 c30821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12624
  · exact u12625
  · exact u12626

def b30822 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 148 76 84 291 355 419 291), lower := (rows 11 35 148 76 84 32 64 128 256), losses := [] }

theorem u30822 : Upper (D 6) (R 6) [10,33,144,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30823 : Route 9 := (fun mask => (mask,id))

def c30823 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30823 : Upper (D 6) (R 6) [10,33,144,68,96] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68,96] 13 (by decide) (choices 1) [1,2,4,256] r30823 c30823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12627
  · exact u12628
  · exact u12629
  · exact u12630

def r30824 : Route 9 := (fun mask => (mask,id))

def c30824 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30824 : Upper (D 6) (R 6) [10,33,144,68,257] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68,257] 13 (by decide) (choices 1) [2,4,64] r30824 c30824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12631
  · exact u12632
  · exact u12633

def r30825 : Route 9 := (fun mask => (mask,id))

def c30825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30825 : Upper (D 6) (R 6) [10,33,144,68,258] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68,258] 13 (by decide) (choices 1) [1,4,64] r30825 c30825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12634
  · exact u12635
  · exact u12636

def r30826 : Route 9 := (fun mask => (mask,id))

def c30826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30826 : Upper (D 6) (R 6) [10,33,144,68,260] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68,260] 13 (by decide) (choices 1) [1,2,64] r30826 c30826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12637
  · exact u12638
  · exact u12639

def r30827 : Route 9 := (fun mask => (mask,id))

def c30827 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30827 : Upper (D 6) (R 6) [10,33,144,68,288] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68,288] 13 (by decide) (choices 1) [1,2,4,64] r30827 c30827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12640
  · exact u12641
  · exact u12642
  · exact u12643

def r30828 : Route 9 := (fun mask => (mask,id))

def c30828 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30828 : Upper (D 6) (R 6) [10,33,144,68,320] 13 := by
  apply FastRouting.sound _ _ [10,33,144,68,320] 13 (by decide) (choices 1) [1,2,4] r30828 c30828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12644
  · exact u12645
  · exact u12646

def b30829 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 265 22 100 100 228 356), lower := (rows 11 35 148 265 22 32 64 128 256), losses := [] }

theorem u30829 : Upper (D 6) (R 6) [10,33,144,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30830 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 148 265 50 100 68 196 324), lower := (rows 11 35 148 265 50 32 64 128 256), losses := [] }

theorem u30830 : Upper (D 6) (R 6) [10,33,144,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30831 : Route 9 := (fun mask => (mask,id))

def c30831 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30831 : Upper (D 6) (R 6) [10,33,144,257,36] 13 := by
  apply FastRouting.sound _ _ [10,33,144,257,36] 13 (by decide) (choices 1) [2,4,64] r30831 c30831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12647
  · exact u12648
  · exact u12649

def b30832 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 265 82 100 100 228 356), lower := (rows 11 35 148 265 82 32 64 128 256), losses := [] }

theorem u30832 : Upper (D 6) (R 6) [10,33,144,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30833 : Route 9 := (fun mask => (mask,id))

def c30833 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30833 : Upper (D 6) (R 6) [10,33,144,257,68] 13 := by
  apply FastRouting.sound _ _ [10,33,144,257,68] 13 (by decide) (choices 1) [2,4,64] r30833 c30833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12650
  · exact u12651
  · exact u12652

def r30834 : Route 9 := (fun mask => (mask,id))

def c30834 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30834 : Upper (D 6) (R 6) [10,33,144,257,96] 13 := by
  apply FastRouting.sound _ _ [10,33,144,257,96] 13 (by decide) (choices 1) [2,4,64] r30834 c30834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12653
  · exact u12654
  · exact u12655

def b30835 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 148 268 19 100 100 228 356), lower := (rows 11 35 148 268 19 32 64 128 256), losses := [] }

theorem u30835 : Upper (D 6) (R 6) [10,33,144,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30836 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 148 268 21 98 98 226 354), lower := (rows 11 35 148 268 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 490 482 156 268 508 32 64 128 256) }] }

theorem u30836 : Upper (D 6) (R 6) [10,33,144,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30837 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 148 268 22 97 97 225 353), lower := (rows 11 35 148 268 22 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 489 481 156 268 508 32 64 128 256) }] }

theorem u30837 : Upper (D 6) (R 6) [10,33,144,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30838 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 148 268 49 102 70 198 326), lower := (rows 11 35 148 268 49 32 64 128 256), losses := [] }

theorem u30838 : Upper (D 6) (R 6) [10,33,144,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30839 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 148 268 50 101 69 197 325), lower := (rows 11 35 148 268 50 32 64 128 256), losses := [] }

theorem u30839 : Upper (D 6) (R 6) [10,33,144,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30839
end Delivery.IrregularNine14.P06
