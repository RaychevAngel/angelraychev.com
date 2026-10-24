import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0463
import IrregularNine14P06C0464
import IrregularNine14P06C0465
import IrregularNine14P06C0466

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40620 : PairBound 9 := { available := 470, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 41 470 502 470 470 470), lower := (rows 7 11 100 41 16 32 64 128 256), losses := [] }

theorem u40620 : Upper (D 6) (R 6) [6,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40621 : PairBound 9 := { available := 469, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 42 469 501 469 469 469), lower := (rows 7 11 100 42 16 32 64 128 256), losses := [] }

theorem u40621 : Upper (D 6) (R 6) [6,9,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40622 : PairBound 9 := { available := 467, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 44 467 499 467 467 467), lower := (rows 7 11 100 44 16 32 64 128 256), losses := [] }

theorem u40622 : Upper (D 6) (R 6) [6,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40623 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40623 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u40623 : Upper (D 6) (R 6) [6,9,96,48] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r40623 c40623
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27794
  · exact u27795
  · exact u27796
  · exact u27797
  · exact u27798
  · exact u27799
  · exact u27800
  · exact u27801
  · exact u27802
  · exact u27803
  · exact u27804

def b40624 : PairBound 9 := { available := 407, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 11 100 104 407 439 471 407 407), lower := (rows 7 11 100 104 16 32 64 128 256), losses := [] }

theorem u40624 : Upper (D 6) (R 6) [6,9,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40625 : PairBound 9 := { available := 374, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 100 137 374 374 374 502 374), lower := (rows 7 11 100 137 16 32 64 128 256), losses := [] }

theorem u40625 : Upper (D 6) (R 6) [6,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40626 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40626 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40626 : Upper (D 6) (R 6) [6,9,96,130] 13 := by
  apply FastRouting.sound _ _ [6,9,96,130] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r40626 c40626
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27805
  · exact u27806
  · exact u27807
  · exact u27808
  · exact u27809
  · exact u27810
  · exact u27811

def b40627 : PairBound 9 := { available := 371, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 100 140 371 371 371 499 371), lower := (rows 7 11 100 140 16 32 64 128 256), losses := [] }

theorem u40627 : Upper (D 6) (R 6) [6,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40628 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40628 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40628 : Upper (D 6) (R 6) [6,9,96,144] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r40628 c40628
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27812
  · exact u27813
  · exact u27814
  · exact u27815
  · exact u27816
  · exact u27817
  · exact u27818
  · exact u27819
  · exact u27820
  · exact u27821
  · exact u27822

def r40629 : Route 9 := (fun mask => (mask,id))

def c40629 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40629 : Upper (D 6) (R 6) [6,9,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40629 c40629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27823
  · exact u27824
  · exact u27825
  · exact u27826
  · exact u27827
  · exact u27828
  · exact u27829
  · exact u27830
  · exact u27831
  · exact u27832

def r40630 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40630 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40630 : Upper (D 6) (R 6) [6,9,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r40630 c40630
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27833
  · exact u27834
  · exact u27835
  · exact u27836
  · exact u27837
  · exact u27838
  · exact u27839

def b40631 : PairBound 9 := { available := 368, camps := [{ cop := 7, region := 15, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 133 14 368 368 368 496 368), lower := (rows 7 11 133 14 16 32 64 128 256), losses := [] }

theorem u40631 : Upper (D 6) (R 6) [6,9,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40632 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 26 372 356 356 484 356), lower := (rows 7 11 133 26 16 32 64 128 256), losses := [] }

theorem u40632 : Upper (D 6) (R 6) [6,9,129,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40633 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 133 28 370 354 354 482 354), lower := (rows 7 11 133 28 16 32 64 128 256), losses := [] }

theorem u40633 : Upper (D 6) (R 6) [6,9,129,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40634 : PairBound 9 := { available := 372, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 42 372 372 372 500 372), lower := (rows 7 11 133 42 16 32 64 128 256), losses := [] }

theorem u40634 : Upper (D 6) (R 6) [6,9,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40635 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 133 44 370 370 370 498 370), lower := (rows 7 11 133 44 16 32 64 128 256), losses := [] }

theorem u40635 : Upper (D 6) (R 6) [6,9,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40636 : Route 9 := (fun mask => (mask,id))

def c40636 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40636 : Upper (D 6) (R 6) [6,9,129,48] 13 := by
  apply FastRouting.sound _ _ [6,9,129,48] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40636 c40636
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27840
  · exact u27841
  · exact u27842
  · exact u27843
  · exact u27844
  · exact u27845
  · exact u27846
  · exact u27847
  · exact u27848
  · exact u27849

def r40637 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40637 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40637 : Upper (D 6) (R 6) [6,9,129,96] 13 := by
  apply FastRouting.sound _ _ [6,9,129,96] 13 (by decide) (choices 2) [6,34,36,96,258,260,288] r40637 c40637
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27850
  · exact u27851
  · exact u27852
  · exact u27853
  · exact u27854
  · exact u27855
  · exact u27856

def b40638 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 266 116 116 116 244 372), lower := (rows 7 11 133 266 16 32 64 128 256), losses := [] }

theorem u40638 : Upper (D 6) (R 6) [6,9,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40639 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 133 268 114 114 114 242 370), lower := (rows 7 11 133 268 16 32 64 128 256), losses := [] }

theorem u40639 : Upper (D 6) (R 6) [6,9,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40640 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40640 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40640 : Upper (D 6) (R 6) [6,9,129,272] 13 := by
  apply FastRouting.sound _ _ [6,9,129,272] 13 (by decide) (choices 2) [6,34,36,96] r40640 c40640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27857
  · exact u27858
  · exact u27859
  · exact u27860

def r40641 : Route 9 := (fun mask => (mask,id))

def c40641 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40641 : Upper (D 6) (R 6) [6,9,129,288] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288] 13 (by decide) (choices 2) [6,34,36,66,68,96] r40641 c40641
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27861
  · exact u27862
  · exact u27863
  · exact u27864
  · exact u27865
  · exact u27866

def b40642 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 148 11 372 356 356 484 356), lower := (rows 7 11 148 11 16 32 64 128 256), losses := [] }

theorem u40642 : Upper (D 6) (R 6) [6,9,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40643 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 148 13 370 354 354 482 354), lower := (rows 7 11 148 13 16 32 64 128 256), losses := [] }

theorem u40643 : Upper (D 6) (R 6) [6,9,144,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40644 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 148 14 369 353 353 481 353), lower := (rows 7 11 148 14 16 32 64 128 256), losses := [] }

theorem u40644 : Upper (D 6) (R 6) [6,9,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40645 : PairBound 9 := { available := 358, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 148 41 374 358 358 486 358), lower := (rows 7 11 148 41 16 32 64 128 256), losses := [] }

theorem u40645 : Upper (D 6) (R 6) [6,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40646 : Route 9 := (fun mask => (mask,id))

def c40646 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40646 : Upper (D 6) (R 6) [6,9,144,34] 13 := by
  apply FastRouting.sound _ _ [6,9,144,34] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40646 c40646
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27867
  · exact u27868
  · exact u27869
  · exact u27870
  · exact u27871
  · exact u27872
  · exact u27873
  · exact u27874
  · exact u27875
  · exact u27876

def b40647 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 148 44 371 355 355 483 355), lower := (rows 7 11 148 44 16 32 64 128 256), losses := [] }

theorem u40647 : Upper (D 6) (R 6) [6,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40648 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40648 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40648 : Upper (D 6) (R 6) [6,9,144,96] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r40648 c40648
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27877
  · exact u27878
  · exact u27879
  · exact u27880
  · exact u27881
  · exact u27882
  · exact u27883
  · exact u27884
  · exact u27885
  · exact u27886
  · exact u27887

def b40649 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 148 265 118 102 102 230 358), lower := (rows 7 11 148 265 16 32 64 128 256), losses := [] }

theorem u40649 : Upper (D 6) (R 6) [6,9,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40650 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40650 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40650 : Upper (D 6) (R 6) [6,9,144,258] 13 := by
  apply FastRouting.sound _ _ [6,9,144,258] 13 (by decide) (choices 2) [5,33,36,96] r40650 c40650
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27888
  · exact u27889
  · exact u27890
  · exact u27891

def b40651 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 148 268 115 99 99 227 355), lower := (rows 7 11 148 268 16 32 64 128 256), losses := [] }

theorem u40651 : Upper (D 6) (R 6) [6,9,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40652 : Route 9 := (fun mask => (mask,id))

def c40652 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40652 : Upper (D 6) (R 6) [6,9,144,288] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40652 c40652
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27892
  · exact u27893
  · exact u27894
  · exact u27895
  · exact u27896
  · exact u27897
  · exact u27898
  · exact u27899
  · exact u27900
  · exact u27901

def b40653 : PairBound 9 := { available := 372, camps := [{ cop := 0, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 164 11 372 372 372 500 372), lower := (rows 7 11 164 11 16 32 64 128 256), losses := [] }

theorem u40653 : Upper (D 6) (R 6) [6,9,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40654 : PairBound 9 := { available := 370, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 13 370 370 370 498 370), lower := (rows 7 11 164 13 16 32 64 128 256), losses := [] }

theorem u40654 : Upper (D 6) (R 6) [6,9,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40655 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 14 369 369 369 497 369), lower := (rows 7 11 164 14 16 32 64 128 256), losses := [] }

theorem u40655 : Upper (D 6) (R 6) [6,9,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40656 : PairBound 9 := { available := 358, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 164 25 374 358 358 486 358), lower := (rows 7 11 164 25 16 32 64 128 256), losses := [] }

theorem u40656 : Upper (D 6) (R 6) [6,9,160,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40657 : Route 9 := (fun mask => (mask,id))

def c40657 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40657 : Upper (D 6) (R 6) [6,9,160,18] 13 := by
  apply FastRouting.sound _ _ [6,9,160,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40657 c40657
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27902
  · exact u27903
  · exact u27904
  · exact u27905
  · exact u27906
  · exact u27907
  · exact u27908
  · exact u27909
  · exact u27910
  · exact u27911

def b40658 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 28 371 355 355 483 355), lower := (rows 7 11 164 28 16 32 64 128 256), losses := [] }

theorem u40658 : Upper (D 6) (R 6) [6,9,160,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40659 : PairBound 9 := { available := 342, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 41 342 374 342 470 342), lower := (rows 7 11 164 41 16 32 64 128 256), losses := [] }

theorem u40659 : Upper (D 6) (R 6) [6,9,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40660 : PairBound 9 := { available := 341, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 42 341 373 341 469 341), lower := (rows 7 11 164 42 16 32 64 128 256), losses := [] }

theorem u40660 : Upper (D 6) (R 6) [6,9,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40661 : PairBound 9 := { available := 339, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 44 339 371 339 467 339), lower := (rows 7 11 164 44 16 32 64 128 256), losses := [] }

theorem u40661 : Upper (D 6) (R 6) [6,9,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40662 : Route 9 := (fun mask => (mask,id))

def c40662 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40662 : Upper (D 6) (R 6) [6,9,160,48] 13 := by
  apply FastRouting.sound _ _ [6,9,160,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40662 c40662
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27912
  · exact u27913
  · exact u27914
  · exact u27915
  · exact u27916
  · exact u27917
  · exact u27918
  · exact u27919
  · exact u27920
  · exact u27921

def b40663 : PairBound 9 := { available := 374, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 164 73 374 374 374 502 374), lower := (rows 7 11 164 73 16 32 64 128 256), losses := [] }

theorem u40663 : Upper (D 6) (R 6) [6,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40664 : Route 9 := (fun mask => (mask,id))

def c40664 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40664 : Upper (D 6) (R 6) [6,9,160,66] 13 := by
  apply FastRouting.sound _ _ [6,9,160,66] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40664 c40664
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27922
  · exact u27923
  · exact u27924
  · exact u27925
  · exact u27926
  · exact u27927
  · exact u27928
  · exact u27929
  · exact u27930
  · exact u27931

def b40665 : PairBound 9 := { available := 371, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 76 371 371 371 499 371), lower := (rows 7 11 164 76 16 32 64 128 256), losses := [] }

theorem u40665 : Upper (D 6) (R 6) [6,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40666 : Route 9 := (fun mask => (mask,id))

def c40666 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40666 : Upper (D 6) (R 6) [6,9,160,80] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r40666 c40666
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27932
  · exact u27933
  · exact u27934
  · exact u27935
  · exact u27936
  · exact u27937
  · exact u27938
  · exact u27939
  · exact u27940
  · exact u27941
  · exact u27942
  · exact u27943
  · exact u27944
  · exact u27945
  · exact u27946

def r40667 : Route 9 := (fun mask => (mask,id))

def c40667 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40667 : Upper (D 6) (R 6) [6,9,160,96] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40667 c40667
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27947
  · exact u27948
  · exact u27949
  · exact u27950
  · exact u27951
  · exact u27952
  · exact u27953
  · exact u27954
  · exact u27955
  · exact u27956

def b40668 : PairBound 9 := { available := 118, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 164 265 118 118 118 246 374), lower := (rows 7 11 164 265 16 32 64 128 256), losses := [] }

theorem u40668 : Upper (D 6) (R 6) [6,9,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40669 : Route 9 := (fun mask => (mask,id))

def c40669 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40669 : Upper (D 6) (R 6) [6,9,160,258] 13 := by
  apply FastRouting.sound _ _ [6,9,160,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r40669 c40669
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27957
  · exact u27958
  · exact u27959
  · exact u27960
  · exact u27961
  · exact u27962

def b40670 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 268 115 115 115 243 371), lower := (rows 7 11 164 268 16 32 64 128 256), losses := [] }

theorem u40670 : Upper (D 6) (R 6) [6,9,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40671 : Route 9 := (fun mask => (mask,id))

def c40671 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40671 : Upper (D 6) (R 6) [6,9,160,272] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40671 c40671
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27963
  · exact u27964
  · exact u27965
  · exact u27966
  · exact u27967
  · exact u27968
  · exact u27969
  · exact u27970
  · exact u27971
  · exact u27972

def r40672 : Route 9 := (fun mask => (mask,id))

def c40672 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40672 : Upper (D 6) (R 6) [6,9,160,288] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r40672 c40672
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27973
  · exact u27974
  · exact u27975
  · exact u27976
  · exact u27977
  · exact u27978

def r40673 : Route 9 := (fun mask => (mask,id))

def c40673 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40673 : Upper (D 6) (R 6) [6,9,160,320] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40673 c40673
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27979
  · exact u27980
  · exact u27981
  · exact u27982
  · exact u27983
  · exact u27984
  · exact u27985
  · exact u27986
  · exact u27987
  · exact u27988

def b40674 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 388 11 116 116 116 244 372), lower := (rows 7 11 388 11 16 32 64 128 256), losses := [] }

theorem u40674 : Upper (D 6) (R 6) [6,9,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40675 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 388 13 114 114 114 242 370), lower := (rows 7 11 388 13 16 32 64 128 256), losses := [] }

theorem u40675 : Upper (D 6) (R 6) [6,9,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40676 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 388 14 113 113 113 241 369), lower := (rows 7 11 388 14 16 32 64 128 256), losses := [] }

theorem u40676 : Upper (D 6) (R 6) [6,9,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40677 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 388 25 118 102 102 230 358), lower := (rows 7 11 388 25 16 32 64 128 256), losses := [] }

theorem u40677 : Upper (D 6) (R 6) [6,9,384,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40678 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40678 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40678 : Upper (D 6) (R 6) [6,9,384,18] 13 := by
  apply FastRouting.sound _ _ [6,9,384,18] 13 (by decide) (choices 2) [5,33,36,96] r40678 c40678
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27989
  · exact u27990
  · exact u27991
  · exact u27992

def b40679 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 388 28 115 99 99 227 355), lower := (rows 7 11 388 28 16 32 64 128 256), losses := [] }

theorem u40679 : Upper (D 6) (R 6) [6,9,384,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40679
end Delivery.IrregularNine14.P06
