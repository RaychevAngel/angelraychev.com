import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0543
import IrregularNine14P06C0544
import IrregularNine14P06C0545
import IrregularNine14P06C0546
import IrregularNine14P06C0547

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41760 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 388 14 117 117 117 245 373), lower := (rows 11 98 388 14 16 32 64 128 256), losses := [] }

theorem u41760 : Upper (D 6) (R 6) [10,96,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41761 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41761 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41761 : Upper (D 6) (R 6) [10,96,384,17] 13 := by
  apply FastRouting.sound _ _ [10,96,384,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41761 c41761
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32584
  · exact u32585
  · exact u32586
  · exact u32587
  · exact u32588
  · exact u32589
  · exact u32590

def b41762 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 388 26 117 101 101 229 357), lower := (rows 11 98 388 26 16 32 64 128 256), losses := [] }

theorem u41762 : Upper (D 6) (R 6) [10,96,384,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41763 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41763 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41763 : Upper (D 6) (R 6) [10,96,384,20] 13 := by
  apply FastRouting.sound _ _ [10,96,384,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41763 c41763
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32591
  · exact u32592
  · exact u32593
  · exact u32594
  · exact u32595
  · exact u32596
  · exact u32597

def b41764 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 388 41 87 119 87 215 343), lower := (rows 11 98 388 41 16 32 64 128 256), losses := [] }

theorem u41764 : Upper (D 6) (R 6) [10,96,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41765 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 388 42 85 117 85 213 341), lower := (rows 11 98 388 42 16 32 64 128 256), losses := [] }

theorem u41765 : Upper (D 6) (R 6) [10,96,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41766 : Route 9 := (fun mask => (mask,id))

def c41766 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41766 : Upper (D 6) (R 6) [10,96,384,36] 13 := by
  apply FastRouting.sound _ _ [10,96,384,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41766 c41766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32598
  · exact u32599
  · exact u32600
  · exact u32601
  · exact u32602
  · exact u32603

def r41767 : Route 9 := (fun mask => (mask,id))

def c41767 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41767 : Upper (D 6) (R 6) [10,96,384,48] 13 := by
  apply FastRouting.sound _ _ [10,96,384,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41767 c41767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32604
  · exact u32605
  · exact u32606
  · exact u32607
  · exact u32608
  · exact u32609

def b41768 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 388 104 23 55 87 151 279), lower := (rows 11 98 388 104 16 32 64 128 256), losses := [] }

theorem u41768 : Upper (D 6) (R 6) [10,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41769 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 22 13 372 356 356 484 356), lower := (rows 11 131 22 13 16 32 64 128 256), losses := [] }

theorem u41769 : Upper (D 6) (R 6) [10,129,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41770 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 368, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 22 41 372 356 356 484 356), lower := (rows 11 131 22 41 16 32 64 128 256), losses := [] }

theorem u41770 : Upper (D 6) (R 6) [10,129,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41771 : Route 9 := (fun mask => (mask,id))

def c41771 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41771 : Upper (D 6) (R 6) [10,129,18,36] 13 := by
  apply FastRouting.sound _ _ [10,129,18,36] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41771 c41771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32610
  · exact u32611
  · exact u32612
  · exact u32613
  · exact u32614
  · exact u32615
  · exact u32616
  · exact u32617
  · exact u32618
  · exact u32619

def r41772 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41772 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41772 : Upper (D 6) (R 6) [10,129,18,96] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r41772 c41772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32620
  · exact u32621
  · exact u32622
  · exact u32623
  · exact u32624
  · exact u32625
  · exact u32626

def b41773 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 2, region := 112, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 22 265 116 100 100 228 356), lower := (rows 11 131 22 265 16 32 64 128 256), losses := [] }

theorem u41773 : Upper (D 6) (R 6) [10,129,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41774 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41774 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41774 : Upper (D 6) (R 6) [10,129,18,260] 13 := by
  apply FastRouting.sound _ _ [10,129,18,260] 13 (by decide) (choices 2) [5,33,36,96] r41774 c41774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32627
  · exact u32628
  · exact u32629
  · exact u32630

def r41775 : Route 9 := (fun mask => (mask,id))

def c41775 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41775 : Upper (D 6) (R 6) [10,129,18,288] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41775 c41775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32631
  · exact u32632
  · exact u32633
  · exact u32634
  · exact u32635
  · exact u32636

def b41776 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 37 14 372 372 372 500 372), lower := (rows 11 131 37 14 16 32 64 128 256), losses := [] }

theorem u41776 : Upper (D 6) (R 6) [10,129,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41777 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 37 26 372 356 356 484 356), lower := (rows 11 131 37 26 16 32 64 128 256), losses := [] }

theorem u41777 : Upper (D 6) (R 6) [10,129,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41778 : Route 9 := (fun mask => (mask,id))

def c41778 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41778 : Upper (D 6) (R 6) [10,129,33,20] 13 := by
  apply FastRouting.sound _ _ [10,129,33,20] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41778 c41778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32637
  · exact u32638
  · exact u32639
  · exact u32640
  · exact u32641
  · exact u32642
  · exact u32643
  · exact u32644
  · exact u32645
  · exact u32646

def b41779 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 131 37 42 340 372 340 468 340), lower := (rows 11 131 37 42 16 32 64 128 256), losses := [] }

theorem u41779 : Upper (D 6) (R 6) [10,129,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41780 : PairBound 9 := { available := 342, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 37 44 342 374 342 470 342), lower := (rows 11 131 37 44 16 32 64 128 256), losses := [] }

theorem u41780 : Upper (D 6) (R 6) [10,129,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41781 : Route 9 := (fun mask => (mask,id))

def c41781 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41781 : Upper (D 6) (R 6) [10,129,33,48] 13 := by
  apply FastRouting.sound _ _ [10,129,33,48] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41781 c41781
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32647
  · exact u32648
  · exact u32649
  · exact u32650
  · exact u32651
  · exact u32652

def b41782 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 37 74 372 372 372 500 372), lower := (rows 11 131 37 74 16 32 64 128 256), losses := [] }

theorem u41782 : Upper (D 6) (R 6) [10,129,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41783 : Route 9 := (fun mask => (mask,id))

def c41783 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41783 : Upper (D 6) (R 6) [10,129,33,68] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41783 c41783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32653
  · exact u32654
  · exact u32655
  · exact u32656
  · exact u32657
  · exact u32658
  · exact u32659
  · exact u32660
  · exact u32661
  · exact u32662

def r41784 : Route 9 := (fun mask => (mask,id))

def c41784 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41784 : Upper (D 6) (R 6) [10,129,33,80] 13 := by
  apply FastRouting.sound _ _ [10,129,33,80] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41784 c41784
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32663
  · exact u32664
  · exact u32665
  · exact u32666
  · exact u32667
  · exact u32668
  · exact u32669
  · exact u32670
  · exact u32671
  · exact u32672

def r41785 : Route 9 := (fun mask => (mask,id))

def c41785 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41785 : Upper (D 6) (R 6) [10,129,33,96] 13 := by
  apply FastRouting.sound _ _ [10,129,33,96] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41785 c41785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32673
  · exact u32674
  · exact u32675
  · exact u32676
  · exact u32677
  · exact u32678

def b41786 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 37 266 116 116 116 244 372), lower := (rows 11 131 37 266 16 32 64 128 256), losses := [] }

theorem u41786 : Upper (D 6) (R 6) [10,129,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41787 : Route 9 := (fun mask => (mask,id))

def c41787 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41787 : Upper (D 6) (R 6) [10,129,33,260] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41787 c41787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32679
  · exact u32680
  · exact u32681
  · exact u32682
  · exact u32683
  · exact u32684

def r41788 : Route 9 := (fun mask => (mask,id))

def c41788 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41788 : Upper (D 6) (R 6) [10,129,33,272] 13 := by
  apply FastRouting.sound _ _ [10,129,33,272] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41788 c41788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32685
  · exact u32686
  · exact u32687
  · exact u32688
  · exact u32689
  · exact u32690

def r41789 : Route 9 := (fun mask => (mask,id))

def c41789 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41789 : Upper (D 6) (R 6) [10,129,33,288] 13 := by
  apply FastRouting.sound _ _ [10,129,33,288] 13 (by decide) (choices 2) [6,66,68] r41789 c41789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32691
  · exact u32692
  · exact u32693

def r41790 : Route 9 := (fun mask => (mask,id))

def c41790 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41790 : Upper (D 6) (R 6) [10,129,33,320] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41790 c41790
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32694
  · exact u32695
  · exact u32696
  · exact u32697
  · exact u32698
  · exact u32699

def b41791 : PairBound 9 := { available := 372, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 38 13 372 372 372 500 372), lower := (rows 11 131 38 13 16 32 64 128 256), losses := [] }

theorem u41791 : Upper (D 6) (R 6) [10,129,34,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41792 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 336, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 38 25 372 356 356 484 356), lower := (rows 11 131 38 25 16 32 64 128 256), losses := [] }

theorem u41792 : Upper (D 6) (R 6) [10,129,34,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41793 : Route 9 := (fun mask => (mask,id))

def c41793 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41793 : Upper (D 6) (R 6) [10,129,34,20] 13 := by
  apply FastRouting.sound _ _ [10,129,34,20] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41793 c41793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32700
  · exact u32701
  · exact u32702
  · exact u32703
  · exact u32704
  · exact u32705
  · exact u32706
  · exact u32707
  · exact u32708
  · exact u32709

def b41794 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 9, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 131 38 41 340 372 340 468 340), lower := (rows 11 131 38 41 16 32 64 128 256), losses := [] }

theorem u41794 : Upper (D 6) (R 6) [10,129,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41795 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 131 38 44 341 373 341 469 341), lower := (rows 11 131 38 44 16 32 64 128 256), losses := [] }

theorem u41795 : Upper (D 6) (R 6) [10,129,34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41796 : Route 9 := (fun mask => (mask,id))

def c41796 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41796 : Upper (D 6) (R 6) [10,129,34,48] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41796 c41796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32710
  · exact u32711
  · exact u32712
  · exact u32713
  · exact u32714
  · exact u32715

def b41797 : PairBound 9 := { available := 372, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 336, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 38 73 372 372 372 500 372), lower := (rows 11 131 38 73 16 32 64 128 256), losses := [] }

theorem u41797 : Upper (D 6) (R 6) [10,129,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41798 : Route 9 := (fun mask => (mask,id))

def c41798 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41798 : Upper (D 6) (R 6) [10,129,34,68] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41798 c41798
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32716
  · exact u32717
  · exact u32718
  · exact u32719
  · exact u32720
  · exact u32721
  · exact u32722
  · exact u32723
  · exact u32724
  · exact u32725

def r41799 : Route 9 := (fun mask => (mask,id))

def c41799 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41799 : Upper (D 6) (R 6) [10,129,34,80] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41799 c41799
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32726
  · exact u32727
  · exact u32728
  · exact u32729
  · exact u32730
  · exact u32731
  · exact u32732
  · exact u32733
  · exact u32734
  · exact u32735

def r41800 : Route 9 := (fun mask => (mask,id))

def c41800 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41800 : Upper (D 6) (R 6) [10,129,34,96] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41800 c41800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32736
  · exact u32737
  · exact u32738
  · exact u32739
  · exact u32740
  · exact u32741

def b41801 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 2, region := 80, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 38 265 116 116 116 244 372), lower := (rows 11 131 38 265 16 32 64 128 256), losses := [] }

theorem u41801 : Upper (D 6) (R 6) [10,129,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41802 : Route 9 := (fun mask => (mask,id))

def c41802 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41802 : Upper (D 6) (R 6) [10,129,34,260] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41802 c41802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32742
  · exact u32743
  · exact u32744
  · exact u32745
  · exact u32746
  · exact u32747

def r41803 : Route 9 := (fun mask => (mask,id))

def c41803 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41803 : Upper (D 6) (R 6) [10,129,34,272] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41803 c41803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32748
  · exact u32749
  · exact u32750
  · exact u32751
  · exact u32752
  · exact u32753

def r41804 : Route 9 := (fun mask => (mask,id))

def c41804 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41804 : Upper (D 6) (R 6) [10,129,34,288] 13 := by
  apply FastRouting.sound _ _ [10,129,34,288] 13 (by decide) (choices 2) [5,65,68] r41804 c41804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32754
  · exact u32755
  · exact u32756

def r41805 : Route 9 := (fun mask => (mask,id))

def c41805 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41805 : Upper (D 6) (R 6) [10,129,34,320] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41805 c41805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32757
  · exact u32758
  · exact u32759
  · exact u32760
  · exact u32761
  · exact u32762

def b41806 : PairBound 9 := { available := 356, camps := [{ cop := 7, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 52 11 372 356 356 484 356), lower := (rows 11 131 52 11 16 32 64 128 256), losses := [] }

theorem u41806 : Upper (D 6) (R 6) [10,129,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41807 : Route 9 := (fun mask => (mask,id))

def c41807 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41807 : Upper (D 6) (R 6) [10,129,48,5] 13 := by
  apply FastRouting.sound _ _ [10,129,48,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41807 c41807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32763
  · exact u32764
  · exact u32765
  · exact u32766
  · exact u32767
  · exact u32768
  · exact u32769
  · exact u32770
  · exact u32771
  · exact u32772

def b41808 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 52 14 373 357 357 485 357), lower := (rows 11 131 52 14 16 32 64 128 256), losses := [] }

theorem u41808 : Upper (D 6) (R 6) [10,129,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41809 : Route 9 := (fun mask => (mask,id))

def c41809 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41809 : Upper (D 6) (R 6) [10,129,48,33] 13 := by
  apply FastRouting.sound _ _ [10,129,48,33] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41809 c41809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32773
  · exact u32774
  · exact u32775
  · exact u32776
  · exact u32777
  · exact u32778

def b41810 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 52 42 341 357 325 453 325), lower := (rows 11 131 52 42 16 32 64 128 256), losses := [] }

theorem u41810 : Upper (D 6) (R 6) [10,129,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41811 : PairBound 9 := { available := 327, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 52 44 343 359 327 455 327), lower := (rows 11 131 52 44 16 32 64 128 256), losses := [] }

theorem u41811 : Upper (D 6) (R 6) [10,129,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41812 : Route 9 := (fun mask => (mask,id))

def c41812 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41812 : Upper (D 6) (R 6) [10,129,48,65] 13 := by
  apply FastRouting.sound _ _ [10,129,48,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41812 c41812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32779
  · exact u32780
  · exact u32781
  · exact u32782
  · exact u32783
  · exact u32784
  · exact u32785
  · exact u32786
  · exact u32787
  · exact u32788

def b41813 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 52 74 373 357 357 485 357), lower := (rows 11 131 52 74 16 32 64 128 256), losses := [] }

theorem u41813 : Upper (D 6) (R 6) [10,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41814 : Route 9 := (fun mask => (mask,id))

def c41814 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41814 : Upper (D 6) (R 6) [10,129,48,68] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41814 c41814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32789
  · exact u32790
  · exact u32791
  · exact u32792
  · exact u32793
  · exact u32794
  · exact u32795
  · exact u32796
  · exact u32797
  · exact u32798
  · exact u32799
  · exact u32800
  · exact u32801
  · exact u32802
  · exact u32803

def r41815 : Route 9 := (fun mask => (mask,id))

def c41815 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41815 : Upper (D 6) (R 6) [10,129,48,96] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41815 c41815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32804
  · exact u32805
  · exact u32806
  · exact u32807
  · exact u32808
  · exact u32809
  · exact u32810
  · exact u32811
  · exact u32812
  · exact u32813

def r41816 : Route 9 := (fun mask => (mask,id))

def c41816 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41816 : Upper (D 6) (R 6) [10,129,48,257] 13 := by
  apply FastRouting.sound _ _ [10,129,48,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41816 c41816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32814
  · exact u32815
  · exact u32816
  · exact u32817
  · exact u32818
  · exact u32819

def b41817 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 52 266 117 101 101 229 357), lower := (rows 11 131 52 266 16 32 64 128 256), losses := [] }

theorem u41817 : Upper (D 6) (R 6) [10,129,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41818 : Route 9 := (fun mask => (mask,id))

def c41818 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41818 : Upper (D 6) (R 6) [10,129,48,260] 13 := by
  apply FastRouting.sound _ _ [10,129,48,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41818 c41818
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32820
  · exact u32821
  · exact u32822
  · exact u32823
  · exact u32824
  · exact u32825
  · exact u32826
  · exact u32827
  · exact u32828
  · exact u32829

def r41819 : Route 9 := (fun mask => (mask,id))

def c41819 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41819 : Upper (D 6) (R 6) [10,129,48,288] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41819 c41819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32830
  · exact u32831
  · exact u32832
  · exact u32833
  · exact u32834
  · exact u32835

#print axioms u41819
end Delivery.IrregularNine14.P06
