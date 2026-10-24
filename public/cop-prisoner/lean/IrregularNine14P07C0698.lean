import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0558
import IrregularNine14P07C0559
import IrregularNine14P07C0560
import IrregularNine14P07C0561

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41880 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 290 7 26 241 225 225 225 481), lower := (rows 13 290 7 26 16 32 64 128 256), losses := [] }

theorem u41880 : Upper (D 7) (R 7) [12,288,3,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41881 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 7 41 210 242 210 210 466), lower := (rows 13 290 7 41 16 32 64 128 256), losses := [] }

theorem u41881 : Upper (D 7) (R 7) [12,288,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41882 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 7 42 209 241 209 209 465), lower := (rows 13 290 7 42 16 32 64 128 256), losses := [] }

theorem u41882 : Upper (D 7) (R 7) [12,288,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41883 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41883 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41883 : Upper (D 7) (R 7) [12,288,3,48] 13 := by
  apply FastRouting.sound _ _ [12,288,3,48] 13 (by decide) (choices 2) [3,65,66,192] r41883 c41883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33505
  · exact u33506
  · exact u33507
  · exact u33508

def r41884 : Route 9 := (fun mask => (mask,id))

def c41884 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41884 : Upper (D 7) (R 7) [12,288,3,65] 13 := by
  apply FastRouting.sound _ _ [12,288,3,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41884 c41884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33509
  · exact u33510
  · exact u33511
  · exact u33512
  · exact u33513
  · exact u33514

def b41885 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 290 7 74 241 241 241 241 497), lower := (rows 13 290 7 74 16 32 64 128 256), losses := [] }

theorem u41885 : Upper (D 7) (R 7) [12,288,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41886 : Route 9 := (fun mask => (mask,id))

def c41886 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41886 : Upper (D 7) (R 7) [12,288,3,80] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41886 c41886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33515
  · exact u33516
  · exact u33517
  · exact u33518
  · exact u33519
  · exact u33520
  · exact u33521
  · exact u33522
  · exact u33523
  · exact u33524

def r41887 : Route 9 := (fun mask => (mask,id))

def c41887 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41887 : Upper (D 7) (R 7) [12,288,3,96] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41887 c41887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33525
  · exact u33526
  · exact u33527
  · exact u33528
  · exact u33529
  · exact u33530

def r41888 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41888 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41888 : Upper (D 7) (R 7) [12,288,3,192] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41888 c41888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33531
  · exact u33532
  · exact u33533
  · exact u33534
  · exact u33535
  · exact u33536
  · exact u33537

def r41889 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41889 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41889 : Upper (D 7) (R 7) [12,288,17,33] 13 := by
  apply FastRouting.sound _ _ [12,288,17,33] 13 (by decide) (choices 2) [66,192] r41889 c41889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u33538
  · exact u33539

def b41890 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 13 290 21 42 211 227 195 195 451), lower := (rows 13 290 21 42 16 32 64 128 256), losses := [] }

theorem u41890 : Upper (D 7) (R 7) [12,288,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41891 : Route 9 := (fun mask => (mask,id))

def c41891 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41891 : Upper (D 7) (R 7) [12,288,17,65] 13 := by
  apply FastRouting.sound _ _ [12,288,17,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41891 c41891
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33540
  · exact u33541
  · exact u33542
  · exact u33543
  · exact u33544
  · exact u33545

def r41892 : Route 9 := (fun mask => (mask,id))

def c41892 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41892 : Upper (D 7) (R 7) [12,288,17,66] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41892 c41892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33546
  · exact u33547
  · exact u33548
  · exact u33549
  · exact u33550
  · exact u33551
  · exact u33552
  · exact u33553
  · exact u33554
  · exact u33555

def r41893 : Route 9 := (fun mask => (mask,id))

def c41893 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41893 : Upper (D 7) (R 7) [12,288,17,96] 13 := by
  apply FastRouting.sound _ _ [12,288,17,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41893 c41893
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33556
  · exact u33557
  · exact u33558
  · exact u33559
  · exact u33560
  · exact u33561

def r41894 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41894 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41894 : Upper (D 7) (R 7) [12,288,17,192] 13 := by
  apply FastRouting.sound _ _ [12,288,17,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41894 c41894
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33562
  · exact u33563
  · exact u33564
  · exact u33565
  · exact u33566
  · exact u33567
  · exact u33568

def r41895 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41895 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41895 : Upper (D 7) (R 7) [12,288,18,33] 13 := by
  apply FastRouting.sound _ _ [12,288,18,33] 13 (by decide) (choices 2) [3,65,66,192] r41895 c41895
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33569
  · exact u33570
  · exact u33571
  · exact u33572

def b41896 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 13 290 22 42 209 225 193 193 449), lower := (rows 13 290 22 42 16 32 64 128 256), losses := [] }

theorem u41896 : Upper (D 7) (R 7) [12,288,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41897 : Route 9 := (fun mask => (mask,id))

def c41897 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41897 : Upper (D 7) (R 7) [12,288,18,65] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41897 c41897
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33573
  · exact u33574
  · exact u33575
  · exact u33576
  · exact u33577
  · exact u33578
  · exact u33579
  · exact u33580
  · exact u33581
  · exact u33582

def r41898 : Route 9 := (fun mask => (mask,id))

def c41898 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41898 : Upper (D 7) (R 7) [12,288,18,66] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41898 c41898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33583
  · exact u33584
  · exact u33585
  · exact u33586
  · exact u33587
  · exact u33588

def r41899 : Route 9 := (fun mask => (mask,id))

def c41899 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41899 : Upper (D 7) (R 7) [12,288,18,96] 13 := by
  apply FastRouting.sound _ _ [12,288,18,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41899 c41899
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33589
  · exact u33590
  · exact u33591
  · exact u33592
  · exact u33593
  · exact u33594

def r41900 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41900 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41900 : Upper (D 7) (R 7) [12,288,18,192] 13 := by
  apply FastRouting.sound _ _ [12,288,18,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41900 c41900
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33595
  · exact u33596
  · exact u33597
  · exact u33598
  · exact u33599
  · exact u33600
  · exact u33601

def r41901 : Route 9 := (fun mask => (mask,id))

def c41901 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41901 : Upper (D 7) (R 7) [12,288,33,65] 13 := by
  apply FastRouting.sound _ _ [12,288,33,65] 13 (by decide) (choices 2) [66,130,192] r41901 c41901
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33602
  · exact u33603
  · exact u33604

def r41902 : Route 9 := (fun mask => (mask,id))

def c41902 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41902 : Upper (D 7) (R 7) [12,288,33,66] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41902 c41902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33605
  · exact u33606
  · exact u33607
  · exact u33608
  · exact u33609
  · exact u33610

def r41903 : Route 9 := (fun mask => (mask,id))

def c41903 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41903 : Upper (D 7) (R 7) [12,288,33,80] 13 := by
  apply FastRouting.sound _ _ [12,288,33,80] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41903 c41903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33611
  · exact u33612
  · exact u33613
  · exact u33614
  · exact u33615
  · exact u33616

def r41904 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41904 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41904 : Upper (D 7) (R 7) [12,288,33,192] 13 := by
  apply FastRouting.sound _ _ [12,288,33,192] 13 (by decide) (choices 2) [3,65,66,192] r41904 c41904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33617
  · exact u33618
  · exact u33619
  · exact u33620

def b41905 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 217, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 290 38 73 211 243 211 211 467), lower := (rows 13 290 38 73 16 32 64 128 256), losses := [] }

theorem u41905 : Upper (D 7) (R 7) [12,288,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41906 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 217, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 290 38 74 209 241 209 209 465), lower := (rows 13 290 38 74 16 32 64 128 256), losses := [] }

theorem u41906 : Upper (D 7) (R 7) [12,288,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41907 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 217, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 290 38 88 211 227 195 195 451), lower := (rows 13 290 38 88 16 32 64 128 256), losses := [] }

theorem u41907 : Upper (D 7) (R 7) [12,288,34,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41908 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 217, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 290 38 200 211 243 211 211 467), lower := (rows 13 290 38 200 16 32 64 128 256), losses := [] }

theorem u41908 : Upper (D 7) (R 7) [12,288,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41909 : Route 9 := (fun mask => (mask,id))

def c41909 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41909 : Upper (D 7) (R 7) [12,288,48,65] 13 := by
  apply FastRouting.sound _ _ [12,288,48,65] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41909 c41909
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33621
  · exact u33622
  · exact u33623
  · exact u33624
  · exact u33625
  · exact u33626

def r41910 : Route 9 := (fun mask => (mask,id))

def c41910 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41910 : Upper (D 7) (R 7) [12,288,48,66] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41910 c41910
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33627
  · exact u33628
  · exact u33629
  · exact u33630
  · exact u33631
  · exact u33632

def r41911 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41911 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41911 : Upper (D 7) (R 7) [12,288,48,192] 13 := by
  apply FastRouting.sound _ _ [12,288,48,192] 13 (by decide) (choices 2) [3,65,66,192] r41911 c41911
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33633
  · exact u33634
  · exact u33635
  · exact u33636

def b41912 : PairBound 9 := { available := 178, camps := [{ cop := 6, region := 13, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 69 73 178 178 242 178 434), lower := (rows 13 290 69 73 16 32 64 128 256), losses := [] }

theorem u41912 : Upper (D 7) (R 7) [12,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41913 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 69 74 179 179 243 179 435), lower := (rows 13 290 69 74 16 32 64 128 256), losses := [] }

theorem u41913 : Upper (D 7) (R 7) [12,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41914 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 69 88 179 163 227 163 419), lower := (rows 13 290 69 88 16 32 64 128 256), losses := [] }

theorem u41914 : Upper (D 7) (R 7) [12,288,65,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41915 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 69 104 147 179 211 147 403), lower := (rows 13 290 69 104 16 32 64 128 256), losses := [] }

theorem u41915 : Upper (D 7) (R 7) [12,288,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41916_130 : Upper (D 7) (R 7) [12,288,65,129,130] 13 :=
  permutation_upper _ _ _ [12,288,65,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33638

theorem m41916_160 : Upper (D 7) (R 7) [12,288,65,129,160] 13 :=
  permutation_upper _ _ _ [12,288,65,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33639

def r41916 : Route 9 := (fun mask => (mask,id))

def c41916 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41916 : Upper (D 7) (R 7) [12,288,65,129] 13 := by
  apply FastRouting.sound _ _ [12,288,65,129] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41916 c41916
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33637
  · exact u33638
  · exact u33639
  · exact m41916_130
  · exact m41916_160
  · exact u33640

def r41917 : Route 9 := (fun mask => (mask,id))

def c41917 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41917 : Upper (D 7) (R 7) [12,288,65,130] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41917 c41917
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33641
  · exact u33642
  · exact u33643
  · exact u33644
  · exact u33645
  · exact u33646
  · exact u33647
  · exact u33648
  · exact u33649
  · exact u33650

def r41918 : Route 9 := (fun mask => (mask,id))

def c41918 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41918 : Upper (D 7) (R 7) [12,288,65,144] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41918 c41918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33651
  · exact u33652
  · exact u33653
  · exact u33654
  · exact u33655
  · exact u33656
  · exact u33657
  · exact u33658
  · exact u33659
  · exact u33660

def r41919 : Route 9 := (fun mask => (mask,id))

def c41919 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41919 : Upper (D 7) (R 7) [12,288,65,160] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41919 c41919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33661
  · exact u33662
  · exact u33663
  · exact u33664
  · exact u33665
  · exact u33666

def b41920 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 69 200 179 179 243 179 435), lower := (rows 13 290 69 200 16 32 64 128 256), losses := [] }

theorem u41920 : Upper (D 7) (R 7) [12,288,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41921 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 9, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 70 74 177 177 241 177 433), lower := (rows 13 290 70 74 16 32 64 128 256), losses := [] }

theorem u41921 : Upper (D 7) (R 7) [12,288,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41922 : Route 9 := (fun mask => (mask,id))

def c41922 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41922 : Upper (D 7) (R 7) [12,288,66,80] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41922 c41922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33667
  · exact u33668
  · exact u33669
  · exact u33670
  · exact u33671
  · exact u33672

def r41923 : Route 9 := (fun mask => (mask,id))

def c41923 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41923 : Upper (D 7) (R 7) [12,288,66,96] 13 := by
  apply FastRouting.sound _ _ [12,288,66,96] 13 (by decide) (choices 2) [3,129,130] r41923 c41923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33673
  · exact u33674
  · exact u33675

theorem m41924_129 : Upper (D 7) (R 7) [12,288,66,130,129] 13 :=
  permutation_upper _ _ _ [12,288,66,130,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33677

theorem m41924_160 : Upper (D 7) (R 7) [12,288,66,130,160] 13 :=
  permutation_upper _ _ _ [12,288,66,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33678

def r41924 : Route 9 := (fun mask => (mask,id))

def c41924 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41924 : Upper (D 7) (R 7) [12,288,66,130] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41924 c41924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33676
  · exact u33677
  · exact u33678
  · exact m41924_129
  · exact m41924_160
  · exact u33679

def r41925 : Route 9 := (fun mask => (mask,id))

def c41925 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41925 : Upper (D 7) (R 7) [12,288,66,144] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41925 c41925
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33680
  · exact u33681
  · exact u33682
  · exact u33683
  · exact u33684
  · exact u33685
  · exact u33686
  · exact u33687
  · exact u33688
  · exact u33689

def r41926 : Route 9 := (fun mask => (mask,id))

def c41926 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41926 : Upper (D 7) (R 7) [12,288,66,160] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41926 c41926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33690
  · exact u33691
  · exact u33692
  · exact u33693
  · exact u33694
  · exact u33695

def r41927 : Route 9 := (fun mask => (mask,id))

def c41927 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41927 : Upper (D 7) (R 7) [12,288,66,192] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41927 c41927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33696
  · exact u33697
  · exact u33698
  · exact u33699
  · exact u33700
  · exact u33701

def r41928 : Route 9 := (fun mask => (mask,id))

def c41928 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41928 : Upper (D 7) (R 7) [12,288,80,96] 13 := by
  apply FastRouting.sound _ _ [12,288,80,96] 13 (by decide) (choices 2) [3,129,130] r41928 c41928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33702
  · exact u33703
  · exact u33704

def r41929 : Route 9 := (fun mask => (mask,id))

def c41929 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41929 : Upper (D 7) (R 7) [12,288,80,160] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41929 c41929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33705
  · exact u33706
  · exact u33707
  · exact u33708
  · exact u33709
  · exact u33710

def r41930 : Route 9 := (fun mask => (mask,id))

def c41930 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41930 : Upper (D 7) (R 7) [12,288,80,192] 13 := by
  apply FastRouting.sound _ _ [12,288,80,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41930 c41930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33711
  · exact u33712
  · exact u33713
  · exact u33714
  · exact u33715
  · exact u33716

def r41931 : Route 9 := (fun mask => (mask,id))

def c41931 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41931 : Upper (D 7) (R 7) [12,288,96,192] 13 := by
  apply FastRouting.sound _ _ [12,288,96,192] 13 (by decide) (choices 2) [3,129,130] r41931 c41931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33717
  · exact u33718
  · exact u33719

def b41932 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 196 200 51 51 115 179 307), lower := (rows 13 290 196 200 16 32 64 128 256), losses := [] }

theorem u41932 : Upper (D 7) (R 7) [12,288,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41933 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 28 504 488 488 488 488), lower := (rows 35 67 7 28 16 32 64 128 256), losses := [] }

theorem u41933 : Upper (D 7) (R 7) [34,65,3,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41934 : PairBound 9 := { available := 472, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 7 44 472 504 472 472 472), lower := (rows 35 67 7 44 16 32 64 128 256), losses := [] }

theorem u41934 : Upper (D 7) (R 7) [34,65,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41935 : PairBound 9 := { available := 412, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 104 412 444 476 412 412), lower := (rows 35 67 7 104 16 32 64 128 256), losses := [] }

theorem u41935 : Upper (D 7) (R 7) [34,65,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41936 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 140 504 504 504 504 504), lower := (rows 35 67 7 140 16 32 64 128 256), losses := [] }

theorem u41936 : Upper (D 7) (R 7) [34,65,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41937 : PairBound 9 := { available := 476, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 168 476 508 476 476 476), lower := (rows 35 67 7 168 16 32 64 128 256), losses := [] }

theorem u41937 : Upper (D 7) (R 7) [34,65,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41938 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 268 248 248 248 248 504), lower := (rows 35 67 7 268 16 32 64 128 256), losses := [] }

theorem u41938 : Upper (D 7) (R 7) [34,65,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41939 : PairBound 9 := { available := 220, camps := [{ cop := 2, region := 504, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 67 7 296 220 252 220 220 476), lower := (rows 35 67 7 296 16 32 64 128 256), losses := [] }

theorem u41939 : Upper (D 7) (R 7) [34,65,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u41939
end Delivery.IrregularNine14.P07
