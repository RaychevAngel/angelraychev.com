import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0595
import IrregularNine14P06C0596
import IrregularNine14P06C0597
import IrregularNine14P06C0598
import IrregularNine14P06C0599
import IrregularNine14P06C0600

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m42540_6 : Upper (D 6) (R 6) [34,65,136,260,6] 13 :=
  permutation_upper _ _ _ [34,65,136,260,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35756

theorem m42540_65 : Upper (D 6) (R 6) [34,65,136,260,65] 13 :=
  permutation_upper _ _ _ [34,65,136,260,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35758

theorem m42540_66 : Upper (D 6) (R 6) [34,65,136,260,66] 13 :=
  permutation_upper _ _ _ [34,65,136,260,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35757

theorem m42540_68 : Upper (D 6) (R 6) [34,65,136,260,68] 13 :=
  permutation_upper _ _ _ [34,65,136,260,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35759

def r42540 : Route 9 := (fun mask => (mask,id))

def c42540 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42540 : Upper (D 6) (R 6) [34,65,136,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42540 c42540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35755
  · exact u35756
  · exact m42540_6
  · exact u35757
  · exact u35758
  · exact u35759
  · exact m42540_65
  · exact m42540_66
  · exact m42540_68
  · exact u35760

theorem m42541_6 : Upper (D 6) (R 6) [34,65,136,272,6] 13 :=
  permutation_upper _ _ _ [34,65,136,272,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35762

theorem m42541_65 : Upper (D 6) (R 6) [34,65,136,272,65] 13 :=
  permutation_upper _ _ _ [34,65,136,272,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35764

theorem m42541_66 : Upper (D 6) (R 6) [34,65,136,272,66] 13 :=
  permutation_upper _ _ _ [34,65,136,272,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35763

theorem m42541_68 : Upper (D 6) (R 6) [34,65,136,272,68] 13 :=
  permutation_upper _ _ _ [34,65,136,272,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35765

def r42541 : Route 9 := (fun mask => (mask,id))

def c42541 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42541 : Upper (D 6) (R 6) [34,65,136,272] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42541 c42541
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35761
  · exact u35762
  · exact m42541_6
  · exact u35763
  · exact u35764
  · exact u35765
  · exact m42541_65
  · exact m42541_66
  · exact m42541_68
  · exact u35766

def r42542 : Route 9 := (fun mask => (mask,id))

def c42542 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42542 : Upper (D 6) (R 6) [34,65,136,288] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42542 c42542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35767
  · exact u35768
  · exact u35769
  · exact u35770
  · exact u35771
  · exact u35772

def b42543 : PairBound 9 := { available := 348, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 164 11 348 380 348 476 348), lower := (rows 35 67 164 11 16 32 64 128 256), losses := [] }

theorem u42543 : Upper (D 6) (R 6) [34,65,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42544 : Route 9 := (fun mask => (mask,id))

def c42544 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42544 : Upper (D 6) (R 6) [34,65,160,5] 13 := by
  apply FastRouting.sound _ _ [34,65,160,5] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r42544 c42544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35779
  · exact u35780
  · exact u35781
  · exact u35782
  · exact u35783
  · exact u35784
  · exact u35785
  · exact u35786
  · exact u35787
  · exact u35788

theorem m42545_5 : Upper (D 6) (R 6) [34,65,160,6,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35779

def r42545 : Route 9 := (fun mask => (mask,id))

def c42545 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42545 : Upper (D 6) (R 6) [34,65,160,6] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r42545 c42545
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42545_5
  · exact u35789
  · exact u35790
  · exact u35791
  · exact u35792
  · exact u35793
  · exact u35794
  · exact u35795
  · exact u35796
  · exact u35797

theorem m42546_6 : Upper (D 6) (R 6) [34,65,160,17,6] 13 :=
  permutation_upper _ _ _ [34,65,160,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35789

def r42546 : Route 9 := (fun mask => (mask,id))

def c42546 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42546 : Upper (D 6) (R 6) [34,65,160,17] 13 := by
  apply FastRouting.sound _ _ [34,65,160,17] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r42546 c42546
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42546_6
  · exact u35798
  · exact u35799
  · exact u35800
  · exact u35801
  · exact u35802
  · exact u35803
  · exact u35804
  · exact u35805
  · exact u35806

theorem m42547_5 : Upper (D 6) (R 6) [34,65,160,18,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35780

theorem m42547_9 : Upper (D 6) (R 6) [34,65,160,18,9] 13 :=
  permutation_upper _ _ _ [34,65,160,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35798

def r42547 : Route 9 := (fun mask => (mask,id))

def c42547 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42547 : Upper (D 6) (R 6) [34,65,160,18] 13 := by
  apply FastRouting.sound _ _ [34,65,160,18] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r42547 c42547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42547_5
  · exact m42547_9
  · exact u35807
  · exact u35808
  · exact u35809
  · exact u35810
  · exact u35811
  · exact u35812
  · exact u35813
  · exact u35814

theorem m42548_3 : Upper (D 6) (R 6) [34,65,160,20,3] 13 :=
  permutation_upper _ _ _ [34,65,160,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35773

theorem m42548_5 : Upper (D 6) (R 6) [34,65,160,20,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35781

theorem m42548_6 : Upper (D 6) (R 6) [34,65,160,20,6] 13 :=
  permutation_upper _ _ _ [34,65,160,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35790

theorem m42548_9 : Upper (D 6) (R 6) [34,65,160,20,9] 13 :=
  permutation_upper _ _ _ [34,65,160,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35799

theorem m42548_10 : Upper (D 6) (R 6) [34,65,160,20,10] 13 :=
  permutation_upper _ _ _ [34,65,160,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35807

def r42548 : Route 9 := (fun mask => (mask,id))

def c42548 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42548 : Upper (D 6) (R 6) [34,65,160,20] 13 := by
  apply FastRouting.sound _ _ [34,65,160,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,257,258,260,264,320] r42548 c42548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42548_3
  · exact m42548_5
  · exact m42548_6
  · exact m42548_9
  · exact m42548_10
  · exact u35815
  · exact u35816
  · exact u35817
  · exact u35818
  · exact u35819
  · exact u35820
  · exact u35821
  · exact u35822
  · exact u35823
  · exact u35824

def b42549 : PairBound 9 := { available := 286, camps := [{ cop := 1, region := 8, targets := 36 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 35 67 164 73 286 318 350 414 286), lower := (rows 35 67 164 73 16 32 64 128 256), losses := [] }

theorem u42549 : Upper (D 6) (R 6) [34,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42550 : PairBound 9 := { available := 285, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 164 74 285 317 349 413 285), lower := (rows 35 67 164 74 16 32 64 128 256), losses := [] }

theorem u42550 : Upper (D 6) (R 6) [34,65,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42551_3 : Upper (D 6) (R 6) [34,65,160,68,3] 13 :=
  permutation_upper _ _ _ [34,65,160,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35774

theorem m42551_5 : Upper (D 6) (R 6) [34,65,160,68,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35783

theorem m42551_6 : Upper (D 6) (R 6) [34,65,160,68,6] 13 :=
  permutation_upper _ _ _ [34,65,160,6,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35792

theorem m42551_9 : Upper (D 6) (R 6) [34,65,160,68,9] 13 :=
  permutation_upper _ _ _ [34,65,160,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35801

theorem m42551_10 : Upper (D 6) (R 6) [34,65,160,68,10] 13 :=
  permutation_upper _ _ _ [34,65,160,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35809

theorem m42551_12 : Upper (D 6) (R 6) [34,65,160,68,12] 13 :=
  permutation_upper _ _ _ [34,65,160,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35818

def r42551 : Route 9 := (fun mask => (mask,id))

def c42551 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42551 : Upper (D 6) (R 6) [34,65,160,68] 13 := by
  apply FastRouting.sound _ _ [34,65,160,68] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r42551 c42551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42551_3
  · exact m42551_5
  · exact m42551_6
  · exact m42551_9
  · exact m42551_10
  · exact m42551_12
  · exact u35831
  · exact u35832
  · exact u35833
  · exact u35834

theorem m42552_3 : Upper (D 6) (R 6) [34,65,160,80,3] 13 :=
  permutation_upper _ _ _ [34,65,160,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35775

theorem m42552_5 : Upper (D 6) (R 6) [34,65,160,80,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35784

theorem m42552_6 : Upper (D 6) (R 6) [34,65,160,80,6] 13 :=
  permutation_upper _ _ _ [34,65,160,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35793

theorem m42552_9 : Upper (D 6) (R 6) [34,65,160,80,9] 13 :=
  permutation_upper _ _ _ [34,65,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35802

theorem m42552_10 : Upper (D 6) (R 6) [34,65,160,80,10] 13 :=
  permutation_upper _ _ _ [34,65,160,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35810

theorem m42552_12 : Upper (D 6) (R 6) [34,65,160,80,12] 13 :=
  permutation_upper _ _ _ [34,65,160,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35819

def r42552 : Route 9 := (fun mask => (mask,id))

def c42552 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42552 : Upper (D 6) (R 6) [34,65,160,80] 13 := by
  apply FastRouting.sound _ _ [34,65,160,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r42552 c42552
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42552_3
  · exact m42552_5
  · exact m42552_6
  · exact m42552_9
  · exact m42552_10
  · exact m42552_12
  · exact u35835
  · exact u35836
  · exact u35837
  · exact u35838

theorem m42553_6 : Upper (D 6) (R 6) [34,65,160,257,6] 13 :=
  permutation_upper _ _ _ [34,65,160,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35794

theorem m42553_10 : Upper (D 6) (R 6) [34,65,160,257,10] 13 :=
  permutation_upper _ _ _ [34,65,160,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35811

theorem m42553_12 : Upper (D 6) (R 6) [34,65,160,257,12] 13 :=
  permutation_upper _ _ _ [34,65,160,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35820

theorem m42553_66 : Upper (D 6) (R 6) [34,65,160,257,66] 13 :=
  permutation_upper _ _ _ [34,65,160,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35828

theorem m42553_68 : Upper (D 6) (R 6) [34,65,160,257,68] 13 :=
  permutation_upper _ _ _ [34,65,160,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35831

theorem m42553_72 : Upper (D 6) (R 6) [34,65,160,257,72] 13 :=
  permutation_upper _ _ _ [34,65,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35835

def r42553 : Route 9 := (fun mask => (mask,id))

def c42553 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42553 : Upper (D 6) (R 6) [34,65,160,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,257] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42553 c42553
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42553_6
  · exact m42553_10
  · exact m42553_12
  · exact m42553_66
  · exact m42553_68
  · exact m42553_72

theorem m42554_5 : Upper (D 6) (R 6) [34,65,160,258,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35785

theorem m42554_9 : Upper (D 6) (R 6) [34,65,160,258,9] 13 :=
  permutation_upper _ _ _ [34,65,160,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35803

theorem m42554_12 : Upper (D 6) (R 6) [34,65,160,258,12] 13 :=
  permutation_upper _ _ _ [34,65,160,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35821

theorem m42554_65 : Upper (D 6) (R 6) [34,65,160,258,65] 13 :=
  permutation_upper _ _ _ [34,65,160,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35825

theorem m42554_68 : Upper (D 6) (R 6) [34,65,160,258,68] 13 :=
  permutation_upper _ _ _ [34,65,160,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35832

theorem m42554_72 : Upper (D 6) (R 6) [34,65,160,258,72] 13 :=
  permutation_upper _ _ _ [34,65,160,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35836

def r42554 : Route 9 := (fun mask => (mask,id))

def c42554 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42554 : Upper (D 6) (R 6) [34,65,160,258] 13 := by
  apply FastRouting.sound _ _ [34,65,160,258] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42554 c42554
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42554_5
  · exact m42554_9
  · exact m42554_12
  · exact m42554_65
  · exact m42554_68
  · exact m42554_72

theorem m42555_3 : Upper (D 6) (R 6) [34,65,160,260,3] 13 :=
  permutation_upper _ _ _ [34,65,160,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35776

theorem m42555_5 : Upper (D 6) (R 6) [34,65,160,260,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35786

theorem m42555_6 : Upper (D 6) (R 6) [34,65,160,260,6] 13 :=
  permutation_upper _ _ _ [34,65,160,6,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35795

theorem m42555_9 : Upper (D 6) (R 6) [34,65,160,260,9] 13 :=
  permutation_upper _ _ _ [34,65,160,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35804

theorem m42555_10 : Upper (D 6) (R 6) [34,65,160,260,10] 13 :=
  permutation_upper _ _ _ [34,65,160,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35812

theorem m42555_12 : Upper (D 6) (R 6) [34,65,160,260,12] 13 :=
  permutation_upper _ _ _ [34,65,160,20,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35822

theorem m42555_65 : Upper (D 6) (R 6) [34,65,160,260,65] 13 :=
  permutation_upper _ _ _ [34,65,160,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35826

theorem m42555_66 : Upper (D 6) (R 6) [34,65,160,260,66] 13 :=
  permutation_upper _ _ _ [34,65,160,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35829

theorem m42555_68 : Upper (D 6) (R 6) [34,65,160,260,68] 13 :=
  permutation_upper _ _ _ [34,65,160,68,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35833

theorem m42555_72 : Upper (D 6) (R 6) [34,65,160,260,72] 13 :=
  permutation_upper _ _ _ [34,65,160,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35837

def r42555 : Route 9 := (fun mask => (mask,id))

def c42555 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42555 : Upper (D 6) (R 6) [34,65,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42555 c42555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42555_3
  · exact m42555_5
  · exact m42555_6
  · exact m42555_9
  · exact m42555_10
  · exact m42555_12
  · exact m42555_65
  · exact m42555_66
  · exact m42555_68
  · exact m42555_72

theorem m42556_3 : Upper (D 6) (R 6) [34,65,160,272,3] 13 :=
  permutation_upper _ _ _ [34,65,160,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35777

theorem m42556_5 : Upper (D 6) (R 6) [34,65,160,272,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35787

theorem m42556_6 : Upper (D 6) (R 6) [34,65,160,272,6] 13 :=
  permutation_upper _ _ _ [34,65,160,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35796

theorem m42556_9 : Upper (D 6) (R 6) [34,65,160,272,9] 13 :=
  permutation_upper _ _ _ [34,65,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35805

theorem m42556_10 : Upper (D 6) (R 6) [34,65,160,272,10] 13 :=
  permutation_upper _ _ _ [34,65,160,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35813

theorem m42556_12 : Upper (D 6) (R 6) [34,65,160,272,12] 13 :=
  permutation_upper _ _ _ [34,65,160,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35823

theorem m42556_65 : Upper (D 6) (R 6) [34,65,160,272,65] 13 :=
  permutation_upper _ _ _ [34,65,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35827

theorem m42556_66 : Upper (D 6) (R 6) [34,65,160,272,66] 13 :=
  permutation_upper _ _ _ [34,65,160,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35830

theorem m42556_68 : Upper (D 6) (R 6) [34,65,160,272,68] 13 :=
  permutation_upper _ _ _ [34,65,160,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35834

theorem m42556_72 : Upper (D 6) (R 6) [34,65,160,272,72] 13 :=
  permutation_upper _ _ _ [34,65,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35838

def r42556 : Route 9 := (fun mask => (mask,id))

def c42556 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42556 : Upper (D 6) (R 6) [34,65,160,272] 13 := by
  apply FastRouting.sound _ _ [34,65,160,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42556 c42556
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42556_3
  · exact m42556_5
  · exact m42556_6
  · exact m42556_9
  · exact m42556_10
  · exact m42556_12
  · exact m42556_65
  · exact m42556_66
  · exact m42556_68
  · exact m42556_72

theorem m42557_3 : Upper (D 6) (R 6) [34,65,160,320,3] 13 :=
  permutation_upper _ _ _ [34,65,160,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35778

theorem m42557_5 : Upper (D 6) (R 6) [34,65,160,320,5] 13 :=
  permutation_upper _ _ _ [34,65,160,5,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35788

theorem m42557_6 : Upper (D 6) (R 6) [34,65,160,320,6] 13 :=
  permutation_upper _ _ _ [34,65,160,6,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35797

theorem m42557_9 : Upper (D 6) (R 6) [34,65,160,320,9] 13 :=
  permutation_upper _ _ _ [34,65,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35806

theorem m42557_10 : Upper (D 6) (R 6) [34,65,160,320,10] 13 :=
  permutation_upper _ _ _ [34,65,160,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35814

theorem m42557_12 : Upper (D 6) (R 6) [34,65,160,320,12] 13 :=
  permutation_upper _ _ _ [34,65,160,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35824

def r42557 : Route 9 := (fun mask => (mask,id))

def c42557 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42557 : Upper (D 6) (R 6) [34,65,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,160,320] 13 (by decide) (choices 2) [3,5,6,9,10,12] r42557 c42557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42557_3
  · exact m42557_5
  · exact m42557_6
  · exact m42557_9
  · exact m42557_10
  · exact m42557_12

def b42558 : PairBound 9 := { available := 124, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 388 11 124 124 124 252 380), lower := (rows 35 67 388 11 16 32 64 128 256), losses := [] }

theorem u42558 : Upper (D 6) (R 6) [34,65,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42559 : Route 9 := (fun mask => (mask,id))

def c42559 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42559 : Upper (D 6) (R 6) [34,65,384,5] 13 := by
  apply FastRouting.sound _ _ [34,65,384,5] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42559 c42559
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35843
  · exact u35844
  · exact u35845
  · exact u35846
  · exact u35847
  · exact u35848
  · exact u35849
  · exact u35850
  · exact u35851
  · exact u35852

theorem m42560_6 : Upper (D 6) (R 6) [34,65,384,17,6] 13 :=
  permutation_upper _ _ _ [34,65,384,5,10] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35844

def r42560 : Route 9 := (fun mask => (mask,id))

def c42560 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42560 : Upper (D 6) (R 6) [34,65,384,17] 13 := by
  apply FastRouting.sound _ _ [34,65,384,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42560 c42560
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42560_6
  · exact u35853
  · exact u35854
  · exact u35855
  · exact u35856
  · exact u35857
  · exact u35858
  · exact u35859
  · exact u35860
  · exact u35861

theorem m42561_3 : Upper (D 6) (R 6) [34,65,384,20,3] 13 :=
  permutation_upper _ _ _ [34,65,384,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35839

theorem m42561_5 : Upper (D 6) (R 6) [34,65,384,20,5] 13 :=
  permutation_upper _ _ _ [34,65,384,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35845

theorem m42561_6 : Upper (D 6) (R 6) [34,65,384,20,6] 13 :=
  permutation_upper _ _ _ [34,65,384,5,12] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35845

theorem m42561_9 : Upper (D 6) (R 6) [34,65,384,20,9] 13 :=
  permutation_upper _ _ _ [34,65,384,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35854

theorem m42561_10 : Upper (D 6) (R 6) [34,65,384,20,10] 13 :=
  permutation_upper _ _ _ [34,65,384,17,12] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35854

theorem m42561_65 : Upper (D 6) (R 6) [34,65,384,20,65] 13 :=
  permutation_upper _ _ _ [34,65,384,20,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35864

theorem m42561_66 : Upper (D 6) (R 6) [34,65,384,20,66] 13 :=
  permutation_upper _ _ _ [34,65,384,20,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35863

theorem m42561_68 : Upper (D 6) (R 6) [34,65,384,20,68] 13 :=
  permutation_upper _ _ _ [34,65,384,20,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35865

theorem m42561_72 : Upper (D 6) (R 6) [34,65,384,20,72] 13 :=
  permutation_upper _ _ _ [34,65,384,20,40] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35866

def r42561 : Route 9 := (fun mask => (mask,id))

def c42561 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42561 : Upper (D 6) (R 6) [34,65,384,20] 13 := by
  apply FastRouting.sound _ _ [34,65,384,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r42561 c42561
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42561_3
  · exact m42561_5
  · exact m42561_6
  · exact m42561_9
  · exact m42561_10
  · exact u35862
  · exact u35863
  · exact u35864
  · exact u35865
  · exact u35866
  · exact m42561_65
  · exact m42561_66
  · exact m42561_68
  · exact m42561_72
  · exact u35867

def b42562 : PairBound 9 := { available := 94, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 67 388 41 94 126 94 222 350), lower := (rows 35 67 388 41 16 32 64 128 256), losses := [] }

theorem u42562 : Upper (D 6) (R 6) [34,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42563 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 388 42 93 125 93 221 349), lower := (rows 35 67 388 42 16 32 64 128 256), losses := [] }

theorem u42563 : Upper (D 6) (R 6) [34,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42564_3 : Upper (D 6) (R 6) [34,65,384,36,3] 13 :=
  permutation_upper _ _ _ [34,65,384,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35840

theorem m42564_5 : Upper (D 6) (R 6) [34,65,384,36,5] 13 :=
  permutation_upper _ _ _ [34,65,384,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35847

theorem m42564_6 : Upper (D 6) (R 6) [34,65,384,36,6] 13 :=
  permutation_upper _ _ _ [34,65,384,5,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35850

theorem m42564_9 : Upper (D 6) (R 6) [34,65,384,36,9] 13 :=
  permutation_upper _ _ _ [34,65,384,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35856

theorem m42564_10 : Upper (D 6) (R 6) [34,65,384,36,10] 13 :=
  permutation_upper _ _ _ [34,65,384,17,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35859

theorem m42564_12 : Upper (D 6) (R 6) [34,65,384,36,12] 13 :=
  permutation_upper _ _ _ [34,65,384,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35865

theorem m42564_65 : Upper (D 6) (R 6) [34,65,384,36,65] 13 :=
  permutation_upper _ _ _ [34,65,384,34,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35870

theorem m42564_66 : Upper (D 6) (R 6) [34,65,384,36,66] 13 :=
  permutation_upper _ _ _ [34,65,384,33,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35868

def r42564 : Route 9 := (fun mask => (mask,id))

def c42564 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42564 : Upper (D 6) (R 6) [34,65,384,36] 13 := by
  apply FastRouting.sound _ _ [34,65,384,36] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42564 c42564
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42564_3
  · exact m42564_5
  · exact m42564_6
  · exact m42564_9
  · exact m42564_10
  · exact m42564_12
  · exact m42564_65
  · exact m42564_66
  · exact u35872
  · exact u35873

theorem m42565_3 : Upper (D 6) (R 6) [34,65,384,48,3] 13 :=
  permutation_upper _ _ _ [34,65,384,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35841

theorem m42565_5 : Upper (D 6) (R 6) [34,65,384,48,5] 13 :=
  permutation_upper _ _ _ [34,65,384,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35848

theorem m42565_6 : Upper (D 6) (R 6) [34,65,384,48,6] 13 :=
  permutation_upper _ _ _ [34,65,384,5,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35851

theorem m42565_9 : Upper (D 6) (R 6) [34,65,384,48,9] 13 :=
  permutation_upper _ _ _ [34,65,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35857

theorem m42565_10 : Upper (D 6) (R 6) [34,65,384,48,10] 13 :=
  permutation_upper _ _ _ [34,65,384,17,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35860

theorem m42565_12 : Upper (D 6) (R 6) [34,65,384,48,12] 13 :=
  permutation_upper _ _ _ [34,65,384,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35866

theorem m42565_65 : Upper (D 6) (R 6) [34,65,384,48,65] 13 :=
  permutation_upper _ _ _ [34,65,384,34,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35871

theorem m42565_66 : Upper (D 6) (R 6) [34,65,384,48,66] 13 :=
  permutation_upper _ _ _ [34,65,384,33,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35869

theorem m42565_68 : Upper (D 6) (R 6) [34,65,384,48,68] 13 :=
  permutation_upper _ _ _ [34,65,384,36,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35873

def r42565 : Route 9 := (fun mask => (mask,id))

def c42565 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42565 : Upper (D 6) (R 6) [34,65,384,48] 13 := by
  apply FastRouting.sound _ _ [34,65,384,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42565 c42565
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42565_3
  · exact m42565_5
  · exact m42565_6
  · exact m42565_9
  · exact m42565_10
  · exact m42565_12
  · exact m42565_65
  · exact m42565_66
  · exact m42565_68
  · exact u35874

theorem m42566_3 : Upper (D 6) (R 6) [34,65,384,96,3] 13 :=
  permutation_upper _ _ _ [34,65,384,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35842

theorem m42566_5 : Upper (D 6) (R 6) [34,65,384,96,5] 13 :=
  permutation_upper _ _ _ [34,65,384,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35852

theorem m42566_6 : Upper (D 6) (R 6) [34,65,384,96,6] 13 :=
  permutation_upper _ _ _ [34,65,384,5,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35852

theorem m42566_9 : Upper (D 6) (R 6) [34,65,384,96,9] 13 :=
  permutation_upper _ _ _ [34,65,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35861

theorem m42566_10 : Upper (D 6) (R 6) [34,65,384,96,10] 13 :=
  permutation_upper _ _ _ [34,65,384,17,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35861

theorem m42566_12 : Upper (D 6) (R 6) [34,65,384,96,12] 13 :=
  permutation_upper _ _ _ [34,65,384,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35867

def r42566 : Route 9 := (fun mask => (mask,id))

def c42566 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42566 : Upper (D 6) (R 6) [34,65,384,96] 13 := by
  apply FastRouting.sound _ _ [34,65,384,96] 13 (by decide) (choices 2) [3,5,6,9,10,12] r42566 c42566
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42566_3
  · exact m42566_5
  · exact m42566_6
  · exact m42566_9
  · exact m42566_10
  · exact m42566_12

def b42567 : PairBound 9 := { available := 469, camps := [{ cop := 0, region := 8, targets := 36 },{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6),(3,2),(3,5)], upper := (rows 35 70 44 11 469 501 469 469 469), lower := (rows 35 70 44 11 16 32 64 128 256), losses := [] }

theorem u42567 : Upper (D 6) (R 6) [34,68,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42568 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 12, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 70 44 13 467 499 467 467 467), lower := (rows 35 70 44 13 16 32 64 128 256), losses := [] }

theorem u42568 : Upper (D 6) (R 6) [34,68,40,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42569 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 44 14 465 497 465 465 465), lower := (rows 35 70 44 14 16 32 64 128 256), losses := [] }

theorem u42569 : Upper (D 6) (R 6) [34,68,40,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42570 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42570 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42570 : Upper (D 6) (R 6) [34,68,40,17] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r42570 c42570
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35875
  · exact u35876
  · exact u35877
  · exact u35878
  · exact u35879
  · exact u35880
  · exact u35881
  · exact u35882
  · exact u35883
  · exact u35884
  · exact u35885

def r42571 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42571 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42571 : Upper (D 6) (R 6) [34,68,40,18] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18] 13 (by decide) (choices 2) [5,65,68,129,132,192,384] r42571 c42571
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35886
  · exact u35887
  · exact u35888
  · exact u35889
  · exact u35890
  · exact u35891
  · exact u35892

def b42572 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 433, targets := 4 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 70 44 28 467 483 451 451 451), lower := (rows 35 70 44 28 16 32 64 128 256), losses := [] }

theorem u42572 : Upper (D 6) (R 6) [34,68,40,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42573 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42573 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42573 : Upper (D 6) (R 6) [34,68,40,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,65] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42573 c42573
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35893
  · exact u35894
  · exact u35895
  · exact u35896
  · exact u35897
  · exact u35898
  · exact u35899

def b42574 : PairBound 9 := { available := 405, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 44 74 405 437 469 405 405), lower := (rows 35 70 44 74 16 32 64 128 256), losses := [] }

theorem u42574 : Upper (D 6) (R 6) [34,68,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42575 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 1, region := 433, targets := 4 }], pairs := [(0,2),(3,0),(3,5)], upper := (rows 35 70 44 76 403 435 467 403 403), lower := (rows 35 70 44 76 16 32 64 128 256), losses := [] }

theorem u42575 : Upper (D 6) (R 6) [34,68,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42576 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42576 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42576 : Upper (D 6) (R 6) [34,68,40,80] 13 := by
  apply FastRouting.sound _ _ [34,68,40,80] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42576 c42576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35900
  · exact u35901
  · exact u35902
  · exact u35903
  · exact u35904
  · exact u35905
  · exact u35906

def r42577 : Route 9 := (fun mask => (mask,id))

def c42577 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42577 : Upper (D 6) (R 6) [34,68,40,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42577 c42577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35907
  · exact u35908
  · exact u35909
  · exact u35910
  · exact u35911
  · exact u35912
  · exact u35913
  · exact u35914
  · exact u35915
  · exact u35916

def r42578 : Route 9 := (fun mask => (mask,id))

def c42578 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42578 : Upper (D 6) (R 6) [34,68,40,130] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42578 c42578
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35917
  · exact u35918
  · exact u35919
  · exact u35920
  · exact u35921
  · exact u35922

def b42579 : PairBound 9 := { available := 339, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 70 44 140 339 371 339 467 339), lower := (rows 35 70 44 140 16 32 64 128 256), losses := [] }

theorem u42579 : Upper (D 6) (R 6) [34,68,40,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42580 : Route 9 := (fun mask => (mask,id))

def c42580 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42580 : Upper (D 6) (R 6) [34,68,40,144] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42580 c42580
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35923
  · exact u35924
  · exact u35925
  · exact u35926
  · exact u35927
  · exact u35928
  · exact u35929
  · exact u35930
  · exact u35931
  · exact u35932

def r42581 : Route 9 := (fun mask => (mask,id))

def c42581 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42581 : Upper (D 6) (R 6) [34,68,40,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42581 c42581
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35933
  · exact u35934
  · exact u35935
  · exact u35936
  · exact u35937
  · exact u35938

def r42582 : Route 9 := (fun mask => (mask,id))

def c42582 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42582 : Upper (D 6) (R 6) [34,68,40,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42582 c42582
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35939
  · exact u35940
  · exact u35941
  · exact u35942
  · exact u35943
  · exact u35944

def b42583 : PairBound 9 := { available := 380, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 133 11 380 380 380 508 380), lower := (rows 35 70 133 11 16 32 64 128 256), losses := [] }

theorem u42583 : Upper (D 6) (R 6) [34,68,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42584 : PairBound 9 := { available := 378, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 70 133 13 378 378 378 506 378), lower := (rows 35 70 133 13 16 32 64 128 256), losses := [] }

theorem u42584 : Upper (D 6) (R 6) [34,68,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42585 : PairBound 9 := { available := 377, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 133 14 377 377 377 505 377), lower := (rows 35 70 133 14 16 32 64 128 256), losses := [] }

theorem u42585 : Upper (D 6) (R 6) [34,68,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42586_6 : Upper (D 6) (R 6) [34,68,129,17,6] 13 :=
  permutation_upper _ _ _ [34,68,129,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35962

def r42586 : Route 9 := (fun mask => (mask,id))

def c42586 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42586 : Upper (D 6) (R 6) [34,68,129,17] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,258,260,264,288,320] r42586 c42586
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42586_6
  · exact u35971
  · exact u35972
  · exact u35973
  · exact u35974
  · exact u35975
  · exact u35976
  · exact u35977
  · exact u35978
  · exact u35979
  · exact u35980
  · exact u35981
  · exact u35982
  · exact u35983
  · exact u35984

theorem m42587_5 : Upper (D 6) (R 6) [34,68,129,18,5] 13 :=
  permutation_upper _ _ _ [34,68,129,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35954

theorem m42587_9 : Upper (D 6) (R 6) [34,68,129,18,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35971

def r42587 : Route 9 := (fun mask => (mask,id))

def c42587 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42587 : Upper (D 6) (R 6) [34,68,129,18] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,257,260,264,288,320] r42587 c42587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42587_5
  · exact m42587_9
  · exact u35985
  · exact u35986
  · exact u35987
  · exact u35988
  · exact u35989
  · exact u35990
  · exact u35991
  · exact u35992
  · exact u35993
  · exact u35994
  · exact u35995
  · exact u35996
  · exact u35997

theorem m42588_3 : Upper (D 6) (R 6) [34,68,129,20,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35945

theorem m42588_9 : Upper (D 6) (R 6) [34,68,129,20,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35972

theorem m42588_10 : Upper (D 6) (R 6) [34,68,129,20,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35985

def r42588 : Route 9 := (fun mask => (mask,id))

def c42588 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42588 : Upper (D 6) (R 6) [34,68,129,20] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,257,258,264,288,320] r42588 c42588
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42588_3
  · exact m42588_9
  · exact m42588_10
  · exact u35998
  · exact u35999
  · exact u36000
  · exact u36001
  · exact u36002
  · exact u36003
  · exact u36004
  · exact u36005
  · exact u36006
  · exact u36007
  · exact u36008
  · exact u36009

def b42589 : PairBound 9 := { available := 350, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 133 41 350 382 350 478 350), lower := (rows 35 70 133 41 16 32 64 128 256), losses := [] }

theorem u42589 : Upper (D 6) (R 6) [34,68,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42590 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 133 42 349 381 349 477 349), lower := (rows 35 70 133 42 16 32 64 128 256), losses := [] }

theorem u42590 : Upper (D 6) (R 6) [34,68,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42591_3 : Upper (D 6) (R 6) [34,68,129,36,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35946

theorem m42591_9 : Upper (D 6) (R 6) [34,68,129,36,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35974

theorem m42591_10 : Upper (D 6) (R 6) [34,68,129,36,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35987

def r42591 : Route 9 := (fun mask => (mask,id))

def c42591 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42591 : Upper (D 6) (R 6) [34,68,129,36] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r42591 c42591
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42591_3
  · exact m42591_9
  · exact m42591_10
  · exact u36021
  · exact u36022
  · exact u36023
  · exact u36024
  · exact u36025
  · exact u36026
  · exact u36027

theorem m42592_3 : Upper (D 6) (R 6) [34,68,129,48,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35947

theorem m42592_5 : Upper (D 6) (R 6) [34,68,129,48,5] 13 :=
  permutation_upper _ _ _ [34,68,129,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35955

theorem m42592_6 : Upper (D 6) (R 6) [34,68,129,48,6] 13 :=
  permutation_upper _ _ _ [34,68,129,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35963

theorem m42592_9 : Upper (D 6) (R 6) [34,68,129,48,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35975

theorem m42592_10 : Upper (D 6) (R 6) [34,68,129,48,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35988

theorem m42592_12 : Upper (D 6) (R 6) [34,68,129,48,12] 13 :=
  permutation_upper _ _ _ [34,68,129,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36000

def r42592 : Route 9 := (fun mask => (mask,id))

def c42592 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42592 : Upper (D 6) (R 6) [34,68,129,48] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,257,258,260,264,320] r42592 c42592
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42592_3
  · exact m42592_5
  · exact m42592_6
  · exact m42592_9
  · exact m42592_10
  · exact m42592_12
  · exact u36028
  · exact u36029
  · exact u36030
  · exact u36031
  · exact u36032
  · exact u36033
  · exact u36034
  · exact u36035
  · exact u36036

theorem m42593_6 : Upper (D 6) (R 6) [34,68,129,65,6] 13 :=
  permutation_upper _ _ _ [34,68,129,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35964

theorem m42593_10 : Upper (D 6) (R 6) [34,68,129,65,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35989

theorem m42593_12 : Upper (D 6) (R 6) [34,68,129,65,12] 13 :=
  permutation_upper _ _ _ [34,68,129,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36001

theorem m42593_34 : Upper (D 6) (R 6) [34,68,129,65,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36015

theorem m42593_36 : Upper (D 6) (R 6) [34,68,129,65,36] 13 :=
  permutation_upper _ _ _ [34,68,129,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36021

theorem m42593_40 : Upper (D 6) (R 6) [34,68,129,65,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36028

def r42593 : Route 9 := (fun mask => (mask,id))

def c42593 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42593 : Upper (D 6) (R 6) [34,68,129,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r42593 c42593
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42593_6
  · exact m42593_10
  · exact m42593_12
  · exact m42593_34
  · exact m42593_36
  · exact m42593_40
  · exact u36037
  · exact u36038
  · exact u36039
  · exact u36040

def b42594 : PairBound 9 := { available := 317, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 133 74 317 317 381 445 317), lower := (rows 35 70 133 74 16 32 64 128 256), losses := [] }

theorem u42594 : Upper (D 6) (R 6) [34,68,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42595 : PairBound 9 := { available := 315, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 133 76 315 315 379 443 315), lower := (rows 35 70 133 76 16 32 64 128 256), losses := [] }

theorem u42595 : Upper (D 6) (R 6) [34,68,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42596_3 : Upper (D 6) (R 6) [34,68,129,80,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35948

theorem m42596_5 : Upper (D 6) (R 6) [34,68,129,80,5] 13 :=
  permutation_upper _ _ _ [34,68,129,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35956

theorem m42596_6 : Upper (D 6) (R 6) [34,68,129,80,6] 13 :=
  permutation_upper _ _ _ [34,68,129,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35965

theorem m42596_9 : Upper (D 6) (R 6) [34,68,129,80,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35978

theorem m42596_10 : Upper (D 6) (R 6) [34,68,129,80,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35991

theorem m42596_12 : Upper (D 6) (R 6) [34,68,129,80,12] 13 :=
  permutation_upper _ _ _ [34,68,129,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36003

theorem m42596_33 : Upper (D 6) (R 6) [34,68,129,80,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36010

theorem m42596_34 : Upper (D 6) (R 6) [34,68,129,80,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36016

theorem m42596_36 : Upper (D 6) (R 6) [34,68,129,80,36] 13 :=
  permutation_upper _ _ _ [34,68,129,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36023

theorem m42596_40 : Upper (D 6) (R 6) [34,68,129,80,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36031

def r42596 : Route 9 := (fun mask => (mask,id))

def c42596 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42596 : Upper (D 6) (R 6) [34,68,129,80] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r42596 c42596
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42596_3
  · exact m42596_5
  · exact m42596_6
  · exact m42596_9
  · exact m42596_10
  · exact m42596_12
  · exact m42596_33
  · exact m42596_34
  · exact m42596_36
  · exact m42596_40
  · exact u36049
  · exact u36050
  · exact u36051
  · exact u36052
  · exact u36053

theorem m42597_3 : Upper (D 6) (R 6) [34,68,129,96,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35949

theorem m42597_5 : Upper (D 6) (R 6) [34,68,129,96,5] 13 :=
  permutation_upper _ _ _ [34,68,129,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35957

theorem m42597_6 : Upper (D 6) (R 6) [34,68,129,96,6] 13 :=
  permutation_upper _ _ _ [34,68,129,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35966

theorem m42597_9 : Upper (D 6) (R 6) [34,68,129,96,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35979

theorem m42597_10 : Upper (D 6) (R 6) [34,68,129,96,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35992

theorem m42597_12 : Upper (D 6) (R 6) [34,68,129,96,12] 13 :=
  permutation_upper _ _ _ [34,68,129,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36004

def r42597 : Route 9 := (fun mask => (mask,id))

def c42597 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42597 : Upper (D 6) (R 6) [34,68,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r42597 c42597
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42597_3
  · exact m42597_5
  · exact m42597_6
  · exact m42597_9
  · exact m42597_10
  · exact m42597_12
  · exact u36054
  · exact u36055
  · exact u36056
  · exact u36057

theorem m42598_6 : Upper (D 6) (R 6) [34,68,129,257,6] 13 :=
  permutation_upper _ _ _ [34,68,129,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35967

theorem m42598_10 : Upper (D 6) (R 6) [34,68,129,257,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35993

theorem m42598_12 : Upper (D 6) (R 6) [34,68,129,257,12] 13 :=
  permutation_upper _ _ _ [34,68,129,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36005

theorem m42598_34 : Upper (D 6) (R 6) [34,68,129,257,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36017

theorem m42598_36 : Upper (D 6) (R 6) [34,68,129,257,36] 13 :=
  permutation_upper _ _ _ [34,68,129,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36024

theorem m42598_40 : Upper (D 6) (R 6) [34,68,129,257,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36032

theorem m42598_66 : Upper (D 6) (R 6) [34,68,129,257,66] 13 :=
  permutation_upper _ _ _ [34,68,129,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36041

theorem m42598_68 : Upper (D 6) (R 6) [34,68,129,257,68] 13 :=
  permutation_upper _ _ _ [34,68,129,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36045

theorem m42598_72 : Upper (D 6) (R 6) [34,68,129,257,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36049

theorem m42598_96 : Upper (D 6) (R 6) [34,68,129,257,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36054

def r42598 : Route 9 := (fun mask => (mask,id))

def c42598 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42598 : Upper (D 6) (R 6) [34,68,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42598 c42598
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42598_6
  · exact m42598_10
  · exact m42598_12
  · exact m42598_34
  · exact m42598_36
  · exact m42598_40
  · exact m42598_66
  · exact m42598_68
  · exact m42598_72
  · exact m42598_96

theorem m42599_5 : Upper (D 6) (R 6) [34,68,129,258,5] 13 :=
  permutation_upper _ _ _ [34,68,129,5,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35958

theorem m42599_9 : Upper (D 6) (R 6) [34,68,129,258,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35980

theorem m42599_12 : Upper (D 6) (R 6) [34,68,129,258,12] 13 :=
  permutation_upper _ _ _ [34,68,129,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36006

theorem m42599_33 : Upper (D 6) (R 6) [34,68,129,258,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36011

theorem m42599_36 : Upper (D 6) (R 6) [34,68,129,258,36] 13 :=
  permutation_upper _ _ _ [34,68,129,36,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36025

theorem m42599_40 : Upper (D 6) (R 6) [34,68,129,258,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36033

theorem m42599_65 : Upper (D 6) (R 6) [34,68,129,258,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36037

theorem m42599_68 : Upper (D 6) (R 6) [34,68,129,258,68] 13 :=
  permutation_upper _ _ _ [34,68,129,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36046

theorem m42599_72 : Upper (D 6) (R 6) [34,68,129,258,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36050

theorem m42599_96 : Upper (D 6) (R 6) [34,68,129,258,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36055

def r42599 : Route 9 := (fun mask => (mask,id))

def c42599 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42599 : Upper (D 6) (R 6) [34,68,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42599 c42599
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42599_5
  · exact m42599_9
  · exact m42599_12
  · exact m42599_33
  · exact m42599_36
  · exact m42599_40
  · exact m42599_65
  · exact m42599_68
  · exact m42599_72
  · exact m42599_96

#print axioms u42599
end Delivery.IrregularNine14.P06
