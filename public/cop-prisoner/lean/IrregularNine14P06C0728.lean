import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0679
import IrregularNine14P06C0680
import IrregularNine14P06C0681
import IrregularNine14P06C0682
import IrregularNine14P06C0683
import IrregularNine14P06C0684
import IrregularNine14P06C0685
import IrregularNine14P06C0686
import IrregularNine14P06C0687

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b43680 : PairBound 9 := { available := 477, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 7 35 38 477 477 509 477 477 477), lower := (rows 7 35 38 8 16 32 64 128 256), losses := [] }

theorem u43680 : Upper (D 6) (R 6) [6,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43681 : PairBound 9 := { available := 471, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 35 44 479 471 503 471 471 471), lower := (rows 7 35 44 8 16 32 64 128 256), losses := [] }

theorem u43681 : Upper (D 6) (R 6) [6,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43682_20 : Upper (D 6) (R 6) [6,33,65,20] 13 :=
  permutation_upper _ _ _ [6,33,65,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40747

theorem m43682_66 : Upper (D 6) (R 6) [6,33,65,66] 13 :=
  permutation_upper _ _ _ [6,33,65,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40749

theorem m43682_68 : Upper (D 6) (R 6) [6,33,65,68] 13 :=
  permutation_upper _ _ _ [6,33,65,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40748

theorem m43682_80 : Upper (D 6) (R 6) [6,33,65,80] 13 :=
  permutation_upper _ _ _ [6,33,65,48] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40750

theorem m43682_132 : Upper (D 6) (R 6) [6,33,65,132] 13 :=
  permutation_upper _ _ _ [6,33,65,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40752

theorem m43682_192 : Upper (D 6) (R 6) [6,33,65,192] 13 :=
  permutation_upper _ _ _ [6,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40754

def r43682 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43682 : Nat → Fin 9 := (fun _ => 0)

theorem u43682 : Upper (D 6) (R 6) [6,33,65] 13 := by
  apply FastRouting.sound _ _ [6,33,65] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,130,132,144,160,192,384] r43682 c43682
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40746
  · exact u40747
  · exact m43682_20
  · exact u40748
  · exact u40749
  · exact u40750
  · exact m43682_66
  · exact m43682_68
  · exact m43682_80
  · exact u40751
  · exact u40752
  · exact m43682_132
  · exact u40753
  · exact u40754
  · exact m43682_192
  · exact u40755

def b43683 : PairBound 9 := { available := 509, camps := [{ cop := 0, region := 504, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 35 70 509 509 509 509 509 509), lower := (rows 7 35 70 8 16 32 64 128 256), losses := [] }

theorem u43683 : Upper (D 6) (R 6) [6,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43684 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43684 : Nat → Fin 9 := (fun _ => 0)

theorem u43684 : Upper (D 6) (R 6) [6,33,72] 13 := by
  apply FastRouting.sound _ _ [6,33,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,129,130,132,144,160,192,384] r43684 c43684
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40756
  · exact u40757
  · exact u40758
  · exact u40759
  · exact u40760
  · exact u40761
  · exact u40762
  · exact u40763
  · exact u40764
  · exact u40765
  · exact u40766
  · exact u40767
  · exact u40768
  · exact u40769
  · exact u40770
  · exact u40771
  · exact u40772
  · exact u40773
  · exact u40774
  · exact u40775
  · exact u40776
  · exact u40777

def b43685 : PairBound 9 := { available := 479, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 35 100 479 479 511 479 479 479), lower := (rows 7 35 100 8 16 32 64 128 256), losses := [] }

theorem u43685 : Upper (D 6) (R 6) [6,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43686 : Route 9 := (fun mask => (mask,id))

def c43686 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43686 : Upper (D 6) (R 6) [6,33,129] 13 := by
  apply FastRouting.sound _ _ [6,33,129] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,258,260,272,288,320] r43686 c43686
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40778
  · exact u40779
  · exact u40780
  · exact u40781
  · exact u40782
  · exact u40783
  · exact u40784
  · exact u40785
  · exact u40786
  · exact u40787
  · exact u40788
  · exact u40789
  · exact u40790
  · exact u40791
  · exact u40792

def b43687 : PairBound 9 := { available := 381, camps := [{ cop := 0, region := 376, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 35 134 381 381 381 381 509 381), lower := (rows 7 35 134 8 16 32 64 128 256), losses := [] }

theorem u43687 : Upper (D 6) (R 6) [6,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43688 : Route 9 := (fun mask => (mask,id))

def c43688 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43688 : Upper (D 6) (R 6) [6,33,136] 13 := by
  apply FastRouting.sound _ _ [6,33,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43688 c43688
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40793
  · exact u40794
  · exact u40795
  · exact u40796
  · exact u40797
  · exact u40798
  · exact u40799
  · exact u40800
  · exact u40801
  · exact u40802
  · exact u40803
  · exact u40804
  · exact u40805
  · exact u40806
  · exact u40807
  · exact u40808
  · exact u40809
  · exact u40810
  · exact u40811
  · exact u40812
  · exact u40813

def b43689 : PairBound 9 := { available := 351, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 35 164 351 351 383 351 479 351), lower := (rows 7 35 164 8 16 32 64 128 256), losses := [] }

theorem u43689 : Upper (D 6) (R 6) [6,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43690 : Route 9 := (fun mask => (mask,id))

def c43690 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43690 : Upper (D 6) (R 6) [6,33,192] 13 := by
  apply FastRouting.sound _ _ [6,33,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43690 c43690
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40814
  · exact u40815
  · exact u40816
  · exact u40817
  · exact u40818
  · exact u40819
  · exact u40820
  · exact u40821
  · exact u40822
  · exact u40823
  · exact u40824
  · exact u40825
  · exact u40826
  · exact u40827
  · exact u40828
  · exact u40829
  · exact u40830
  · exact u40831
  · exact u40832
  · exact u40833
  · exact u40834

def r43691 : Route 9 := (fun mask => (mask,id))

def c43691 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43691 : Upper (D 6) (R 6) [6,33,384] 13 := by
  apply FastRouting.sound _ _ [6,33,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43691 c43691
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40835
  · exact u40836
  · exact u40837
  · exact u40838
  · exact u40839
  · exact u40840
  · exact u40841
  · exact u40842
  · exact u40843
  · exact u40844
  · exact u40845
  · exact u40846
  · exact u40847
  · exact u40848
  · exact u40849

def b43692 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 7 38 44 475 467 499 467 467 467), lower := (rows 7 38 44 8 16 32 64 128 256), losses := [] }

theorem u43692 : Upper (D 6) (R 6) [6,36,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43693 : PairBound 9 := { available := 505, camps := [{ cop := 0, region := 504, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 38 70 505 505 505 505 505 505), lower := (rows 7 38 70 8 16 32 64 128 256), losses := [] }

theorem u43693 : Upper (D 6) (R 6) [6,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43694 : PairBound 9 := { available := 499, camps := [{ cop := 0, region := 504, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 38 76 507 499 499 499 499 499), lower := (rows 7 38 76 8 16 32 64 128 256), losses := [] }

theorem u43694 : Upper (D 6) (R 6) [6,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43695 : PairBound 9 := { available := 475, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 7 38 100 475 475 507 475 475 475), lower := (rows 7 38 100 8 16 32 64 128 256), losses := [] }

theorem u43695 : Upper (D 6) (R 6) [6,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43696 : PairBound 9 := { available := 379, camps := [{ cop := 0, region := 376, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 38 133 379 379 379 379 507 379), lower := (rows 7 38 133 8 16 32 64 128 256), losses := [] }

theorem u43696 : Upper (D 6) (R 6) [6,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43697 : PairBound 9 := { available := 377, camps := [{ cop := 0, region := 376, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 38 134 377 377 377 377 505 377), lower := (rows 7 38 134 8 16 32 64 128 256), losses := [] }

theorem u43697 : Upper (D 6) (R 6) [6,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43698 : PairBound 9 := { available := 371, camps := [{ cop := 0, region := 376, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 38 140 379 371 371 371 499 371), lower := (rows 7 38 140 8 16 32 64 128 256), losses := [] }

theorem u43698 : Upper (D 6) (R 6) [6,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43699 : PairBound 9 := { available := 347, camps := [{ cop := 1, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 7 38 164 347 347 379 347 475 347), lower := (rows 7 38 164 8 16 32 64 128 256), losses := [] }

theorem u43699 : Upper (D 6) (R 6) [6,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43700 : PairBound 9 := { available := 379, camps := [{ cop := 0, region := 376, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 38 196 379 379 379 379 507 379), lower := (rows 7 38 196 8 16 32 64 128 256), losses := [] }

theorem u43700 : Upper (D 6) (R 6) [6,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43701 : PairBound 9 := { available := 123, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 38 388 123 123 123 123 251 379), lower := (rows 7 38 388 8 16 32 64 128 256), losses := [] }

theorem u43701 : Upper (D 6) (R 6) [6,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43702 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43702 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43702 : Upper (D 6) (R 6) [6,40,48] 13 := by
  apply FastRouting.sound _ _ [6,40,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r43702 c43702
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40850
  · exact u40851
  · exact u40852
  · exact u40853
  · exact u40854
  · exact u40855
  · exact u40856
  · exact u40857
  · exact u40858
  · exact u40859
  · exact u40860

def r43703 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43703 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43703 : Upper (D 6) (R 6) [6,40,80] 13 := by
  apply FastRouting.sound _ _ [6,40,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43703 c43703
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40861
  · exact u40862
  · exact u40863
  · exact u40864
  · exact u40865
  · exact u40866
  · exact u40867
  · exact u40868
  · exact u40869
  · exact u40870
  · exact u40871
  · exact u40872
  · exact u40873
  · exact u40874
  · exact u40875
  · exact u40876

def r43704 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43704 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43704 : Upper (D 6) (R 6) [6,40,96] 13 := by
  apply FastRouting.sound _ _ [6,40,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192,384] r43704 c43704
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40877
  · exact u40878
  · exact u40879
  · exact u40880
  · exact u40881
  · exact u40882
  · exact u40883
  · exact u40884
  · exact u40885
  · exact u40886
  · exact u40887
  · exact u40888
  · exact u40889
  · exact u40890
  · exact u40891
  · exact u40892

def r43705 : Route 9 := (fun mask => (mask,id))

def c43705 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43705 : Upper (D 6) (R 6) [6,40,129] 13 := by
  apply FastRouting.sound _ _ [6,40,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43705 c43705
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40893
  · exact u40894
  · exact u40895
  · exact u40896
  · exact u40897
  · exact u40898
  · exact u40899
  · exact u40900
  · exact u40901
  · exact u40902
  · exact u40903
  · exact u40904
  · exact u40905
  · exact u40906
  · exact u40907
  · exact u40908
  · exact u40909
  · exact u40910
  · exact u40911
  · exact u40912
  · exact u40913

def b43706 : PairBound 9 := { available := 373, camps := [{ cop := 0, region := 376, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 42 134 381 373 373 373 501 373), lower := (rows 7 42 134 8 16 32 64 128 256), losses := [] }

theorem u43706 : Upper (D 6) (R 6) [6,40,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43707 : Route 9 := (fun mask => (mask,id))

def c43707 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43707 : Upper (D 6) (R 6) [6,40,144] 13 := by
  apply FastRouting.sound _ _ [6,40,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43707 c43707
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40914
  · exact u40915
  · exact u40916
  · exact u40917
  · exact u40918
  · exact u40919
  · exact u40920
  · exact u40921
  · exact u40922
  · exact u40923
  · exact u40924
  · exact u40925
  · exact u40926
  · exact u40927
  · exact u40928

def r43708 : Route 9 := (fun mask => (mask,id))

def c43708 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43708 : Upper (D 6) (R 6) [6,40,160] 13 := by
  apply FastRouting.sound _ _ [6,40,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43708 c43708
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40929
  · exact u40930
  · exact u40931
  · exact u40932
  · exact u40933
  · exact u40934
  · exact u40935
  · exact u40936
  · exact u40937
  · exact u40938
  · exact u40939
  · exact u40940
  · exact u40941
  · exact u40942
  · exact u40943

def r43709 : Route 9 := (fun mask => (mask,id))

def c43709 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43709 : Upper (D 6) (R 6) [6,40,192] 13 := by
  apply FastRouting.sound _ _ [6,40,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43709 c43709
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40944
  · exact u40945
  · exact u40946
  · exact u40947
  · exact u40948
  · exact u40949
  · exact u40950
  · exact u40951
  · exact u40952
  · exact u40953
  · exact u40954
  · exact u40955
  · exact u40956
  · exact u40957
  · exact u40958
  · exact u40959
  · exact u40960
  · exact u40961
  · exact u40962
  · exact u40963
  · exact u40964

def r43710 : Route 9 := (fun mask => (mask,id))

def c43710 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43710 : Upper (D 6) (R 6) [6,40,384] 13 := by
  apply FastRouting.sound _ _ [6,40,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43710 c43710
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40965
  · exact u40966
  · exact u40967
  · exact u40968
  · exact u40969
  · exact u40970
  · exact u40971
  · exact u40972
  · exact u40973
  · exact u40974
  · exact u40975
  · exact u40976
  · exact u40977
  · exact u40978
  · exact u40979

def b43711 : PairBound 9 := { available := 415, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 100 415 415 447 479 415 415), lower := (rows 7 98 100 8 16 32 64 128 256), losses := [] }

theorem u43711 : Upper (D 6) (R 6) [6,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43712 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43712 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43712 : Upper (D 6) (R 6) [6,96,129] 13 := by
  apply FastRouting.sound _ _ [6,96,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,257,258,260,272,288] r43712 c43712
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40980
  · exact u40981
  · exact u40982
  · exact u40983
  · exact u40984
  · exact u40985
  · exact u40986
  · exact u40987
  · exact u40988
  · exact u40989
  · exact u40990
  · exact u40991
  · exact u40992
  · exact u40993
  · exact u40994
  · exact u40995

def b43713 : PairBound 9 := { available := 381, camps := [{ cop := 0, region := 376, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 98 134 381 381 381 381 509 381), lower := (rows 7 98 134 8 16 32 64 128 256), losses := [] }

theorem u43713 : Upper (D 6) (R 6) [6,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43714 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43714 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43714 : Upper (D 6) (R 6) [6,96,136] 13 := by
  apply FastRouting.sound _ _ [6,96,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,257,258,260,272,288] r43714 c43714
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40996
  · exact u40997
  · exact u40998
  · exact u40999
  · exact u41000
  · exact u41001
  · exact u41002
  · exact u41003
  · exact u41004
  · exact u41005
  · exact u41006
  · exact u41007
  · exact u41008
  · exact u41009
  · exact u41010
  · exact u41011

def r43715 : Route 9 := (fun mask => (mask,id))

def c43715 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43715 : Upper (D 6) (R 6) [6,96,160] 13 := by
  apply FastRouting.sound _ _ [6,96,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43715 c43715
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41012
  · exact u41013
  · exact u41014
  · exact u41015
  · exact u41016
  · exact u41017
  · exact u41018
  · exact u41019
  · exact u41020
  · exact u41021
  · exact u41022
  · exact u41023
  · exact u41024
  · exact u41025
  · exact u41026

def r43716 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43716 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43716 : Upper (D 6) (R 6) [6,96,384] 13 := by
  apply FastRouting.sound _ _ [6,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96] r43716 c43716
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41027
  · exact u41028
  · exact u41029
  · exact u41030
  · exact u41031
  · exact u41032
  · exact u41033
  · exact u41034
  · exact u41035
  · exact u41036
  · exact u41037

theorem m43717_20 : Upper (D 6) (R 6) [6,129,257,20] 13 :=
  permutation_upper _ _ _ [6,129,257,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41039

theorem m43717_36 : Upper (D 6) (R 6) [6,129,257,36] 13 :=
  permutation_upper _ _ _ [6,129,257,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41040

def r43717 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43717 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43717 : Upper (D 6) (R 6) [6,129,257] 13 := by
  apply FastRouting.sound _ _ [6,129,257] 13 (by decide) (choices 2) [6,18,20,34,36,48,96] r43717 c43717
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41038
  · exact u41039
  · exact m43717_20
  · exact u41040
  · exact m43717_36
  · exact u41041
  · exact u41042

def b43718 : PairBound 9 := { available := 125, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 131 262 125 125 125 125 253 381), lower := (rows 7 131 262 8 16 32 64 128 256), losses := [] }

theorem u43718 : Upper (D 6) (R 6) [6,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43719 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43719 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43719 : Upper (D 6) (R 6) [6,129,264] 13 := by
  apply FastRouting.sound _ _ [6,129,264] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96] r43719 c43719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41043
  · exact u41044
  · exact u41045
  · exact u41046
  · exact u41047
  · exact u41048
  · exact u41049
  · exact u41050
  · exact u41051
  · exact u41052
  · exact u41053

def r43720 : Route 9 := (fun mask => (mask,id))

def c43720 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43720 : Upper (D 6) (R 6) [6,129,288] 13 := by
  apply FastRouting.sound _ _ [6,129,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43720 c43720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41054
  · exact u41055
  · exact u41056
  · exact u41057
  · exact u41058
  · exact u41059
  · exact u41060
  · exact u41061
  · exact u41062
  · exact u41063
  · exact u41064
  · exact u41065
  · exact u41066
  · exact u41067
  · exact u41068

def b43721 : PairBound 9 := { available := 121, camps := [{ cop := 0, region := 120, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 134 262 121 121 121 121 249 377), lower := (rows 7 134 262 8 16 32 64 128 256), losses := [] }

theorem u43721 : Upper (D 6) (R 6) [6,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43722 : PairBound 9 := { available := 115, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 134 268 123 115 115 115 243 371), lower := (rows 7 134 268 8 16 32 64 128 256), losses := [] }

theorem u43722 : Upper (D 6) (R 6) [6,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43723 : PairBound 9 := { available := 123, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 134 292 123 123 123 123 251 379), lower := (rows 7 134 292 8 16 32 64 128 256), losses := [] }

theorem u43723 : Upper (D 6) (R 6) [6,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43724 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43724 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43724 : Upper (D 6) (R 6) [6,136,272] 13 := by
  apply FastRouting.sound _ _ [6,136,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43724 c43724
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41069
  · exact u41070
  · exact u41071
  · exact u41072
  · exact u41073
  · exact u41074
  · exact u41075

def r43725 : Route 9 := (fun mask => (mask,id))

def c43725 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43725 : Upper (D 6) (R 6) [6,136,288] 13 := by
  apply FastRouting.sound _ _ [6,136,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43725 c43725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41076
  · exact u41077
  · exact u41078
  · exact u41079
  · exact u41080
  · exact u41081
  · exact u41082
  · exact u41083
  · exact u41084
  · exact u41085
  · exact u41086
  · exact u41087
  · exact u41088
  · exact u41089
  · exact u41090

theorem m43726_5 : Upper (D 6) (R 6) [6,160,288,5] 13 :=
  permutation_upper _ _ _ [6,160,288,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41091

theorem m43726_20 : Upper (D 6) (R 6) [6,160,288,20] 13 :=
  permutation_upper _ _ _ [6,160,288,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41094

theorem m43726_68 : Upper (D 6) (R 6) [6,160,288,68] 13 :=
  permutation_upper _ _ _ [6,160,288,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41096

def r43726 : Route 9 := (fun mask => (mask,id))

def c43726 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43726 : Upper (D 6) (R 6) [6,160,288] 13 := by
  apply FastRouting.sound _ _ [6,160,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43726 c43726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41091
  · exact m43726_5
  · exact u41092
  · exact u41093
  · exact u41094
  · exact m43726_20
  · exact u41095
  · exact u41096
  · exact m43726_68
  · exact u41097

theorem m43727_5 : Upper (D 6) (R 6) [6,160,320,5] 13 :=
  permutation_upper _ _ _ [6,160,320,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41098

theorem m43727_20 : Upper (D 6) (R 6) [6,160,320,20] 13 :=
  permutation_upper _ _ _ [6,160,320,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41101

theorem m43727_65 : Upper (D 6) (R 6) [6,160,320,65] 13 :=
  permutation_upper _ _ _ [6,160,320,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41102

theorem m43727_66 : Upper (D 6) (R 6) [6,160,320,66] 13 :=
  permutation_upper _ _ _ [6,160,320,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41104

theorem m43727_68 : Upper (D 6) (R 6) [6,160,320,68] 13 :=
  permutation_upper _ _ _ [6,160,320,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41103

theorem m43727_80 : Upper (D 6) (R 6) [6,160,320,80] 13 :=
  permutation_upper _ _ _ [6,160,320,48] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41105

def r43727 : Route 9 := (fun mask => (mask,id))

def c43727 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43727 : Upper (D 6) (R 6) [6,160,320] 13 := by
  apply FastRouting.sound _ _ [6,160,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43727 c43727
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41098
  · exact m43727_5
  · exact u41099
  · exact u41100
  · exact u41101
  · exact m43727_20
  · exact u41102
  · exact u41103
  · exact u41104
  · exact u41105
  · exact m43727_65
  · exact m43727_66
  · exact m43727_68
  · exact m43727_80
  · exact u41106

def r43728 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43728 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43728 : Upper (D 6) (R 6) [10,17,33] 13 := by
  apply FastRouting.sound _ _ [10,17,33] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r43728 c43728
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41107
  · exact u41108
  · exact u41109
  · exact u41110
  · exact u41111
  · exact u41112
  · exact u41113
  · exact u41114
  · exact u41115
  · exact u41116
  · exact u41117

def r43729 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43729 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43729 : Upper (D 6) (R 6) [10,17,96] 13 := by
  apply FastRouting.sound _ _ [10,17,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160,384] r43729 c43729
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41118
  · exact u41119
  · exact u41120
  · exact u41121
  · exact u41122
  · exact u41123
  · exact u41124
  · exact u41125
  · exact u41126
  · exact u41127
  · exact u41128
  · exact u41129

def r43730 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43730 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43730 : Upper (D 6) (R 6) [10,17,129] 13 := by
  apply FastRouting.sound _ _ [10,17,129] 13 (by decide) (choices 2) [6,34,36,96,258,260,288] r43730 c43730
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41130
  · exact u41131
  · exact u41132
  · exact u41133
  · exact u41134
  · exact u41135
  · exact u41136

def r43731 : Route 9 := (fun mask => (mask,id))

def c43731 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43731 : Upper (D 6) (R 6) [10,17,160] 13 := by
  apply FastRouting.sound _ _ [10,17,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43731 c43731
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41137
  · exact u41138
  · exact u41139
  · exact u41140
  · exact u41141
  · exact u41142
  · exact u41143
  · exact u41144
  · exact u41145
  · exact u41146
  · exact u41147
  · exact u41148
  · exact u41149
  · exact u41150
  · exact u41151

def r43732 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43732 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43732 : Upper (D 6) (R 6) [10,17,384] 13 := by
  apply FastRouting.sound _ _ [10,17,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43732 c43732
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41152
  · exact u41153
  · exact u41154
  · exact u41155
  · exact u41156
  · exact u41157
  · exact u41158

def r43733 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43733 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43733 : Upper (D 6) (R 6) [10,20,33] 13 := by
  apply FastRouting.sound _ _ [10,20,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43733 c43733
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41159
  · exact u41160
  · exact u41161
  · exact u41162
  · exact u41163
  · exact u41164
  · exact u41165
  · exact u41166
  · exact u41167
  · exact u41168
  · exact u41169
  · exact u41170
  · exact u41171
  · exact u41172
  · exact u41173
  · exact u41174

def r43734 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43734 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43734 : Upper (D 6) (R 6) [10,20,34] 13 := by
  apply FastRouting.sound _ _ [10,20,34] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r43734 c43734
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41175
  · exact u41176
  · exact u41177
  · exact u41178
  · exact u41179
  · exact u41180
  · exact u41181
  · exact u41182
  · exact u41183
  · exact u41184
  · exact u41185

def r43735 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43735 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43735 : Upper (D 6) (R 6) [10,20,96] 13 := by
  apply FastRouting.sound _ _ [10,20,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160,384] r43735 c43735
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41186
  · exact u41187
  · exact u41188
  · exact u41189
  · exact u41190
  · exact u41191
  · exact u41192
  · exact u41193
  · exact u41194
  · exact u41195
  · exact u41196
  · exact u41197

def r43736 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43736 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43736 : Upper (D 6) (R 6) [10,20,129] 13 := by
  apply FastRouting.sound _ _ [10,20,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r43736 c43736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41198
  · exact u41199
  · exact u41200
  · exact u41201
  · exact u41202
  · exact u41203
  · exact u41204
  · exact u41205
  · exact u41206
  · exact u41207
  · exact u41208

def r43737 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43737 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43737 : Upper (D 6) (R 6) [10,20,130] 13 := by
  apply FastRouting.sound _ _ [10,20,130] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r43737 c43737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41209
  · exact u41210
  · exact u41211
  · exact u41212
  · exact u41213
  · exact u41214
  · exact u41215

def r43738 : Route 9 := (fun mask => (mask,id))

def c43738 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43738 : Upper (D 6) (R 6) [10,20,160] 13 := by
  apply FastRouting.sound _ _ [10,20,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43738 c43738
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41216
  · exact u41217
  · exact u41218
  · exact u41219
  · exact u41220
  · exact u41221
  · exact u41222
  · exact u41223
  · exact u41224
  · exact u41225
  · exact u41226
  · exact u41227
  · exact u41228
  · exact u41229
  · exact u41230

def r43739 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43739 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43739 : Upper (D 6) (R 6) [10,20,384] 13 := by
  apply FastRouting.sound _ _ [10,20,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43739 c43739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41231
  · exact u41232
  · exact u41233
  · exact u41234
  · exact u41235
  · exact u41236
  · exact u41237

#print axioms u43739
end Delivery.IrregularNine14.P06
