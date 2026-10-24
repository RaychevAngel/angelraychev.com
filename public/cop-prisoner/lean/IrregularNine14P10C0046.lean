import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0018
import IrregularNine14P10C0019
import IrregularNine14P10C0020
import IrregularNine14P10C0021
import IrregularNine14P10C0022
import IrregularNine14P10C0023
import IrregularNine14P10C0024
import IrregularNine14P10C0025
import IrregularNine14P10C0029
import IrregularNine14P10C0030

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2760 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 41 440 440 504 440 440), lower := (rows 7 98 196 41 16 32 64 128 256), losses := [] }

theorem u2760 : Upper (D 10) (R 10) [6,96,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2760 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2761 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 137 312 312 376 440 312), lower := (rows 7 98 196 137 16 32 64 128 256), losses := [] }

theorem u2761 : Upper (D 10) (R 10) [6,96,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2761 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2762 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 168 313 313 377 441 313), lower := (rows 7 98 196 168 16 32 64 128 256), losses := [] }

theorem u2762 : Upper (D 10) (R 10) [6,96,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2762 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2763 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 265 440 440 504 440 440), lower := (rows 7 98 196 265 16 32 64 128 256), losses := [] }

theorem u2763 : Upper (D 10) (R 10) [6,96,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2763 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2764 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 296 441 441 505 441 441), lower := (rows 7 98 196 296 16 32 64 128 256), losses := [] }

theorem u2764 : Upper (D 10) (R 10) [6,96,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2764 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2765 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 392 313 313 377 441 313), lower := (rows 7 98 196 392 16 32 64 128 256), losses := [] }

theorem u2765 : Upper (D 10) (R 10) [6,96,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2765 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2766_40 : Upper (D 10) (R 10) [6,96,384,17,40] 13 :=
  permutation_upper _ _ _ [6,24,33,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1155

theorem m2766_72 : Upper (D 10) (R 10) [6,96,384,17,72] 13 :=
  permutation_upper _ _ _ [6,24,65,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1159

theorem m2766_96 : Upper (D 10) (R 10) [6,96,384,17,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1175

theorem m2766_136 : Upper (D 10) (R 10) [6,96,384,17,136] 13 :=
  permutation_upper _ _ _ [6,24,65,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1163

theorem m2766_160 : Upper (D 10) (R 10) [6,96,384,17,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1184

theorem m2766_192 : Upper (D 10) (R 10) [6,96,384,17,192] 13 :=
  permutation_upper _ _ _ [6,24,192,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1198

theorem m2766_384 : Upper (D 10) (R 10) [6,96,384,17,384] 13 :=
  permutation_upper _ _ _ [6,24,192,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1200

def r2766 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2766 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2766 : Upper (D 10) (R 10) [6,96,384,17] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2766 c2766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2766_40
  · exact m2766_72
  · exact m2766_96
  · exact m2766_136
  · exact m2766_160
  · exact m2766_192
  · exact m2766_384

def r2767 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2767 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2767 : Upper (D 10) (R 10) [6,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2767 c2767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1796
  · exact u1797
  · exact u1798
  · exact u1799
  · exact u1800
  · exact u1801
  · exact u1802

theorem m2768_9 : Upper (D 10) (R 10) [6,96,384,48,9] 13 :=
  permutation_upper _ _ _ [6,24,33,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1155

theorem m2768_33 : Upper (D 10) (R 10) [6,96,384,48,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1796

def r2768 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2768 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2768 : Upper (D 10) (R 10) [6,96,384,48] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,384] r2768 c2768
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2768_9
  · exact m2768_33
  · exact u1803
  · exact u1804
  · exact u1805
  · exact u1806
  · exact u1807
  · exact u1808
  · exact u1809
  · exact u1810
  · exact u1811

def b2769 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 98 388 73 440 440 504 440 440), lower := (rows 7 98 388 73 16 32 64 128 256), losses := [] }

theorem u2769 : Upper (D 10) (R 10) [6,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2769 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2770_9 : Upper (D 10) (R 10) [6,96,384,80,9] 13 :=
  permutation_upper _ _ _ [6,24,65,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1159

theorem m2770_33 : Upper (D 10) (R 10) [6,96,384,80,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1797

theorem m2770_40 : Upper (D 10) (R 10) [6,96,384,80,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1805

def r2770 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2770 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2770 : Upper (D 10) (R 10) [6,96,384,80] 13 := by
  apply FastRouting.sound _ _ [6,96,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,384] r2770 c2770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2770_9
  · exact m2770_33
  · exact m2770_40
  · exact u1814
  · exact u1815
  · exact u1816
  · exact u1817

def b2771 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 388 104 441 441 505 441 441), lower := (rows 7 98 388 104 16 32 64 128 256), losses := [] }

theorem u2771 : Upper (D 10) (R 10) [6,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2771 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2772 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 98 388 137 376 376 376 504 376), lower := (rows 7 98 388 137 16 32 64 128 256), losses := [] }

theorem u2772 : Upper (D 10) (R 10) [6,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2772 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2773_9 : Upper (D 10) (R 10) [6,96,384,144,9] 13 :=
  permutation_upper _ _ _ [6,24,65,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1163

theorem m2773_33 : Upper (D 10) (R 10) [6,96,384,144,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1799

theorem m2773_40 : Upper (D 10) (R 10) [6,96,384,144,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1808

theorem m2773_65 : Upper (D 10) (R 10) [6,96,384,144,65] 13 :=
  permutation_upper _ _ _ [6,96,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1812

theorem m2773_72 : Upper (D 10) (R 10) [6,96,384,144,72] 13 :=
  permutation_upper _ _ _ [6,96,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1815

theorem m2773_96 : Upper (D 10) (R 10) [6,96,384,144,96] 13 :=
  permutation_upper _ _ _ [6,96,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1818

theorem m2773_257 : Upper (D 10) (R 10) [6,96,384,144,257] 13 :=
  permutation_upper _ _ _ [6,96,384,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1820

def r2773 : Route 9 := (fun mask => (mask,id))

def c2773 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2773 : Upper (D 10) (R 10) [6,96,384,144] 13 := by
  apply FastRouting.sound _ _ [6,96,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r2773 c2773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2773_9
  · exact m2773_33
  · exact m2773_40
  · exact m2773_65
  · exact m2773_72
  · exact m2773_96
  · exact m2773_257
  · exact u1823
  · exact u1824
  · exact u1825

theorem m2774_9 : Upper (D 10) (R 10) [6,96,384,160,9] 13 :=
  permutation_upper _ _ _ [6,24,96,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1184

theorem m2774_33 : Upper (D 10) (R 10) [6,96,384,160,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1800

theorem m2774_40 : Upper (D 10) (R 10) [6,96,384,160,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1809

theorem m2774_65 : Upper (D 10) (R 10) [6,96,384,160,65] 13 :=
  permutation_upper _ _ _ [6,96,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1813

theorem m2774_72 : Upper (D 10) (R 10) [6,96,384,160,72] 13 :=
  permutation_upper _ _ _ [6,96,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1816

theorem m2774_96 : Upper (D 10) (R 10) [6,96,384,160,96] 13 :=
  permutation_upper _ _ _ [6,96,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1819

theorem m2774_257 : Upper (D 10) (R 10) [6,96,384,160,257] 13 :=
  permutation_upper _ _ _ [6,96,384,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1821

theorem m2774_264 : Upper (D 10) (R 10) [6,96,384,160,264] 13 :=
  permutation_upper _ _ _ [6,96,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1824

def r2774 : Route 9 := (fun mask => (mask,id))

def c2774 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2774 : Upper (D 10) (R 10) [6,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r2774 c2774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2774_9
  · exact m2774_33
  · exact m2774_40
  · exact m2774_65
  · exact m2774_72
  · exact m2774_96
  · exact m2774_257
  · exact m2774_264
  · exact u1826
  · exact u1827

theorem m2775_9 : Upper (D 10) (R 10) [6,96,384,192,9] 13 :=
  permutation_upper _ _ _ [6,24,192,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1198

theorem m2775_33 : Upper (D 10) (R 10) [6,96,384,192,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1801

theorem m2775_40 : Upper (D 10) (R 10) [6,96,384,192,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1810

theorem m2775_257 : Upper (D 10) (R 10) [6,96,384,192,257] 13 :=
  permutation_upper _ _ _ [6,96,384,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1822

theorem m2775_264 : Upper (D 10) (R 10) [6,96,384,192,264] 13 :=
  permutation_upper _ _ _ [6,96,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1825

theorem m2775_288 : Upper (D 10) (R 10) [6,96,384,192,288] 13 :=
  permutation_upper _ _ _ [6,96,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1827

def r2775 : Route 9 := (fun mask => (mask,id))

def c2775 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2775 : Upper (D 10) (R 10) [6,96,384,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r2775 c2775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2775_9
  · exact m2775_33
  · exact m2775_40
  · exact m2775_257
  · exact m2775_264
  · exact m2775_288

def b2776 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 98 388 392 121 121 121 249 377), lower := (rows 7 98 388 392 16 32 64 128 256), losses := [] }

theorem u2776 : Upper (D 10) (R 10) [6,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2776 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2777 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 5, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 194 196 41 312 312 376 440 312), lower := (rows 7 194 196 41 16 32 64 128 256), losses := [] }

theorem u2777 : Upper (D 10) (R 10) [6,192,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2777 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2778 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 5, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 194 196 265 312 312 376 440 312), lower := (rows 7 194 196 265 16 32 64 128 256), losses := [] }

theorem u2778 : Upper (D 10) (R 10) [6,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2778 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2779 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 5, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 194 196 296 313 313 377 441 313), lower := (rows 7 194 196 296 16 32 64 128 256), losses := [] }

theorem u2779 : Upper (D 10) (R 10) [6,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2779 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2780 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 25 440 424 488 424 424), lower := (rows 7 194 324 25 16 32 64 128 256), losses := [] }

theorem u2780 : Upper (D 10) (R 10) [6,192,320,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2780 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2781 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 41 440 440 504 440 440), lower := (rows 7 194 324 41 16 32 64 128 256), losses := [] }

theorem u2781 : Upper (D 10) (R 10) [6,192,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2781 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2782 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 137 312 312 376 440 312), lower := (rows 7 194 324 137 16 32 64 128 256), losses := [] }

theorem u2782 : Upper (D 10) (R 10) [6,192,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2782 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2783 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 168 313 313 377 441 313), lower := (rows 7 194 324 168 16 32 64 128 256), losses := [] }

theorem u2783 : Upper (D 10) (R 10) [6,192,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2783 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 392 57 57 121 185 313), lower := (rows 7 194 324 392 16 32 64 128 256), losses := [] }

theorem u2784 : Upper (D 10) (R 10) [6,192,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2784 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2785_96 : Upper (D 10) (R 10) [18,33,40,68,96] 13 :=
  permutation_upper _ _ _ [6,33,96,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1241

theorem m2785_160 : Upper (D 10) (R 10) [18,33,40,68,160] 13 :=
  permutation_upper _ _ _ [6,33,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1242

theorem m2785_192 : Upper (D 10) (R 10) [18,33,40,68,192] 13 :=
  permutation_upper _ _ _ [6,33,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1258

theorem m2785_384 : Upper (D 10) (R 10) [18,33,40,68,384] 13 :=
  permutation_upper _ _ _ [6,33,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1261

def r2785 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2785 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2785 : Upper (D 10) (R 10) [18,33,40,68] 13 := by
  apply FastRouting.sound _ _ [18,33,40,68] 13 (by decide) (choices 2) [96,160,192,384] r2785 c2785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2785_96
  · exact m2785_160
  · exact m2785_192
  · exact m2785_384

theorem m2786_36 : Upper (D 10) (R 10) [18,33,40,192,36] 13 :=
  permutation_upper _ _ _ [6,33,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1206

theorem m2786_68 : Upper (D 10) (R 10) [18,33,40,192,68] 13 :=
  permutation_upper _ _ _ [6,33,72,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1216

theorem m2786_96 : Upper (D 10) (R 10) [18,33,40,192,96] 13 :=
  permutation_upper _ _ _ [6,33,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1243

theorem m2786_192 : Upper (D 10) (R 10) [18,33,40,192,192] 13 :=
  permutation_upper _ _ _ [6,33,192,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1260

theorem m2786_260 : Upper (D 10) (R 10) [18,33,40,192,260] 13 :=
  permutation_upper _ _ _ [6,33,72,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1217

theorem m2786_288 : Upper (D 10) (R 10) [18,33,40,192,288] 13 :=
  permutation_upper _ _ _ [6,33,96,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1244

theorem m2786_320 : Upper (D 10) (R 10) [18,33,40,192,320] 13 :=
  permutation_upper _ _ _ [6,33,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1263

def r2786 : Route 9 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2786 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2786 : Upper (D 10) (R 10) [18,33,40,192] 13 := by
  apply FastRouting.sound _ _ [18,33,40,192] 13 (by decide) (choices 2) [36,68,96,192,260,288,320] r2786 c2786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2786_36
  · exact m2786_68
  · exact m2786_96
  · exact m2786_192
  · exact m2786_260
  · exact m2786_288
  · exact m2786_320

theorem m2787_96 : Upper (D 10) (R 10) [18,33,72,132,96] 13 :=
  permutation_upper _ _ _ [6,33,96,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1245

theorem m2787_160 : Upper (D 10) (R 10) [18,33,72,132,160] 13 :=
  permutation_upper _ _ _ [6,33,96,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1245

theorem m2787_192 : Upper (D 10) (R 10) [18,33,72,132,192] 13 :=
  permutation_upper _ _ _ [6,33,192,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1264

theorem m2787_288 : Upper (D 10) (R 10) [18,33,72,132,288] 13 :=
  permutation_upper _ _ _ [6,33,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1250

theorem m2787_320 : Upper (D 10) (R 10) [18,33,72,132,320] 13 :=
  permutation_upper _ _ _ [6,33,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1266

theorem m2787_384 : Upper (D 10) (R 10) [18,33,72,132,384] 13 :=
  permutation_upper _ _ _ [6,33,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1266

def r2787 : Route 9 := (fun mask => (mask,id))

def c2787 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2787 : Upper (D 10) (R 10) [18,33,72,132] 13 := by
  apply FastRouting.sound _ _ [18,33,72,132] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2787 c2787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2787_96
  · exact m2787_160
  · exact m2787_192
  · exact m2787_288
  · exact m2787_320
  · exact m2787_384

theorem m2788_36 : Upper (D 10) (R 10) [18,33,72,160,36] 13 :=
  permutation_upper _ _ _ [6,33,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1207

theorem m2788_68 : Upper (D 10) (R 10) [18,33,72,160,68] 13 :=
  permutation_upper _ _ _ [6,33,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1218

theorem m2788_96 : Upper (D 10) (R 10) [18,33,72,160,96] 13 :=
  permutation_upper _ _ _ [6,33,96,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1246

theorem m2788_132 : Upper (D 10) (R 10) [18,33,72,160,132] 13 :=
  permutation_upper _ _ _ [6,33,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1222

theorem m2788_160 : Upper (D 10) (R 10) [18,33,72,160,160] 13 :=
  permutation_upper _ _ _ [6,33,96,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1248

theorem m2788_192 : Upper (D 10) (R 10) [18,33,72,160,192] 13 :=
  permutation_upper _ _ _ [6,33,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1265

theorem m2788_260 : Upper (D 10) (R 10) [18,33,72,160,260] 13 :=
  permutation_upper _ _ _ [6,33,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1225

theorem m2788_288 : Upper (D 10) (R 10) [18,33,72,160,288] 13 :=
  permutation_upper _ _ _ [6,33,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1251

theorem m2788_320 : Upper (D 10) (R 10) [18,33,72,160,320] 13 :=
  permutation_upper _ _ _ [6,33,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1267

theorem m2788_384 : Upper (D 10) (R 10) [18,33,72,160,384] 13 :=
  permutation_upper _ _ _ [6,33,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1270

def r2788 : Route 9 := (fun mask => (mask,id))

def c2788 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2788 : Upper (D 10) (R 10) [18,33,72,160] 13 := by
  apply FastRouting.sound _ _ [18,33,72,160] 13 (by decide) (choices 2) [36,68,96,132,160,192,260,288,320,384] r2788 c2788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2788_36
  · exact m2788_68
  · exact m2788_96
  · exact m2788_132
  · exact m2788_160
  · exact m2788_192
  · exact m2788_260
  · exact m2788_288
  · exact m2788_320
  · exact m2788_384

theorem m2789_36 : Upper (D 10) (R 10) [18,33,72,384,36] 13 :=
  permutation_upper _ _ _ [6,33,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1208

theorem m2789_68 : Upper (D 10) (R 10) [18,33,72,384,68] 13 :=
  permutation_upper _ _ _ [6,33,72,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1219

theorem m2789_96 : Upper (D 10) (R 10) [18,33,72,384,96] 13 :=
  permutation_upper _ _ _ [6,33,96,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1247

theorem m2789_132 : Upper (D 10) (R 10) [18,33,72,384,132] 13 :=
  permutation_upper _ _ _ [6,33,72,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1226

theorem m2789_160 : Upper (D 10) (R 10) [18,33,72,384,160] 13 :=
  permutation_upper _ _ _ [6,33,96,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1252

theorem m2789_192 : Upper (D 10) (R 10) [18,33,72,384,192] 13 :=
  permutation_upper _ _ _ [6,33,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1268

theorem m2789_384 : Upper (D 10) (R 10) [18,33,72,384,384] 13 :=
  permutation_upper _ _ _ [6,33,192,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1273

def r2789 : Route 9 := (fun mask => match mask with | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2789 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2789 : Upper (D 10) (R 10) [18,33,72,384] 13 := by
  apply FastRouting.sound _ _ [18,33,72,384] 13 (by decide) (choices 2) [36,68,96,132,160,192,384] r2789 c2789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2789_36
  · exact m2789_68
  · exact m2789_96
  · exact m2789_132
  · exact m2789_160
  · exact m2789_192
  · exact m2789_384

theorem m2790_12 : Upper (D 10) (R 10) [18,33,96,160,12] 13 :=
  permutation_upper _ _ _ [6,24,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1153

theorem m2790_68 : Upper (D 10) (R 10) [18,33,96,160,68] 13 :=
  permutation_upper _ _ _ [6,33,72,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1220

theorem m2790_72 : Upper (D 10) (R 10) [18,33,96,160,72] 13 :=
  permutation_upper _ _ _ [6,33,72,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1228

theorem m2790_132 : Upper (D 10) (R 10) [18,33,96,160,132] 13 :=
  permutation_upper _ _ _ [6,33,72,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1228

theorem m2790_136 : Upper (D 10) (R 10) [18,33,96,160,136] 13 :=
  permutation_upper _ _ _ [6,33,72,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1220

theorem m2790_192 : Upper (D 10) (R 10) [18,33,96,160,192] 13 :=
  permutation_upper _ _ _ [6,33,192,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1269

theorem m2790_260 : Upper (D 10) (R 10) [18,33,96,160,260] 13 :=
  permutation_upper _ _ _ [6,33,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1231

theorem m2790_264 : Upper (D 10) (R 10) [18,33,96,160,264] 13 :=
  permutation_upper _ _ _ [6,33,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1231

theorem m2790_320 : Upper (D 10) (R 10) [18,33,96,160,320] 13 :=
  permutation_upper _ _ _ [6,33,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1271

theorem m2790_384 : Upper (D 10) (R 10) [18,33,96,160,384] 13 :=
  permutation_upper _ _ _ [6,33,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1271

def r2790 : Route 9 := (fun mask => (mask,id))

def c2790 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u2790 : Upper (D 10) (R 10) [18,33,96,160] 13 := by
  apply FastRouting.sound _ _ [18,33,96,160] 13 (by decide) (choices 2) [12,68,72,132,136,192,260,264,320,384] r2790 c2790
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2790_12
  · exact m2790_68
  · exact m2790_72
  · exact m2790_132
  · exact m2790_136
  · exact m2790_192
  · exact m2790_260
  · exact m2790_264
  · exact m2790_320
  · exact m2790_384

theorem m2791_12 : Upper (D 10) (R 10) [18,33,96,192,12] 13 :=
  permutation_upper _ _ _ [6,24,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1154

theorem m2791_36 : Upper (D 10) (R 10) [18,33,96,192,36] 13 :=
  permutation_upper _ _ _ [6,33,40,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1209

theorem m2791_40 : Upper (D 10) (R 10) [18,33,96,192,40] 13 :=
  permutation_upper _ _ _ [6,33,40,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1211

theorem m2791_132 : Upper (D 10) (R 10) [18,33,96,192,132] 13 :=
  permutation_upper _ _ _ [6,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1230

theorem m2791_136 : Upper (D 10) (R 10) [18,33,96,192,136] 13 :=
  permutation_upper _ _ _ [6,33,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1234

theorem m2791_160 : Upper (D 10) (R 10) [18,33,96,192,160] 13 :=
  permutation_upper _ _ _ [6,33,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1253

theorem m2791_260 : Upper (D 10) (R 10) [18,33,96,192,260] 13 :=
  permutation_upper _ _ _ [6,33,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1233

theorem m2791_264 : Upper (D 10) (R 10) [18,33,96,192,264] 13 :=
  permutation_upper _ _ _ [6,33,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1238

theorem m2791_288 : Upper (D 10) (R 10) [18,33,96,192,288] 13 :=
  permutation_upper _ _ _ [6,33,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1255

theorem m2791_384 : Upper (D 10) (R 10) [18,33,96,192,384] 13 :=
  permutation_upper _ _ _ [6,33,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1279

def r2791 : Route 9 := (fun mask => (mask,id))

def c2791 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2791 : Upper (D 10) (R 10) [18,33,96,192] 13 := by
  apply FastRouting.sound _ _ [18,33,96,192] 13 (by decide) (choices 2) [12,36,40,132,136,160,260,264,288,384] r2791 c2791
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2791_12
  · exact m2791_36
  · exact m2791_40
  · exact m2791_132
  · exact m2791_136
  · exact m2791_160
  · exact m2791_260
  · exact m2791_264
  · exact m2791_288
  · exact m2791_384

theorem m2792_12 : Upper (D 10) (R 10) [18,33,96,384,12] 13 :=
  permutation_upper _ _ _ [6,24,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1155

theorem m2792_36 : Upper (D 10) (R 10) [18,33,96,384,36] 13 :=
  permutation_upper _ _ _ [6,33,40,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1210

theorem m2792_40 : Upper (D 10) (R 10) [18,33,96,384,40] 13 :=
  permutation_upper _ _ _ [6,33,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1212

theorem m2792_68 : Upper (D 10) (R 10) [18,33,96,384,68] 13 :=
  permutation_upper _ _ _ [6,33,72,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1221

theorem m2792_72 : Upper (D 10) (R 10) [18,33,96,384,72] 13 :=
  permutation_upper _ _ _ [6,33,72,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1237

theorem m2792_96 : Upper (D 10) (R 10) [18,33,96,384,96] 13 :=
  permutation_upper _ _ _ [6,33,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1249

theorem m2792_132 : Upper (D 10) (R 10) [18,33,96,384,132] 13 :=
  permutation_upper _ _ _ [6,33,72,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1232

theorem m2792_136 : Upper (D 10) (R 10) [18,33,96,384,136] 13 :=
  permutation_upper _ _ _ [6,33,72,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1235

theorem m2792_160 : Upper (D 10) (R 10) [18,33,96,384,160] 13 :=
  permutation_upper _ _ _ [6,33,96,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1254

theorem m2792_192 : Upper (D 10) (R 10) [18,33,96,384,192] 13 :=
  permutation_upper _ _ _ [6,33,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1272

theorem m2792_384 : Upper (D 10) (R 10) [18,33,96,384,384] 13 :=
  permutation_upper _ _ _ [6,33,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1274

def r2792 : Route 9 := (fun mask => match mask with | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2792 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u2792 : Upper (D 10) (R 10) [18,33,96,384] 13 := by
  apply FastRouting.sound _ _ [18,33,96,384] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192,384] r2792 c2792
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2792_12
  · exact m2792_36
  · exact m2792_40
  · exact m2792_68
  · exact m2792_72
  · exact m2792_96
  · exact m2792_132
  · exact m2792_136
  · exact m2792_160
  · exact m2792_192
  · exact m2792_384

theorem m2793_12 : Upper (D 10) (R 10) [18,33,192,320,12] 13 :=
  permutation_upper _ _ _ [6,24,33,192,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1157

theorem m2793_36 : Upper (D 10) (R 10) [18,33,192,320,36] 13 :=
  permutation_upper _ _ _ [6,33,40,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1213

theorem m2793_40 : Upper (D 10) (R 10) [18,33,192,320,40] 13 :=
  permutation_upper _ _ _ [6,33,40,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1213

theorem m2793_132 : Upper (D 10) (R 10) [18,33,192,320,132] 13 :=
  permutation_upper _ _ _ [6,33,72,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1236

theorem m2793_136 : Upper (D 10) (R 10) [18,33,192,320,136] 13 :=
  permutation_upper _ _ _ [6,33,72,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1239

theorem m2793_160 : Upper (D 10) (R 10) [18,33,192,320,160] 13 :=
  permutation_upper _ _ _ [6,33,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1256

theorem m2793_260 : Upper (D 10) (R 10) [18,33,192,320,260] 13 :=
  permutation_upper _ _ _ [6,33,72,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1239

theorem m2793_264 : Upper (D 10) (R 10) [18,33,192,320,264] 13 :=
  permutation_upper _ _ _ [6,33,72,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1236

theorem m2793_288 : Upper (D 10) (R 10) [18,33,192,320,288] 13 :=
  permutation_upper _ _ _ [6,33,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1256

theorem m2793_384 : Upper (D 10) (R 10) [18,33,192,320,384] 13 :=
  permutation_upper _ _ _ [6,33,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1280

def r2793 : Route 9 := (fun mask => (mask,id))

def c2793 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2793 : Upper (D 10) (R 10) [18,33,192,320] 13 := by
  apply FastRouting.sound _ _ [18,33,192,320] 13 (by decide) (choices 2) [12,36,40,132,136,160,260,264,288,384] r2793 c2793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2793_12
  · exact m2793_36
  · exact m2793_40
  · exact m2793_132
  · exact m2793_136
  · exact m2793_160
  · exact m2793_260
  · exact m2793_264
  · exact m2793_288
  · exact m2793_384

def b2794 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 37 104 472 488 456 456 456), lower := (rows 19 38 37 104 16 32 64 128 256), losses := [] }

theorem u2794 : Upper (D 10) (R 10) [18,36,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2794 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2795 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 37 200 504 488 488 488 488), lower := (rows 19 38 37 200 16 32 64 128 256), losses := [] }

theorem u2795 : Upper (D 10) (R 10) [18,36,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2795 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2796 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 44 73 496 480 480 480 480), lower := (rows 19 38 44 73 16 32 64 128 256), losses := [] }

theorem u2796 : Upper (D 10) (R 10) [18,36,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2796 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 44 200 497 481 481 481 481), lower := (rows 19 38 44 200 16 32 64 128 256), losses := [] }

theorem u2797 : Upper (D 10) (R 10) [18,36,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2797 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2798_40 : Upper (D 10) (R 10) [18,36,65,96,40] 13 :=
  permutation_upper _ _ _ [6,40,48,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1282

theorem m2798_136 : Upper (D 10) (R 10) [18,36,65,96,136] 13 :=
  permutation_upper _ _ _ [6,40,80,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1321

theorem m2798_160 : Upper (D 10) (R 10) [18,36,65,96,160] 13 :=
  permutation_upper _ _ _ [6,40,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1359

theorem m2798_384 : Upper (D 10) (R 10) [18,36,65,96,384] 13 :=
  permutation_upper _ _ _ [6,40,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1419

def r2798 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2798 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2798 : Upper (D 10) (R 10) [18,36,65,96] 13 := by
  apply FastRouting.sound _ _ [18,36,65,96] 13 (by decide) (choices 2) [40,136,160,384] r2798 c2798
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2798_40
  · exact m2798_136
  · exact m2798_160
  · exact m2798_384

theorem m2799_40 : Upper (D 10) (R 10) [18,36,65,160,40] 13 :=
  permutation_upper _ _ _ [6,40,48,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1283

theorem m2799_72 : Upper (D 10) (R 10) [18,36,65,160,72] 13 :=
  permutation_upper _ _ _ [6,40,80,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1314

theorem m2799_96 : Upper (D 10) (R 10) [18,36,65,160,96] 13 :=
  permutation_upper _ _ _ [6,40,96,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1350

theorem m2799_136 : Upper (D 10) (R 10) [18,36,65,160,136] 13 :=
  permutation_upper _ _ _ [6,40,80,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1320

theorem m2799_160 : Upper (D 10) (R 10) [18,36,65,160,160] 13 :=
  permutation_upper _ _ _ [6,40,96,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1358

theorem m2799_192 : Upper (D 10) (R 10) [18,36,65,160,192] 13 :=
  permutation_upper _ _ _ [6,40,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1400

theorem m2799_264 : Upper (D 10) (R 10) [18,36,65,160,264] 13 :=
  permutation_upper _ _ _ [6,40,80,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1323

theorem m2799_288 : Upper (D 10) (R 10) [18,36,65,160,288] 13 :=
  permutation_upper _ _ _ [6,40,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1361

theorem m2799_320 : Upper (D 10) (R 10) [18,36,65,160,320] 13 :=
  permutation_upper _ _ _ [6,40,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1401

theorem m2799_384 : Upper (D 10) (R 10) [18,36,65,160,384] 13 :=
  permutation_upper _ _ _ [6,40,192,257,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1417

def r2799 : Route 9 := (fun mask => (mask,id))

def c2799 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2799 : Upper (D 10) (R 10) [18,36,65,160] 13 := by
  apply FastRouting.sound _ _ [18,36,65,160] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2799 c2799
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2799_40
  · exact m2799_72
  · exact m2799_96
  · exact m2799_136
  · exact m2799_160
  · exact m2799_192
  · exact m2799_264
  · exact m2799_288
  · exact m2799_320
  · exact m2799_384

theorem m2800_40 : Upper (D 10) (R 10) [18,36,65,192,40] 13 :=
  permutation_upper _ _ _ [6,40,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1284

theorem m2800_136 : Upper (D 10) (R 10) [18,36,65,192,136] 13 :=
  permutation_upper _ _ _ [6,40,80,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1322

theorem m2800_160 : Upper (D 10) (R 10) [18,36,65,192,160] 13 :=
  permutation_upper _ _ _ [6,40,96,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1360

theorem m2800_264 : Upper (D 10) (R 10) [18,36,65,192,264] 13 :=
  permutation_upper _ _ _ [6,40,80,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1325

theorem m2800_288 : Upper (D 10) (R 10) [18,36,65,192,288] 13 :=
  permutation_upper _ _ _ [6,40,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1363

theorem m2800_384 : Upper (D 10) (R 10) [18,36,65,192,384] 13 :=
  permutation_upper _ _ _ [6,40,192,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1420

def r2800 : Route 9 := (fun mask => (mask,id))

def c2800 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2800 : Upper (D 10) (R 10) [18,36,65,192] 13 := by
  apply FastRouting.sound _ _ [18,36,65,192] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2800 c2800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2800_40
  · exact m2800_136
  · exact m2800_160
  · exact m2800_264
  · exact m2800_288
  · exact m2800_384

theorem m2801_40 : Upper (D 10) (R 10) [18,36,65,384,40] 13 :=
  permutation_upper _ _ _ [6,40,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1285

theorem m2801_72 : Upper (D 10) (R 10) [18,36,65,384,72] 13 :=
  permutation_upper _ _ _ [6,40,80,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1315

theorem m2801_96 : Upper (D 10) (R 10) [18,36,65,384,96] 13 :=
  permutation_upper _ _ _ [6,40,96,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1351

theorem m2801_136 : Upper (D 10) (R 10) [18,36,65,384,136] 13 :=
  permutation_upper _ _ _ [6,40,80,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1324

theorem m2801_160 : Upper (D 10) (R 10) [18,36,65,384,160] 13 :=
  permutation_upper _ _ _ [6,40,96,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1362

theorem m2801_192 : Upper (D 10) (R 10) [18,36,65,384,192] 13 :=
  permutation_upper _ _ _ [6,40,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1402

theorem m2801_384 : Upper (D 10) (R 10) [18,36,65,384,384] 13 :=
  permutation_upper _ _ _ [6,40,192,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1418

def r2801 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2801 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2801 : Upper (D 10) (R 10) [18,36,65,384] 13 := by
  apply FastRouting.sound _ _ [18,36,65,384] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2801 c2801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2801_40
  · exact m2801_72
  · exact m2801_96
  · exact m2801_136
  · exact m2801_160
  · exact m2801_192
  · exact m2801_384

theorem m2802_96 : Upper (D 10) (R 10) [18,36,72,33,96] 13 :=
  permutation_upper _ _ _ [6,40,96,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1352

theorem m2802_160 : Upper (D 10) (R 10) [18,36,72,33,160] 13 :=
  permutation_upper _ _ _ [6,40,96,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1364

theorem m2802_192 : Upper (D 10) (R 10) [18,36,72,33,192] 13 :=
  permutation_upper _ _ _ [6,40,192,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1403

theorem m2802_384 : Upper (D 10) (R 10) [18,36,72,33,384] 13 :=
  permutation_upper _ _ _ [6,40,192,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1421

def r2802 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2802 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2802 : Upper (D 10) (R 10) [18,36,72,33] 13 := by
  apply FastRouting.sound _ _ [18,36,72,33] 13 (by decide) (choices 2) [96,160,192,384] r2802 c2802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2802_96
  · exact m2802_160
  · exact m2802_192
  · exact m2802_384

theorem m2803_96 : Upper (D 10) (R 10) [18,36,72,129,96] 13 :=
  permutation_upper _ _ _ [6,40,96,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1353

theorem m2803_160 : Upper (D 10) (R 10) [18,36,72,129,160] 13 :=
  permutation_upper _ _ _ [6,40,96,144,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1365

theorem m2803_192 : Upper (D 10) (R 10) [18,36,72,129,192] 13 :=
  permutation_upper _ _ _ [6,40,192,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1404

theorem m2803_288 : Upper (D 10) (R 10) [18,36,72,129,288] 13 :=
  permutation_upper _ _ _ [6,40,96,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1370

theorem m2803_320 : Upper (D 10) (R 10) [18,36,72,129,320] 13 :=
  permutation_upper _ _ _ [6,40,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1406

theorem m2803_384 : Upper (D 10) (R 10) [18,36,72,129,384] 13 :=
  permutation_upper _ _ _ [6,40,192,272,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1422

def r2803 : Route 9 := (fun mask => (mask,id))

def c2803 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2803 : Upper (D 10) (R 10) [18,36,72,129] 13 := by
  apply FastRouting.sound _ _ [18,36,72,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2803 c2803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2803_96
  · exact m2803_160
  · exact m2803_192
  · exact m2803_288
  · exact m2803_320
  · exact m2803_384

theorem m2804_33 : Upper (D 10) (R 10) [18,36,72,160,33] 13 :=
  permutation_upper _ _ _ [6,33,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1207

theorem m2804_65 : Upper (D 10) (R 10) [18,36,72,160,65] 13 :=
  permutation_upper _ _ _ [6,40,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1292

theorem m2804_96 : Upper (D 10) (R 10) [18,36,72,160,96] 13 :=
  permutation_upper _ _ _ [6,40,96,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1354

theorem m2804_129 : Upper (D 10) (R 10) [18,36,72,160,129] 13 :=
  permutation_upper _ _ _ [6,40,65,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1296

theorem m2804_160 : Upper (D 10) (R 10) [18,36,72,160,160] 13 :=
  permutation_upper _ _ _ [6,40,96,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1366

theorem m2804_192 : Upper (D 10) (R 10) [18,36,72,160,192] 13 :=
  permutation_upper _ _ _ [6,40,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1405

theorem m2804_257 : Upper (D 10) (R 10) [18,36,72,160,257] 13 :=
  permutation_upper _ _ _ [6,40,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1299

theorem m2804_288 : Upper (D 10) (R 10) [18,36,72,160,288] 13 :=
  permutation_upper _ _ _ [6,40,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1371

theorem m2804_320 : Upper (D 10) (R 10) [18,36,72,160,320] 13 :=
  permutation_upper _ _ _ [6,40,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1407

theorem m2804_384 : Upper (D 10) (R 10) [18,36,72,160,384] 13 :=
  permutation_upper _ _ _ [6,40,192,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1423

def r2804 : Route 9 := (fun mask => (mask,id))

def c2804 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2804 : Upper (D 10) (R 10) [18,36,72,160] 13 := by
  apply FastRouting.sound _ _ [18,36,72,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2804 c2804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2804_33
  · exact m2804_65
  · exact m2804_96
  · exact m2804_129
  · exact m2804_160
  · exact m2804_192
  · exact m2804_257
  · exact m2804_288
  · exact m2804_320
  · exact m2804_384

theorem m2805_33 : Upper (D 10) (R 10) [18,36,72,384,33] 13 :=
  permutation_upper _ _ _ [6,33,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1208

theorem m2805_65 : Upper (D 10) (R 10) [18,36,72,384,65] 13 :=
  permutation_upper _ _ _ [6,40,65,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1293

theorem m2805_96 : Upper (D 10) (R 10) [18,36,72,384,96] 13 :=
  permutation_upper _ _ _ [6,40,96,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1355

theorem m2805_129 : Upper (D 10) (R 10) [18,36,72,384,129] 13 :=
  permutation_upper _ _ _ [6,40,65,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1300

theorem m2805_160 : Upper (D 10) (R 10) [18,36,72,384,160] 13 :=
  permutation_upper _ _ _ [6,40,96,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1372

theorem m2805_192 : Upper (D 10) (R 10) [18,36,72,384,192] 13 :=
  permutation_upper _ _ _ [6,40,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1408

theorem m2805_384 : Upper (D 10) (R 10) [18,36,72,384,384] 13 :=
  permutation_upper _ _ _ [6,40,192,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1424

def r2805 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2805 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2805 : Upper (D 10) (R 10) [18,36,72,384] 13 := by
  apply FastRouting.sound _ _ [18,36,72,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r2805 c2805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2805_33
  · exact m2805_65
  · exact m2805_96
  · exact m2805_129
  · exact m2805_160
  · exact m2805_192
  · exact m2805_384

def b2806 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 100 41 472 488 456 456 456), lower := (rows 19 38 100 41 16 32 64 128 256), losses := [] }

theorem u2806 : Upper (D 10) (R 10) [18,36,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2806 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2807 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 100 73 440 424 488 424 424), lower := (rows 19 38 100 73 16 32 64 128 256), losses := [] }

theorem u2807 : Upper (D 10) (R 10) [18,36,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2807 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2808 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 100 137 504 488 488 488 488), lower := (rows 19 38 100 137 16 32 64 128 256), losses := [] }

theorem u2808 : Upper (D 10) (R 10) [18,36,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2808 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 457, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 100 168 473 489 457 457 457), lower := (rows 19 38 100 168 16 32 64 128 256), losses := [] }

theorem u2809 : Upper (D 10) (R 10) [18,36,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2809 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 425, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 100 200 441 425 489 425 425), lower := (rows 19 38 100 200 16 32 64 128 256), losses := [] }

theorem u2810 : Upper (D 10) (R 10) [18,36,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2810 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 489, camps := [{ cop := 2, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 19 38 100 392 505 489 489 489 489), lower := (rows 19 38 100 392 16 32 64 128 256), losses := [] }

theorem u2811 : Upper (D 10) (R 10) [18,36,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2811 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2812_40 : Upper (D 10) (R 10) [18,36,192,33,40] 13 :=
  permutation_upper _ _ _ [6,40,48,33,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1281

theorem m2812_72 : Upper (D 10) (R 10) [18,36,192,33,72] 13 :=
  permutation_upper _ _ _ [6,40,80,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1332

theorem m2812_96 : Upper (D 10) (R 10) [18,36,192,33,96] 13 :=
  permutation_upper _ _ _ [6,40,96,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1379

theorem m2812_192 : Upper (D 10) (R 10) [18,36,192,33,192] 13 :=
  permutation_upper _ _ _ [6,40,192,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1414

theorem m2812_264 : Upper (D 10) (R 10) [18,36,192,33,264] 13 :=
  permutation_upper _ _ _ [6,40,80,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1338

theorem m2812_288 : Upper (D 10) (R 10) [18,36,192,33,288] 13 :=
  permutation_upper _ _ _ [6,40,96,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1385

theorem m2812_320 : Upper (D 10) (R 10) [18,36,192,33,320] 13 :=
  permutation_upper _ _ _ [6,40,192,320,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1433

def r2812 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2812 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2812 : Upper (D 10) (R 10) [18,36,192,33] 13 := by
  apply FastRouting.sound _ _ [18,36,192,33] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r2812 c2812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2812_40
  · exact m2812_72
  · exact m2812_96
  · exact m2812_192
  · exact m2812_264
  · exact m2812_288
  · exact m2812_320

theorem m2813_40 : Upper (D 10) (R 10) [18,36,192,65,40] 13 :=
  permutation_upper _ _ _ [6,40,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1284

theorem m2813_136 : Upper (D 10) (R 10) [18,36,192,65,136] 13 :=
  permutation_upper _ _ _ [6,40,80,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1333

theorem m2813_160 : Upper (D 10) (R 10) [18,36,192,65,160] 13 :=
  permutation_upper _ _ _ [6,40,96,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1380

theorem m2813_264 : Upper (D 10) (R 10) [18,36,192,65,264] 13 :=
  permutation_upper _ _ _ [6,40,80,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1341

theorem m2813_288 : Upper (D 10) (R 10) [18,36,192,65,288] 13 :=
  permutation_upper _ _ _ [6,40,96,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1388

theorem m2813_384 : Upper (D 10) (R 10) [18,36,192,65,384] 13 :=
  permutation_upper _ _ _ [6,40,192,320,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1436

def r2813 : Route 9 := (fun mask => (mask,id))

def c2813 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2813 : Upper (D 10) (R 10) [18,36,192,65] 13 := by
  apply FastRouting.sound _ _ [18,36,192,65] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2813 c2813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2813_40
  · exact m2813_136
  · exact m2813_160
  · exact m2813_264
  · exact m2813_288
  · exact m2813_384

theorem m2814_9 : Upper (D 10) (R 10) [18,36,192,96,9] 13 :=
  permutation_upper _ _ _ [6,9,48,96,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1115

theorem m2814_33 : Upper (D 10) (R 10) [18,36,192,96,33] 13 :=
  permutation_upper _ _ _ [6,33,40,192,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1211

theorem m2814_40 : Upper (D 10) (R 10) [18,36,192,96,40] 13 :=
  permutation_upper _ _ _ [6,40,48,96,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1286

theorem m2814_129 : Upper (D 10) (R 10) [18,36,192,96,129] 13 :=
  permutation_upper _ _ _ [6,40,65,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1305

theorem m2814_136 : Upper (D 10) (R 10) [18,36,192,96,136] 13 :=
  permutation_upper _ _ _ [6,40,80,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1334

theorem m2814_160 : Upper (D 10) (R 10) [18,36,192,96,160] 13 :=
  permutation_upper _ _ _ [6,40,96,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1381

theorem m2814_257 : Upper (D 10) (R 10) [18,36,192,96,257] 13 :=
  permutation_upper _ _ _ [6,40,65,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1309

theorem m2814_264 : Upper (D 10) (R 10) [18,36,192,96,264] 13 :=
  permutation_upper _ _ _ [6,40,80,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1342

theorem m2814_288 : Upper (D 10) (R 10) [18,36,192,96,288] 13 :=
  permutation_upper _ _ _ [6,40,96,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1389

theorem m2814_384 : Upper (D 10) (R 10) [18,36,192,96,384] 13 :=
  permutation_upper _ _ _ [6,40,192,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1437

def r2814 : Route 9 := (fun mask => (mask,id))

def c2814 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2814 : Upper (D 10) (R 10) [18,36,192,96] 13 := by
  apply FastRouting.sound _ _ [18,36,192,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2814 c2814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2814_9
  · exact m2814_33
  · exact m2814_40
  · exact m2814_129
  · exact m2814_136
  · exact m2814_160
  · exact m2814_257
  · exact m2814_264
  · exact m2814_288
  · exact m2814_384

theorem m2815_40 : Upper (D 10) (R 10) [18,36,192,257,40] 13 :=
  permutation_upper _ _ _ [6,40,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1285

theorem m2815_72 : Upper (D 10) (R 10) [18,36,192,257,72] 13 :=
  permutation_upper _ _ _ [6,40,80,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1335

theorem m2815_96 : Upper (D 10) (R 10) [18,36,192,257,96] 13 :=
  permutation_upper _ _ _ [6,40,96,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1382

theorem m2815_192 : Upper (D 10) (R 10) [18,36,192,257,192] 13 :=
  permutation_upper _ _ _ [6,40,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1415

theorem m2815_264 : Upper (D 10) (R 10) [18,36,192,257,264] 13 :=
  permutation_upper _ _ _ [6,40,80,384,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1339

theorem m2815_288 : Upper (D 10) (R 10) [18,36,192,257,288] 13 :=
  permutation_upper _ _ _ [6,40,96,384,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1386

theorem m2815_320 : Upper (D 10) (R 10) [18,36,192,257,320] 13 :=
  permutation_upper _ _ _ [6,40,192,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1434

def r2815 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2815 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2815 : Upper (D 10) (R 10) [18,36,192,257] 13 := by
  apply FastRouting.sound _ _ [18,36,192,257] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r2815 c2815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2815_40
  · exact m2815_72
  · exact m2815_96
  · exact m2815_192
  · exact m2815_264
  · exact m2815_288
  · exact m2815_320

theorem m2816_9 : Upper (D 10) (R 10) [18,36,192,288,9] 13 :=
  permutation_upper _ _ _ [6,9,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1116

theorem m2816_33 : Upper (D 10) (R 10) [18,36,192,288,33] 13 :=
  permutation_upper _ _ _ [6,33,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1212

theorem m2816_40 : Upper (D 10) (R 10) [18,36,192,288,40] 13 :=
  permutation_upper _ _ _ [6,40,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1287

theorem m2816_65 : Upper (D 10) (R 10) [18,36,192,288,65] 13 :=
  permutation_upper _ _ _ [6,40,65,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1306

theorem m2816_72 : Upper (D 10) (R 10) [18,36,192,288,72] 13 :=
  permutation_upper _ _ _ [6,40,80,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1336

theorem m2816_96 : Upper (D 10) (R 10) [18,36,192,288,96] 13 :=
  permutation_upper _ _ _ [6,40,96,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1383

theorem m2816_192 : Upper (D 10) (R 10) [18,36,192,288,192] 13 :=
  permutation_upper _ _ _ [6,40,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1416

theorem m2816_257 : Upper (D 10) (R 10) [18,36,192,288,257] 13 :=
  permutation_upper _ _ _ [6,40,65,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1308

theorem m2816_264 : Upper (D 10) (R 10) [18,36,192,288,264] 13 :=
  permutation_upper _ _ _ [6,40,80,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1340

theorem m2816_288 : Upper (D 10) (R 10) [18,36,192,288,288] 13 :=
  permutation_upper _ _ _ [6,40,96,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1387

theorem m2816_320 : Upper (D 10) (R 10) [18,36,192,288,320] 13 :=
  permutation_upper _ _ _ [6,40,192,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1435

def r2816 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2816 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2816 : Upper (D 10) (R 10) [18,36,192,288] 13 := by
  apply FastRouting.sound _ _ [18,36,192,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r2816 c2816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2816_9
  · exact m2816_33
  · exact m2816_40
  · exact m2816_65
  · exact m2816_72
  · exact m2816_96
  · exact m2816_192
  · exact m2816_257
  · exact m2816_264
  · exact m2816_288
  · exact m2816_320

theorem m2817_9 : Upper (D 10) (R 10) [18,36,192,320,9] 13 :=
  permutation_upper _ _ _ [6,9,48,192,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1120

theorem m2817_33 : Upper (D 10) (R 10) [18,36,192,320,33] 13 :=
  permutation_upper _ _ _ [6,33,40,192,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1213

theorem m2817_40 : Upper (D 10) (R 10) [18,36,192,320,40] 13 :=
  permutation_upper _ _ _ [6,40,48,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1289

theorem m2817_129 : Upper (D 10) (R 10) [18,36,192,320,129] 13 :=
  permutation_upper _ _ _ [6,40,65,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1307

theorem m2817_136 : Upper (D 10) (R 10) [18,36,192,320,136] 13 :=
  permutation_upper _ _ _ [6,40,80,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1337

theorem m2817_160 : Upper (D 10) (R 10) [18,36,192,320,160] 13 :=
  permutation_upper _ _ _ [6,40,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1384

theorem m2817_257 : Upper (D 10) (R 10) [18,36,192,320,257] 13 :=
  permutation_upper _ _ _ [6,40,65,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1310

theorem m2817_264 : Upper (D 10) (R 10) [18,36,192,320,264] 13 :=
  permutation_upper _ _ _ [6,40,80,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1343

theorem m2817_288 : Upper (D 10) (R 10) [18,36,192,320,288] 13 :=
  permutation_upper _ _ _ [6,40,96,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1390

theorem m2817_384 : Upper (D 10) (R 10) [18,36,192,320,384] 13 :=
  permutation_upper _ _ _ [6,40,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1438

def r2817 : Route 9 := (fun mask => (mask,id))

def c2817 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2817 : Upper (D 10) (R 10) [18,36,192,320] 13 := by
  apply FastRouting.sound _ _ [18,36,192,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2817 c2817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2817_9
  · exact m2817_33
  · exact m2817_40
  · exact m2817_129
  · exact m2817_136
  · exact m2817_160
  · exact m2817_257
  · exact m2817_264
  · exact m2817_288
  · exact m2817_384

def b2818 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 19 67 44 76 432 416 480 416 416), lower := (rows 19 67 44 76 16 32 64 128 256), losses := [] }

theorem u2818 : Upper (D 10) (R 10) [18,65,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2818 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2819_96 : Upper (D 10) (R 10) [18,65,40,132,96] 13 :=
  permutation_upper _ _ _ [6,65,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1444

theorem m2819_160 : Upper (D 10) (R 10) [18,65,40,132,160] 13 :=
  permutation_upper _ _ _ [6,65,160,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1484

theorem m2819_192 : Upper (D 10) (R 10) [18,65,40,132,192] 13 :=
  permutation_upper _ _ _ [6,65,192,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1514

theorem m2819_288 : Upper (D 10) (R 10) [18,65,40,132,288] 13 :=
  permutation_upper _ _ _ [6,65,160,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1487

theorem m2819_320 : Upper (D 10) (R 10) [18,65,40,132,320] 13 :=
  permutation_upper _ _ _ [6,65,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1515

theorem m2819_384 : Upper (D 10) (R 10) [18,65,40,132,384] 13 :=
  permutation_upper _ _ _ [6,65,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1525

def r2819 : Route 9 := (fun mask => (mask,id))

def c2819 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2819 : Upper (D 10) (R 10) [18,65,40,132] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2819 c2819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2819_96
  · exact m2819_160
  · exact m2819_192
  · exact m2819_288
  · exact m2819_320
  · exact m2819_384

#print axioms u2819
end Delivery.IrregularNine14.P10
