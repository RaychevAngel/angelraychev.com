import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0301
import IrregularNine14P08C0302
import IrregularNine14P08C0303
import IrregularNine14P08C0307
import IrregularNine14P08C0310
import IrregularNine14P08C0311
import IrregularNine14P08C0312
import IrregularNine14P08C0313
import IrregularNine14P08C0314
import IrregularNine14P08C0315
import IrregularNine14P08C0316
import IrregularNine14P08C0317
import IrregularNine14P08C0318

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23820 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 98 140 152 55 39 103 167 295), lower := (rows 321 98 140 152 16 32 64 128 256), losses := [] }

theorem u23820 : Upper (D 8) (R 8) [320,96,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23821 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 98 140 168 55 55 119 183 311), lower := (rows 321 98 140 168 16 32 64 128 256), losses := [] }

theorem u23821 : Upper (D 8) (R 8) [320,96,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23822_3 : Upper (D 8) (R 8) [320,96,144,160,3] 13 :=
  permutation_upper _ _ _ [320,5,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18082

theorem m23822_5 : Upper (D 8) (R 8) [320,96,144,160,5] 13 :=
  permutation_upper _ _ _ [320,5,130,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18124

theorem m23822_6 : Upper (D 8) (R 8) [320,96,144,160,6] 13 :=
  permutation_upper _ _ _ [320,12,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18438

theorem m23822_9 : Upper (D 8) (R 8) [320,96,144,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18231

theorem m23822_10 : Upper (D 8) (R 8) [320,96,144,160,10] 13 :=
  permutation_upper _ _ _ [320,12,96,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18447

theorem m23822_12 : Upper (D 8) (R 8) [320,96,144,160,12] 13 :=
  permutation_upper _ _ _ [320,12,130,160,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18467

theorem m23822_33 : Upper (D 8) (R 8) [320,96,144,160,33] 13 :=
  permutation_upper _ _ _ [320,33,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18625

theorem m23822_34 : Upper (D 8) (R 8) [320,96,144,160,34] 13 :=
  permutation_upper _ _ _ [320,36,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18697

theorem m23822_36 : Upper (D 8) (R 8) [320,96,144,160,36] 13 :=
  permutation_upper _ _ _ [320,36,130,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18724

theorem m23822_40 : Upper (D 8) (R 8) [320,96,144,160,40] 13 :=
  permutation_upper _ _ _ [320,36,160,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18753

def r23822 : Route 9 := (fun mask => (mask,id))

def c23822 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23822 : Upper (D 8) (R 8) [320,96,144,160] 13 := by
  apply FastRouting.sound _ _ [320,96,144,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r23822 c23822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23822_3
  · exact m23822_5
  · exact m23822_6
  · exact m23822_9
  · exact m23822_10
  · exact m23822_12
  · exact m23822_33
  · exact m23822_34
  · exact m23822_36
  · exact m23822_40

def b23823 : PairBound 9 := { available := 31, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 98 164 168 31 63 95 159 287), lower := (rows 321 98 164 168 16 32 64 128 256), losses := [] }

theorem u23823 : Upper (D 8) (R 8) [320,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23824 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 488 496 480 480 480 480), lower := (rows 7 11 21 8 16 32 64 128 256), losses := [] }

theorem u23824 : Upper (D 8) (R 8) [6,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23825 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 504 496 496 496 496 496), lower := (rows 7 11 37 8 16 32 64 128 256), losses := [] }

theorem u23825 : Upper (D 8) (R 8) [6,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23826 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23826 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23826 : Upper (D 8) (R 8) [6,9,48] 13 := by
  apply FastRouting.sound _ _ [6,9,48] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r23826 c23826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18755
  · exact u18756
  · exact u18757
  · exact u18758
  · exact u18759
  · exact u18760
  · exact u18761

def b23827 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 69 504 496 496 496 496 496), lower := (rows 7 11 69 8 16 32 64 128 256), losses := [] }

theorem u23827 : Upper (D 8) (R 8) [6,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23828 : Route 9 := (fun mask => (mask,id))

def c23828 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23828 : Upper (D 8) (R 8) [6,9,80] 13 := by
  apply FastRouting.sound _ _ [6,9,80] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r23828 c23828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18762
  · exact u18763
  · exact u18764
  · exact u18765
  · exact u18766
  · exact u18767
  · exact u18768
  · exact u18769
  · exact u18770
  · exact u18771

def r23829 : Route 9 := (fun mask => (mask,id))

def c23829 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23829 : Upper (D 8) (R 8) [6,9,96] 13 := by
  apply FastRouting.sound _ _ [6,9,96] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23829 c23829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18772
  · exact u18773
  · exact u18774
  · exact u18775
  · exact u18776
  · exact u18777
  · exact u18778
  · exact u18779
  · exact u18780
  · exact u18781
  · exact u18782
  · exact u18783
  · exact u18784
  · exact u18785
  · exact u18786

def r23830 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23830 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23830 : Upper (D 8) (R 8) [6,9,192] 13 := by
  apply FastRouting.sound _ _ [6,9,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r23830 c23830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18787
  · exact u18788
  · exact u18789
  · exact u18790
  · exact u18791
  · exact u18792
  · exact u18793
  · exact u18794
  · exact u18795
  · exact u18796
  · exact u18797

def b23831 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 261 248 240 240 240 240 496), lower := (rows 7 11 261 8 16 32 64 128 256), losses := [] }

theorem u23831 : Upper (D 8) (R 8) [6,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23832 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23832 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23832 : Upper (D 8) (R 8) [6,9,272] 13 := by
  apply FastRouting.sound _ _ [6,9,272] 13 (by decide) (choices 2) [33,65,96,192] r23832 c23832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18798
  · exact u18799
  · exact u18800
  · exact u18801

def r23833 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23833 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23833 : Upper (D 8) (R 8) [6,9,288] 13 := by
  apply FastRouting.sound _ _ [6,9,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23833 c23833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18802
  · exact u18803
  · exact u18804
  · exact u18805
  · exact u18806
  · exact u18807
  · exact u18808

def r23834 : Route 9 := (fun mask => (mask,id))

def c23834 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23834 : Upper (D 8) (R 8) [6,9,320] 13 := by
  apply FastRouting.sound _ _ [6,9,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23834 c23834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18809
  · exact u18810
  · exact u18811
  · exact u18812
  · exact u18813
  · exact u18814
  · exact u18815
  · exact u18816
  · exact u18817
  · exact u18818

def r23835 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23835 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23835 : Upper (D 8) (R 8) [6,24,33] 13 := by
  apply FastRouting.sound _ _ [6,24,33] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r23835 c23835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18819
  · exact u18820
  · exact u18821
  · exact u18822
  · exact u18823
  · exact u18824
  · exact u18825

def r23836 : Route 9 := (fun mask => (mask,id))

def c23836 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23836 : Upper (D 8) (R 8) [6,24,65] 13 := by
  apply FastRouting.sound _ _ [6,24,65] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r23836 c23836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18826
  · exact u18827
  · exact u18828
  · exact u18829
  · exact u18830
  · exact u18831
  · exact u18832
  · exact u18833
  · exact u18834
  · exact u18835

def r23837 : Route 9 := (fun mask => (mask,id))

def c23837 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23837 : Upper (D 8) (R 8) [6,24,96] 13 := by
  apply FastRouting.sound _ _ [6,24,96] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r23837 c23837
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18836
  · exact u18837
  · exact u18838
  · exact u18839
  · exact u18840
  · exact u18841
  · exact u18842
  · exact u18843
  · exact u18844
  · exact u18845

def r23838 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23838 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23838 : Upper (D 8) (R 8) [6,24,192] 13 := by
  apply FastRouting.sound _ _ [6,24,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r23838 c23838
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18846
  · exact u18847
  · exact u18848
  · exact u18849
  · exact u18850
  · exact u18851
  · exact u18852

def r23839 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23839 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23839 : Upper (D 8) (R 8) [6,24,257] 13 := by
  apply FastRouting.sound _ _ [6,24,257] 13 (by decide) (choices 2) [33,65,96,192] r23839 c23839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18853
  · exact u18854
  · exact u18855
  · exact u18856

def r23840 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23840 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23840 : Upper (D 8) (R 8) [6,24,288] 13 := by
  apply FastRouting.sound _ _ [6,24,288] 13 (by decide) (choices 2) [33,65,96,192] r23840 c23840
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18857
  · exact u18858
  · exact u18859
  · exact u18860

def r23841 : Route 9 := (fun mask => (mask,id))

def c23841 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23841 : Upper (D 8) (R 8) [6,24,320] 13 := by
  apply FastRouting.sound _ _ [6,24,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23841 c23841
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18861
  · exact u18862
  · exact u18863
  · exact u18864
  · exact u18865
  · exact u18866

def b23842 : PairBound 9 := { available := 504, camps := [{ cop := 5, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 37 504 504 504 504 504 504), lower := (rows 7 35 37 8 16 32 64 128 256), losses := [] }

theorem u23842 : Upper (D 8) (R 8) [6,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23843 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 44 505 497 497 497 497 497), lower := (rows 7 35 44 8 16 32 64 128 256), losses := [] }

theorem u23843 : Upper (D 8) (R 8) [6,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23844 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 504 504 504 504 504 504), lower := (rows 7 35 69 8 16 32 64 128 256), losses := [] }

theorem u23844 : Upper (D 8) (R 8) [6,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23845 : Route 9 := (fun mask => (mask,id))

def c23845 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23845 : Upper (D 8) (R 8) [6,33,72] 13 := by
  apply FastRouting.sound _ _ [6,33,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23845 c23845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18867
  · exact u18868
  · exact u18869
  · exact u18870
  · exact u18871
  · exact u18872
  · exact u18873
  · exact u18874
  · exact u18875
  · exact u18876
  · exact u18877
  · exact u18878
  · exact u18879
  · exact u18880
  · exact u18881

def b23846 : PairBound 9 := { available := 505, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 100 505 505 505 505 505 505), lower := (rows 7 35 100 8 16 32 64 128 256), losses := [] }

theorem u23846 : Upper (D 8) (R 8) [6,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23847 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23847 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23847 : Upper (D 8) (R 8) [6,33,192] 13 := by
  apply FastRouting.sound _ _ [6,33,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r23847 c23847
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18882
  · exact u18883
  · exact u18884
  · exact u18885
  · exact u18886
  · exact u18887
  · exact u18888
  · exact u18889
  · exact u18890
  · exact u18891
  · exact u18892

def b23848 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 261 248 248 248 248 248 504), lower := (rows 7 35 261 8 16 32 64 128 256), losses := [] }

theorem u23848 : Upper (D 8) (R 8) [6,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23849 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23849 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23849 : Upper (D 8) (R 8) [6,33,264] 13 := by
  apply FastRouting.sound _ _ [6,33,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23849 c23849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18893
  · exact u18894
  · exact u18895
  · exact u18896
  · exact u18897
  · exact u18898
  · exact u18899

def b23850 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 292 249 249 249 249 249 505), lower := (rows 7 35 292 8 16 32 64 128 256), losses := [] }

theorem u23850 : Upper (D 8) (R 8) [6,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23851 : Route 9 := (fun mask => (mask,id))

def c23851 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23851 : Upper (D 8) (R 8) [6,33,320] 13 := by
  apply FastRouting.sound _ _ [6,33,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23851 c23851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18900
  · exact u18901
  · exact u18902
  · exact u18903
  · exact u18904
  · exact u18905
  · exact u18906
  · exact u18907
  · exact u18908
  · exact u18909

def r23852 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23852 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23852 : Upper (D 8) (R 8) [6,40,48] 13 := by
  apply FastRouting.sound _ _ [6,40,48] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r23852 c23852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18910
  · exact u18911
  · exact u18912
  · exact u18913
  · exact u18914
  · exact u18915
  · exact u18916

def r23853 : Route 9 := (fun mask => (mask,id))

def c23853 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23853 : Upper (D 8) (R 8) [6,40,65] 13 := by
  apply FastRouting.sound _ _ [6,40,65] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23853 c23853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18917
  · exact u18918
  · exact u18919
  · exact u18920
  · exact u18921
  · exact u18922
  · exact u18923
  · exact u18924
  · exact u18925
  · exact u18926
  · exact u18927
  · exact u18928
  · exact u18929
  · exact u18930
  · exact u18931

def r23854 : Route 9 := (fun mask => (mask,id))

def c23854 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23854 : Upper (D 8) (R 8) [6,40,80] 13 := by
  apply FastRouting.sound _ _ [6,40,80] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r23854 c23854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18932
  · exact u18933
  · exact u18934
  · exact u18935
  · exact u18936
  · exact u18937
  · exact u18938
  · exact u18939
  · exact u18940
  · exact u18941

def r23855 : Route 9 := (fun mask => (mask,id))

def c23855 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23855 : Upper (D 8) (R 8) [6,40,96] 13 := by
  apply FastRouting.sound _ _ [6,40,96] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23855 c23855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18942
  · exact u18943
  · exact u18944
  · exact u18945
  · exact u18946
  · exact u18947
  · exact u18948
  · exact u18949
  · exact u18950
  · exact u18951
  · exact u18952
  · exact u18953
  · exact u18954
  · exact u18955
  · exact u18956

def r23856 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23856 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23856 : Upper (D 8) (R 8) [6,40,192] 13 := by
  apply FastRouting.sound _ _ [6,40,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r23856 c23856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18957
  · exact u18958
  · exact u18959
  · exact u18960
  · exact u18961
  · exact u18962
  · exact u18963
  · exact u18964
  · exact u18965
  · exact u18966
  · exact u18967

def r23857 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23857 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23857 : Upper (D 8) (R 8) [6,40,257] 13 := by
  apply FastRouting.sound _ _ [6,40,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23857 c23857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18968
  · exact u18969
  · exact u18970
  · exact u18971
  · exact u18972
  · exact u18973
  · exact u18974

def r23858 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23858 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23858 : Upper (D 8) (R 8) [6,40,272] 13 := by
  apply FastRouting.sound _ _ [6,40,272] 13 (by decide) (choices 2) [33,65,96,192] r23858 c23858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18975
  · exact u18976
  · exact u18977
  · exact u18978

def r23859 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23859 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23859 : Upper (D 8) (R 8) [6,40,288] 13 := by
  apply FastRouting.sound _ _ [6,40,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23859 c23859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18979
  · exact u18980
  · exact u18981
  · exact u18982
  · exact u18983
  · exact u18984
  · exact u18985

def r23860 : Route 9 := (fun mask => (mask,id))

def c23860 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23860 : Upper (D 8) (R 8) [6,40,320] 13 := by
  apply FastRouting.sound _ _ [6,40,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23860 c23860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18986
  · exact u18987
  · exact u18988
  · exact u18989
  · exact u18990
  · exact u18991
  · exact u18992
  · exact u18993
  · exact u18994
  · exact u18995

def b23861 : PairBound 9 := { available := 440, camps := [{ cop := 6, region := 7, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 69 440 440 440 504 440 440), lower := (rows 7 67 69 8 16 32 64 128 256), losses := [] }

theorem u23861 : Upper (D 8) (R 8) [6,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23862 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 76 441 433 433 497 433 433), lower := (rows 7 67 76 8 16 32 64 128 256), losses := [] }

theorem u23862 : Upper (D 8) (R 8) [6,65,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23863 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 100 441 441 441 505 441 441), lower := (rows 7 67 100 8 16 32 64 128 256), losses := [] }

theorem u23863 : Upper (D 8) (R 8) [6,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23864 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 133 504 504 504 504 504 504), lower := (rows 7 67 133 8 16 32 64 128 256), losses := [] }

theorem u23864 : Upper (D 8) (R 8) [6,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23865 : Route 9 := (fun mask => (mask,id))

def c23865 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23865 : Upper (D 8) (R 8) [6,65,136] 13 := by
  apply FastRouting.sound _ _ [6,65,136] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23865 c23865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18996
  · exact u18997
  · exact u18998
  · exact u18999
  · exact u19000
  · exact u19001
  · exact u19002
  · exact u19003
  · exact u19004
  · exact u19005
  · exact u19006
  · exact u19007
  · exact u19008
  · exact u19009
  · exact u19010

def r23866 : Route 9 := (fun mask => (mask,id))

def c23866 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23866 : Upper (D 8) (R 8) [6,65,160] 13 := by
  apply FastRouting.sound _ _ [6,65,160] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23866 c23866
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19011
  · exact u19012
  · exact u19013
  · exact u19014
  · exact u19015
  · exact u19016
  · exact u19017
  · exact u19018
  · exact u19019
  · exact u19020
  · exact u19021
  · exact u19022
  · exact u19023
  · exact u19024
  · exact u19025

def b23867 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 196 441 441 441 505 441 441), lower := (rows 7 67 196 8 16 32 64 128 256), losses := [] }

theorem u23867 : Upper (D 8) (R 8) [6,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23868 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 261 248 248 248 248 248 504), lower := (rows 7 67 261 8 16 32 64 128 256), losses := [] }

theorem u23868 : Upper (D 8) (R 8) [6,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23869 : Route 9 := (fun mask => (mask,id))

def c23869 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23869 : Upper (D 8) (R 8) [6,65,264] 13 := by
  apply FastRouting.sound _ _ [6,65,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23869 c23869
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19026
  · exact u19027
  · exact u19028
  · exact u19029
  · exact u19030
  · exact u19031
  · exact u19032
  · exact u19033
  · exact u19034
  · exact u19035

def r23870 : Route 9 := (fun mask => (mask,id))

def c23870 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23870 : Upper (D 8) (R 8) [6,65,288] 13 := by
  apply FastRouting.sound _ _ [6,65,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23870 c23870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19036
  · exact u19037
  · exact u19038
  · exact u19039
  · exact u19040
  · exact u19041
  · exact u19042
  · exact u19043
  · exact u19044
  · exact u19045

def b23871 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 324 185 185 185 249 185 441), lower := (rows 7 67 324 8 16 32 64 128 256), losses := [] }

theorem u23871 : Upper (D 8) (R 8) [6,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23872 : Route 9 := (fun mask => (mask,id))

def c23872 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23872 : Upper (D 8) (R 8) [6,65,384] 13 := by
  apply FastRouting.sound _ _ [6,65,384] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23872 c23872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19046
  · exact u19047
  · exact u19048
  · exact u19049
  · exact u19050
  · exact u19051
  · exact u19052
  · exact u19053
  · exact u19054
  · exact u19055

def b23873 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 84 425 433 417 481 417 417), lower := (rows 7 74 84 8 16 32 64 128 256), losses := [] }

theorem u23873 : Upper (D 8) (R 8) [6,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23874 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 100 441 433 433 497 433 433), lower := (rows 7 74 100 8 16 32 64 128 256), losses := [] }

theorem u23874 : Upper (D 8) (R 8) [6,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23875 : Route 9 := (fun mask => (mask,id))

def c23875 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23875 : Upper (D 8) (R 8) [6,72,144] 13 := by
  apply FastRouting.sound _ _ [6,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r23875 c23875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19056
  · exact u19057
  · exact u19058
  · exact u19059
  · exact u19060
  · exact u19061
  · exact u19062
  · exact u19063
  · exact u19064
  · exact u19065

def r23876 : Route 9 := (fun mask => (mask,id))

def c23876 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23876 : Upper (D 8) (R 8) [6,72,160] 13 := by
  apply FastRouting.sound _ _ [6,72,160] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23876 c23876
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19066
  · exact u19067
  · exact u19068
  · exact u19069
  · exact u19070
  · exact u19071
  · exact u19072
  · exact u19073
  · exact u19074
  · exact u19075
  · exact u19076
  · exact u19077
  · exact u19078
  · exact u19079
  · exact u19080

def b23877 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 196 441 433 433 497 433 433), lower := (rows 7 74 196 8 16 32 64 128 256), losses := [] }

theorem u23877 : Upper (D 8) (R 8) [6,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23878 : Route 9 := (fun mask => (mask,id))

def c23878 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23878 : Upper (D 8) (R 8) [6,72,257] 13 := by
  apply FastRouting.sound _ _ [6,72,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23878 c23878
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19081
  · exact u19082
  · exact u19083
  · exact u19084
  · exact u19085
  · exact u19086
  · exact u19087
  · exact u19088
  · exact u19089
  · exact u19090

def r23879 : Route 9 := (fun mask => (mask,id))

def c23879 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23879 : Upper (D 8) (R 8) [6,72,272] 13 := by
  apply FastRouting.sound _ _ [6,72,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23879 c23879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19091
  · exact u19092
  · exact u19093
  · exact u19094
  · exact u19095
  · exact u19096

#print axioms u23879
end Delivery.IrregularNine14.P08
