import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0166
import IrregularNine14P08C0167
import IrregularNine14P08C0168
import IrregularNine14P08C0169

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m19860_9 : Upper (D 8) (R 8) [66,5,160,80,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10000

theorem m19860_33 : Upper (D 8) (R 8) [66,5,160,80,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10009

theorem m19860_40 : Upper (D 8) (R 8) [66,5,160,80,40] 13 :=
  permutation_upper _ _ _ [66,5,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10019

def r19860 : Route 9 := (fun mask => (mask,id))

def c19860 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19860 : Upper (D 8) (R 8) [66,5,160,80] 13 := by
  apply FastRouting.sound _ _ [66,5,160,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19860 c19860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19860_9
  · exact m19860_33
  · exact m19860_40
  · exact u10034
  · exact u10035
  · exact u10036
  · exact u10037
  · exact u10038
  · exact u10039
  · exact u10040

theorem m19861_9 : Upper (D 8) (R 8) [66,5,160,96,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10001

theorem m19861_33 : Upper (D 8) (R 8) [66,5,160,96,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10010

theorem m19861_40 : Upper (D 8) (R 8) [66,5,160,96,40] 13 :=
  permutation_upper _ _ _ [66,5,160,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10020

def r19861 : Route 9 := (fun mask => (mask,id))

def c19861 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19861 : Upper (D 8) (R 8) [66,5,160,96] 13 := by
  apply FastRouting.sound _ _ [66,5,160,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19861 c19861
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19861_9
  · exact m19861_33
  · exact m19861_40
  · exact u10041
  · exact u10042
  · exact u10043
  · exact u10044
  · exact u10045
  · exact u10046
  · exact u10047

def b19862 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 137 376 376 376 504 376), lower := (rows 67 7 164 137 16 32 64 128 256), losses := [] }

theorem u19862 : Upper (D 8) (R 8) [66,5,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19863_9 : Upper (D 8) (R 8) [66,5,160,144,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10002

theorem m19863_33 : Upper (D 8) (R 8) [66,5,160,144,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10011

theorem m19863_40 : Upper (D 8) (R 8) [66,5,160,144,40] 13 :=
  permutation_upper _ _ _ [66,5,160,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10022

theorem m19863_65 : Upper (D 8) (R 8) [66,5,160,144,65] 13 :=
  permutation_upper _ _ _ [66,5,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10030

theorem m19863_72 : Upper (D 8) (R 8) [66,5,160,144,72] 13 :=
  permutation_upper _ _ _ [66,5,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10035

theorem m19863_96 : Upper (D 8) (R 8) [66,5,160,144,96] 13 :=
  permutation_upper _ _ _ [66,5,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10042

def r19863 : Route 9 := (fun mask => (mask,id))

def c19863 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u19863 : Upper (D 8) (R 8) [66,5,160,144] 13 := by
  apply FastRouting.sound _ _ [66,5,160,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r19863 c19863
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19863_9
  · exact m19863_33
  · exact m19863_40
  · exact m19863_65
  · exact m19863_72
  · exact m19863_96
  · exact u10051
  · exact u10052
  · exact u10053
  · exact u10054

def b19864 : PairBound 9 := { available := 377, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 168 377 377 377 505 377), lower := (rows 67 7 164 168 16 32 64 128 256), losses := [] }

theorem u19864 : Upper (D 8) (R 8) [66,5,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19865_9 : Upper (D 8) (R 8) [66,5,160,192,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10003

theorem m19865_33 : Upper (D 8) (R 8) [66,5,160,192,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10012

theorem m19865_40 : Upper (D 8) (R 8) [66,5,160,192,40] 13 :=
  permutation_upper _ _ _ [66,5,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10024

def r19865 : Route 9 := (fun mask => (mask,id))

def c19865 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19865 : Upper (D 8) (R 8) [66,5,160,192] 13 := by
  apply FastRouting.sound _ _ [66,5,160,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r19865 c19865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19865_9
  · exact m19865_33
  · exact m19865_40
  · exact u10058
  · exact u10059
  · exact u10060

def b19866 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 265 248 248 248 248 504), lower := (rows 67 7 164 265 16 32 64 128 256), losses := [] }

theorem u19866 : Upper (D 8) (R 8) [66,5,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19867_9 : Upper (D 8) (R 8) [66,5,160,272,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10004

theorem m19867_33 : Upper (D 8) (R 8) [66,5,160,272,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10013

theorem m19867_40 : Upper (D 8) (R 8) [66,5,160,272,40] 13 :=
  permutation_upper _ _ _ [66,5,160,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10026

theorem m19867_65 : Upper (D 8) (R 8) [66,5,160,272,65] 13 :=
  permutation_upper _ _ _ [66,5,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10031

theorem m19867_72 : Upper (D 8) (R 8) [66,5,160,272,72] 13 :=
  permutation_upper _ _ _ [66,5,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10038

theorem m19867_96 : Upper (D 8) (R 8) [66,5,160,272,96] 13 :=
  permutation_upper _ _ _ [66,5,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10045

theorem m19867_129 : Upper (D 8) (R 8) [66,5,160,272,129] 13 :=
  permutation_upper _ _ _ [66,5,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10048

theorem m19867_136 : Upper (D 8) (R 8) [66,5,160,272,136] 13 :=
  permutation_upper _ _ _ [66,5,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10052

theorem m19867_160 : Upper (D 8) (R 8) [66,5,160,272,160] 13 :=
  permutation_upper _ _ _ [66,5,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10055

theorem m19867_192 : Upper (D 8) (R 8) [66,5,160,272,192] 13 :=
  permutation_upper _ _ _ [66,5,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10059

def r19867 : Route 9 := (fun mask => (mask,id))

def c19867 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19867 : Upper (D 8) (R 8) [66,5,160,272] 13 := by
  apply FastRouting.sound _ _ [66,5,160,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19867 c19867
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19867_9
  · exact m19867_33
  · exact m19867_40
  · exact m19867_65
  · exact m19867_72
  · exact m19867_96
  · exact m19867_129
  · exact m19867_136
  · exact m19867_160
  · exact m19867_192

theorem m19868_9 : Upper (D 8) (R 8) [66,5,160,288,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10005

theorem m19868_33 : Upper (D 8) (R 8) [66,5,160,288,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10014

theorem m19868_40 : Upper (D 8) (R 8) [66,5,160,288,40] 13 :=
  permutation_upper _ _ _ [66,5,160,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10027

theorem m19868_65 : Upper (D 8) (R 8) [66,5,160,288,65] 13 :=
  permutation_upper _ _ _ [66,5,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10032

theorem m19868_72 : Upper (D 8) (R 8) [66,5,160,288,72] 13 :=
  permutation_upper _ _ _ [66,5,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10039

theorem m19868_96 : Upper (D 8) (R 8) [66,5,160,288,96] 13 :=
  permutation_upper _ _ _ [66,5,160,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10046

theorem m19868_129 : Upper (D 8) (R 8) [66,5,160,288,129] 13 :=
  permutation_upper _ _ _ [66,5,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10049

theorem m19868_136 : Upper (D 8) (R 8) [66,5,160,288,136] 13 :=
  permutation_upper _ _ _ [66,5,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10053

theorem m19868_160 : Upper (D 8) (R 8) [66,5,160,288,160] 13 :=
  permutation_upper _ _ _ [66,5,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10056

theorem m19868_192 : Upper (D 8) (R 8) [66,5,160,288,192] 13 :=
  permutation_upper _ _ _ [66,5,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10060

def r19868 : Route 9 := (fun mask => (mask,id))

def c19868 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19868 : Upper (D 8) (R 8) [66,5,160,288] 13 := by
  apply FastRouting.sound _ _ [66,5,160,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19868 c19868
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19868_9
  · exact m19868_33
  · exact m19868_40
  · exact m19868_65
  · exact m19868_72
  · exact m19868_96
  · exact m19868_129
  · exact m19868_136
  · exact m19868_160
  · exact m19868_192

theorem m19869_9 : Upper (D 8) (R 8) [66,5,160,320,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10006

theorem m19869_33 : Upper (D 8) (R 8) [66,5,160,320,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10015

theorem m19869_40 : Upper (D 8) (R 8) [66,5,160,320,40] 13 :=
  permutation_upper _ _ _ [66,5,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10028

theorem m19869_129 : Upper (D 8) (R 8) [66,5,160,320,129] 13 :=
  permutation_upper _ _ _ [66,5,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10050

theorem m19869_136 : Upper (D 8) (R 8) [66,5,160,320,136] 13 :=
  permutation_upper _ _ _ [66,5,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10054

theorem m19869_160 : Upper (D 8) (R 8) [66,5,160,320,160] 13 :=
  permutation_upper _ _ _ [66,5,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10057

def r19869 : Route 9 := (fun mask => (mask,id))

def c19869 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19869 : Upper (D 8) (R 8) [66,5,160,320] 13 := by
  apply FastRouting.sound _ _ [66,5,160,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19869 c19869
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19869_9
  · exact m19869_33
  · exact m19869_40
  · exact m19869_129
  · exact m19869_136
  · exact m19869_160

theorem m19870_9 : Upper (D 8) (R 8) [66,5,160,384,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10007

theorem m19870_33 : Upper (D 8) (R 8) [66,5,160,384,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10016

theorem m19870_40 : Upper (D 8) (R 8) [66,5,160,384,40] 13 :=
  permutation_upper _ _ _ [66,5,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10029

theorem m19870_65 : Upper (D 8) (R 8) [66,5,160,384,65] 13 :=
  permutation_upper _ _ _ [66,5,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10033

theorem m19870_72 : Upper (D 8) (R 8) [66,5,160,384,72] 13 :=
  permutation_upper _ _ _ [66,5,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10040

theorem m19870_96 : Upper (D 8) (R 8) [66,5,160,384,96] 13 :=
  permutation_upper _ _ _ [66,5,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10047

def r19870 : Route 9 := (fun mask => (mask,id))

def c19870 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19870 : Upper (D 8) (R 8) [66,5,160,384] 13 := by
  apply FastRouting.sound _ _ [66,5,160,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19870 c19870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19870_9
  · exact m19870_33
  · exact m19870_40
  · exact m19870_65
  · exact m19870_72
  · exact m19870_96

def b19871 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 25 240 224 224 224 480), lower := (rows 67 7 268 25 16 32 64 128 256), losses := [] }

theorem u19871 : Upper (D 8) (R 8) [66,5,264,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19872 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 41 240 240 240 240 496), lower := (rows 67 7 268 41 16 32 64 128 256), losses := [] }

theorem u19872 : Upper (D 8) (R 8) [66,5,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19873 : Route 9 := (fun mask => (mask,id))

def c19873 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19873 : Upper (D 8) (R 8) [66,5,264,48] 13 := by
  apply FastRouting.sound _ _ [66,5,264,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19873 c19873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10061
  · exact u10062
  · exact u10063
  · exact u10064
  · exact u10065
  · exact u10066

def b19874 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 268 73 176 176 240 176 432), lower := (rows 67 7 268 73 16 32 64 128 256), losses := [] }

theorem u19874 : Upper (D 8) (R 8) [66,5,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19875 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 268 88 177 161 225 161 417), lower := (rows 67 7 268 88 16 32 64 128 256), losses := [] }

theorem u19875 : Upper (D 8) (R 8) [66,5,264,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19876 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 268 104 177 177 241 177 433), lower := (rows 67 7 268 104 16 32 64 128 256), losses := [] }

theorem u19876 : Upper (D 8) (R 8) [66,5,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19877 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 137 240 240 240 240 496), lower := (rows 67 7 268 137 16 32 64 128 256), losses := [] }

theorem u19877 : Upper (D 8) (R 8) [66,5,264,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19878 : Route 9 := (fun mask => (mask,id))

def c19878 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19878 : Upper (D 8) (R 8) [66,5,264,144] 13 := by
  apply FastRouting.sound _ _ [66,5,264,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19878 c19878
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10067
  · exact u10068
  · exact u10069
  · exact u10070
  · exact u10071
  · exact u10072

def r19879 : Route 9 := (fun mask => (mask,id))

def c19879 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19879 : Upper (D 8) (R 8) [66,5,264,160] 13 := by
  apply FastRouting.sound _ _ [66,5,264,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19879 c19879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10073
  · exact u10074
  · exact u10075
  · exact u10076
  · exact u10077
  · exact u10078

def b19880 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 268 200 177 177 241 177 433), lower := (rows 67 7 268 200 16 32 64 128 256), losses := [] }

theorem u19880 : Upper (D 8) (R 8) [66,5,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19881 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 25 248 232 232 232 488), lower := (rows 67 7 292 25 16 32 64 128 256), losses := [] }

theorem u19881 : Upper (D 8) (R 8) [66,5,288,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19882 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 41 248 248 248 248 504), lower := (rows 67 7 292 41 16 32 64 128 256), losses := [] }

theorem u19882 : Upper (D 8) (R 8) [66,5,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19883_9 : Upper (D 8) (R 8) [66,5,288,48,9] 13 :=
  permutation_upper _ _ _ [66,5,288,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10079

theorem m19883_33 : Upper (D 8) (R 8) [66,5,288,48,33] 13 :=
  permutation_upper _ _ _ [66,5,288,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10085

def r19883 : Route 9 := (fun mask => (mask,id))

def c19883 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19883 : Upper (D 8) (R 8) [66,5,288,48] 13 := by
  apply FastRouting.sound _ _ [66,5,288,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19883 c19883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19883_9
  · exact m19883_33
  · exact u10091
  · exact u10092
  · exact u10093
  · exact u10094
  · exact u10095
  · exact u10096
  · exact u10097
  · exact u10098

def b19884 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 292 73 184 184 248 184 440), lower := (rows 67 7 292 73 16 32 64 128 256), losses := [] }

theorem u19884 : Upper (D 8) (R 8) [66,5,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19885_9 : Upper (D 8) (R 8) [66,5,288,80,9] 13 :=
  permutation_upper _ _ _ [66,5,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10080

theorem m19885_33 : Upper (D 8) (R 8) [66,5,288,80,33] 13 :=
  permutation_upper _ _ _ [66,5,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10086

theorem m19885_40 : Upper (D 8) (R 8) [66,5,288,80,40] 13 :=
  permutation_upper _ _ _ [66,5,288,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10093

def r19885 : Route 9 := (fun mask => (mask,id))

def c19885 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19885 : Upper (D 8) (R 8) [66,5,288,80] 13 := by
  apply FastRouting.sound _ _ [66,5,288,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19885 c19885
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19885_9
  · exact m19885_33
  · exact m19885_40
  · exact u10101
  · exact u10102
  · exact u10103

theorem m19886_9 : Upper (D 8) (R 8) [66,5,288,96,9] 13 :=
  permutation_upper _ _ _ [66,5,288,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10081

theorem m19886_33 : Upper (D 8) (R 8) [66,5,288,96,33] 13 :=
  permutation_upper _ _ _ [66,5,288,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10087

theorem m19886_40 : Upper (D 8) (R 8) [66,5,288,96,40] 13 :=
  permutation_upper _ _ _ [66,5,288,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10094

def r19886 : Route 9 := (fun mask => (mask,id))

def c19886 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19886 : Upper (D 8) (R 8) [66,5,288,96] 13 := by
  apply FastRouting.sound _ _ [66,5,288,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19886 c19886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19886_9
  · exact m19886_33
  · exact m19886_40
  · exact u10104
  · exact u10105
  · exact u10106

def b19887 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 137 248 248 248 248 504), lower := (rows 67 7 292 137 16 32 64 128 256), losses := [] }

theorem u19887 : Upper (D 8) (R 8) [66,5,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19888_9 : Upper (D 8) (R 8) [66,5,288,144,9] 13 :=
  permutation_upper _ _ _ [66,5,288,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10082

theorem m19888_33 : Upper (D 8) (R 8) [66,5,288,144,33] 13 :=
  permutation_upper _ _ _ [66,5,288,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10088

theorem m19888_40 : Upper (D 8) (R 8) [66,5,288,144,40] 13 :=
  permutation_upper _ _ _ [66,5,288,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10096

theorem m19888_65 : Upper (D 8) (R 8) [66,5,288,144,65] 13 :=
  permutation_upper _ _ _ [66,5,288,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10099

theorem m19888_72 : Upper (D 8) (R 8) [66,5,288,144,72] 13 :=
  permutation_upper _ _ _ [66,5,288,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10102

theorem m19888_96 : Upper (D 8) (R 8) [66,5,288,144,96] 13 :=
  permutation_upper _ _ _ [66,5,288,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10105

theorem m19888_129 : Upper (D 8) (R 8) [66,5,288,144,129] 13 :=
  permutation_upper _ _ _ [66,5,288,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10107

def r19888 : Route 9 := (fun mask => (mask,id))

def c19888 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19888 : Upper (D 8) (R 8) [66,5,288,144] 13 := by
  apply FastRouting.sound _ _ [66,5,288,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19888 c19888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19888_9
  · exact m19888_33
  · exact m19888_40
  · exact m19888_65
  · exact m19888_72
  · exact m19888_96
  · exact m19888_129
  · exact u10110
  · exact u10111
  · exact u10112

theorem m19889_9 : Upper (D 8) (R 8) [66,5,288,160,9] 13 :=
  permutation_upper _ _ _ [66,5,288,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10083

theorem m19889_33 : Upper (D 8) (R 8) [66,5,288,160,33] 13 :=
  permutation_upper _ _ _ [66,5,288,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10089

theorem m19889_40 : Upper (D 8) (R 8) [66,5,288,160,40] 13 :=
  permutation_upper _ _ _ [66,5,288,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10097

theorem m19889_65 : Upper (D 8) (R 8) [66,5,288,160,65] 13 :=
  permutation_upper _ _ _ [66,5,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10100

theorem m19889_72 : Upper (D 8) (R 8) [66,5,288,160,72] 13 :=
  permutation_upper _ _ _ [66,5,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10103

theorem m19889_96 : Upper (D 8) (R 8) [66,5,288,160,96] 13 :=
  permutation_upper _ _ _ [66,5,288,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10106

theorem m19889_129 : Upper (D 8) (R 8) [66,5,288,160,129] 13 :=
  permutation_upper _ _ _ [66,5,288,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10108

theorem m19889_136 : Upper (D 8) (R 8) [66,5,288,160,136] 13 :=
  permutation_upper _ _ _ [66,5,288,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10111

def r19889 : Route 9 := (fun mask => (mask,id))

def c19889 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19889 : Upper (D 8) (R 8) [66,5,288,160] 13 := by
  apply FastRouting.sound _ _ [66,5,288,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19889 c19889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19889_9
  · exact m19889_33
  · exact m19889_40
  · exact m19889_65
  · exact m19889_72
  · exact m19889_96
  · exact m19889_129
  · exact m19889_136
  · exact u10113
  · exact u10114

theorem m19890_9 : Upper (D 8) (R 8) [66,5,288,192,9] 13 :=
  permutation_upper _ _ _ [66,5,288,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10084

theorem m19890_33 : Upper (D 8) (R 8) [66,5,288,192,33] 13 :=
  permutation_upper _ _ _ [66,5,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10090

theorem m19890_40 : Upper (D 8) (R 8) [66,5,288,192,40] 13 :=
  permutation_upper _ _ _ [66,5,288,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10098

theorem m19890_129 : Upper (D 8) (R 8) [66,5,288,192,129] 13 :=
  permutation_upper _ _ _ [66,5,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10109

theorem m19890_136 : Upper (D 8) (R 8) [66,5,288,192,136] 13 :=
  permutation_upper _ _ _ [66,5,288,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10112

theorem m19890_160 : Upper (D 8) (R 8) [66,5,288,192,160] 13 :=
  permutation_upper _ _ _ [66,5,288,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10114

def r19890 : Route 9 := (fun mask => (mask,id))

def c19890 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19890 : Upper (D 8) (R 8) [66,5,288,192] 13 := by
  apply FastRouting.sound _ _ [66,5,288,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19890 c19890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19890_9
  · exact m19890_33
  · exact m19890_40
  · exact m19890_129
  · exact m19890_136
  · exact m19890_160

def b19891 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 25 248 232 232 232 488), lower := (rows 67 7 388 25 16 32 64 128 256), losses := [] }

theorem u19891 : Upper (D 8) (R 8) [66,5,384,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19892 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 41 248 248 248 248 504), lower := (rows 67 7 388 41 16 32 64 128 256), losses := [] }

theorem u19892 : Upper (D 8) (R 8) [66,5,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19893_9 : Upper (D 8) (R 8) [66,5,384,48,9] 13 :=
  permutation_upper _ _ _ [66,5,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10115

theorem m19893_33 : Upper (D 8) (R 8) [66,5,384,48,33] 13 :=
  permutation_upper _ _ _ [66,5,384,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10121

def r19893 : Route 9 := (fun mask => (mask,id))

def c19893 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19893 : Upper (D 8) (R 8) [66,5,384,48] 13 := by
  apply FastRouting.sound _ _ [66,5,384,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19893 c19893
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19893_9
  · exact m19893_33
  · exact u10127
  · exact u10128
  · exact u10129
  · exact u10130
  · exact u10131
  · exact u10132
  · exact u10133
  · exact u10134

def b19894 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 388 73 184 184 248 184 440), lower := (rows 67 7 388 73 16 32 64 128 256), losses := [] }

theorem u19894 : Upper (D 8) (R 8) [66,5,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19895_9 : Upper (D 8) (R 8) [66,5,384,80,9] 13 :=
  permutation_upper _ _ _ [66,5,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10116

theorem m19895_33 : Upper (D 8) (R 8) [66,5,384,80,33] 13 :=
  permutation_upper _ _ _ [66,5,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10122

theorem m19895_40 : Upper (D 8) (R 8) [66,5,384,80,40] 13 :=
  permutation_upper _ _ _ [66,5,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10129

def r19895 : Route 9 := (fun mask => (mask,id))

def c19895 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19895 : Upper (D 8) (R 8) [66,5,384,80] 13 := by
  apply FastRouting.sound _ _ [66,5,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19895 c19895
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19895_9
  · exact m19895_33
  · exact m19895_40
  · exact u10137
  · exact u10138
  · exact u10139

theorem m19896_9 : Upper (D 8) (R 8) [66,5,384,96,9] 13 :=
  permutation_upper _ _ _ [66,5,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10117

theorem m19896_33 : Upper (D 8) (R 8) [66,5,384,96,33] 13 :=
  permutation_upper _ _ _ [66,5,384,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10123

theorem m19896_40 : Upper (D 8) (R 8) [66,5,384,96,40] 13 :=
  permutation_upper _ _ _ [66,5,384,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10130

def r19896 : Route 9 := (fun mask => (mask,id))

def c19896 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19896 : Upper (D 8) (R 8) [66,5,384,96] 13 := by
  apply FastRouting.sound _ _ [66,5,384,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19896 c19896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19896_9
  · exact m19896_33
  · exact m19896_40
  · exact u10140
  · exact u10141
  · exact u10142

def b19897 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 137 120 120 120 248 376), lower := (rows 67 7 388 137 16 32 64 128 256), losses := [] }

theorem u19897 : Upper (D 8) (R 8) [66,5,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19898_9 : Upper (D 8) (R 8) [66,5,384,144,9] 13 :=
  permutation_upper _ _ _ [66,5,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10118

theorem m19898_33 : Upper (D 8) (R 8) [66,5,384,144,33] 13 :=
  permutation_upper _ _ _ [66,5,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10124

theorem m19898_40 : Upper (D 8) (R 8) [66,5,384,144,40] 13 :=
  permutation_upper _ _ _ [66,5,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10132

theorem m19898_65 : Upper (D 8) (R 8) [66,5,384,144,65] 13 :=
  permutation_upper _ _ _ [66,5,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10135

theorem m19898_72 : Upper (D 8) (R 8) [66,5,384,144,72] 13 :=
  permutation_upper _ _ _ [66,5,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10138

theorem m19898_96 : Upper (D 8) (R 8) [66,5,384,144,96] 13 :=
  permutation_upper _ _ _ [66,5,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10141

def r19898 : Route 9 := (fun mask => (mask,id))

def c19898 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19898 : Upper (D 8) (R 8) [66,5,384,144] 13 := by
  apply FastRouting.sound _ _ [66,5,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19898 c19898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19898_9
  · exact m19898_33
  · exact m19898_40
  · exact m19898_65
  · exact m19898_72
  · exact m19898_96

theorem m19899_9 : Upper (D 8) (R 8) [66,5,384,160,9] 13 :=
  permutation_upper _ _ _ [66,5,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10119

theorem m19899_33 : Upper (D 8) (R 8) [66,5,384,160,33] 13 :=
  permutation_upper _ _ _ [66,5,384,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10125

theorem m19899_40 : Upper (D 8) (R 8) [66,5,384,160,40] 13 :=
  permutation_upper _ _ _ [66,5,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10133

theorem m19899_65 : Upper (D 8) (R 8) [66,5,384,160,65] 13 :=
  permutation_upper _ _ _ [66,5,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10136

theorem m19899_72 : Upper (D 8) (R 8) [66,5,384,160,72] 13 :=
  permutation_upper _ _ _ [66,5,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10139

theorem m19899_96 : Upper (D 8) (R 8) [66,5,384,160,96] 13 :=
  permutation_upper _ _ _ [66,5,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10142

def r19899 : Route 9 := (fun mask => (mask,id))

def c19899 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19899 : Upper (D 8) (R 8) [66,5,384,160] 13 := by
  apply FastRouting.sound _ _ [66,5,384,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19899 c19899
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19899_9
  · exact m19899_33
  · exact m19899_40
  · exact m19899_65
  · exact m19899_72
  · exact m19899_96

theorem m19900_9 : Upper (D 8) (R 8) [66,5,384,192,9] 13 :=
  permutation_upper _ _ _ [66,5,384,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10120

theorem m19900_33 : Upper (D 8) (R 8) [66,5,384,192,33] 13 :=
  permutation_upper _ _ _ [66,5,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10126

theorem m19900_40 : Upper (D 8) (R 8) [66,5,384,192,40] 13 :=
  permutation_upper _ _ _ [66,5,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10134

def r19900 : Route 9 := (fun mask => (mask,id))

def c19900 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19900 : Upper (D 8) (R 8) [66,5,384,192] 13 := by
  apply FastRouting.sound _ _ [66,5,384,192] 13 (by decide) (choices 2) [9,33,40] r19900 c19900
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19900_9
  · exact m19900_33
  · exact m19900_40

def b19901 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 432, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 21 41 496 480 480 480 480), lower := (rows 67 14 21 41 16 32 64 128 256), losses := [] }

theorem u19901 : Upper (D 8) (R 8) [66,12,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19902 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 21 73 432 416 480 416 416), lower := (rows 67 14 21 73 16 32 64 128 256), losses := [] }

theorem u19902 : Upper (D 8) (R 8) [66,12,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19903 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 21 104 433 417 481 417 417), lower := (rows 67 14 21 104 16 32 64 128 256), losses := [] }

theorem u19903 : Upper (D 8) (R 8) [66,12,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19904 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 432, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 21 137 496 480 480 480 480), lower := (rows 67 14 21 137 16 32 64 128 256), losses := [] }

theorem u19904 : Upper (D 8) (R 8) [66,12,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19905 : Route 9 := (fun mask => (mask,id))

def c19905 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19905 : Upper (D 8) (R 8) [66,12,17,160] 13 := by
  apply FastRouting.sound _ _ [66,12,17,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19905 c19905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10143
  · exact u10144
  · exact u10145
  · exact u10146
  · exact u10147
  · exact u10148
  · exact u10149
  · exact u10150
  · exact u10151
  · exact u10152

def b19906 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 21 200 433 417 481 417 417), lower := (rows 67 14 21 200 16 32 64 128 256), losses := [] }

theorem u19906 : Upper (D 8) (R 8) [66,12,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19907 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 21 265 240 224 224 224 480), lower := (rows 67 14 21 265 16 32 64 128 256), losses := [] }

theorem u19907 : Upper (D 8) (R 8) [66,12,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19908 : Route 9 := (fun mask => (mask,id))

def c19908 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19908 : Upper (D 8) (R 8) [66,12,17,288] 13 := by
  apply FastRouting.sound _ _ [66,12,17,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19908 c19908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10153
  · exact u10154
  · exact u10155
  · exact u10156
  · exact u10157
  · exact u10158

def b19909 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 21 328 177 161 225 161 417), lower := (rows 67 14 21 328 16 32 64 128 256), losses := [] }

theorem u19909 : Upper (D 8) (R 8) [66,12,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19910 : Route 9 := (fun mask => (mask,id))

def c19910 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19910 : Upper (D 8) (R 8) [66,12,17,384] 13 := by
  apply FastRouting.sound _ _ [66,12,17,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19910 c19910
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10159
  · exact u10160
  · exact u10161
  · exact u10162
  · exact u10163
  · exact u10164

def b19911 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 41 496 496 496 496 496), lower := (rows 67 14 37 41 16 32 64 128 256), losses := [] }

theorem u19911 : Upper (D 8) (R 8) [66,12,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19912 : Route 9 := (fun mask => (mask,id))

def c19912 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19912 : Upper (D 8) (R 8) [66,12,33,48] 13 := by
  apply FastRouting.sound _ _ [66,12,33,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19912 c19912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10165
  · exact u10166
  · exact u10167
  · exact u10168
  · exact u10169
  · exact u10170
  · exact u10171
  · exact u10172
  · exact u10173
  · exact u10174

def b19913 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 73 432 432 496 432 432), lower := (rows 67 14 37 73 16 32 64 128 256), losses := [] }

theorem u19913 : Upper (D 8) (R 8) [66,12,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19914 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 88 433 417 481 417 417), lower := (rows 67 14 37 88 16 32 64 128 256), losses := [] }

theorem u19914 : Upper (D 8) (R 8) [66,12,33,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19915 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 104 433 433 497 433 433), lower := (rows 67 14 37 104 16 32 64 128 256), losses := [] }

theorem u19915 : Upper (D 8) (R 8) [66,12,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19916 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 432, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 37 137 496 496 496 496 496), lower := (rows 67 14 37 137 16 32 64 128 256), losses := [] }

theorem u19916 : Upper (D 8) (R 8) [66,12,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19917 : Route 9 := (fun mask => (mask,id))

def c19917 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19917 : Upper (D 8) (R 8) [66,12,33,144] 13 := by
  apply FastRouting.sound _ _ [66,12,33,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19917 c19917
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10175
  · exact u10176
  · exact u10177
  · exact u10178
  · exact u10179
  · exact u10180
  · exact u10181
  · exact u10182
  · exact u10183
  · exact u10184

def r19918 : Route 9 := (fun mask => (mask,id))

def c19918 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19918 : Upper (D 8) (R 8) [66,12,33,160] 13 := by
  apply FastRouting.sound _ _ [66,12,33,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19918 c19918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10185
  · exact u10186
  · exact u10187
  · exact u10188
  · exact u10189
  · exact u10190
  · exact u10191
  · exact u10192
  · exact u10193
  · exact u10194

def b19919 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 200 433 433 497 433 433), lower := (rows 67 14 37 200 16 32 64 128 256), losses := [] }

theorem u19919 : Upper (D 8) (R 8) [66,12,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u19919
end Delivery.IrregularNine14.P08
