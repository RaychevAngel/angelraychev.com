import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0284
import IrregularNine14P08C0285
import IrregularNine14P08C0286
import IrregularNine14P08C0287

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22920 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 242 242 242 242 498), lower := (rows 289 7 13 200 16 32 64 128 256), losses := [] }

theorem u22920 : Upper (D 8) (R 8) [288,5,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22921 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 25 240 224 224 224 480), lower := (rows 289 7 14 25 16 32 64 128 256), losses := [] }

theorem u22921 : Upper (D 8) (R 8) [288,5,10,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22922 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 14 41 240 240 240 240 496), lower := (rows 289 7 14 41 16 32 64 128 256), losses := [] }

theorem u22922 : Upper (D 8) (R 8) [288,5,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22923 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22923 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22923 : Upper (D 8) (R 8) [288,5,10,48] 13 := by
  apply FastRouting.sound _ _ [288,5,10,48] 13 (by decide) (choices 2) [33,65,96,192] r22923 c22923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17071
  · exact u17072
  · exact u17073
  · exact u17074

def b22924 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 240 240 240 240 496), lower := (rows 289 7 14 73 16 32 64 128 256), losses := [] }

theorem u22924 : Upper (D 8) (R 8) [288,5,10,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22925 : Route 9 := (fun mask => (mask,id))

def c22925 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22925 : Upper (D 8) (R 8) [288,5,10,80] 13 := by
  apply FastRouting.sound _ _ [288,5,10,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22925 c22925
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u17078
  · exact u17079
  · exact u17080
  · exact u17081
  · exact u17082
  · exact u17083

def r22926 : Route 9 := (fun mask => (mask,id))

def c22926 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22926 : Upper (D 8) (R 8) [288,5,10,96] 13 := by
  apply FastRouting.sound _ _ [288,5,10,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22926 c22926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u17084
  · exact u17085
  · exact u17086
  · exact u17087
  · exact u17088
  · exact u17089

def r22927 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22927 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22927 : Upper (D 8) (R 8) [288,5,10,192] 13 := by
  apply FastRouting.sound _ _ [288,5,10,192] 13 (by decide) (choices 2) [33,65,96,192] r22927 c22927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17090
  · exact u17091
  · exact u17092
  · exact u17093

def b22928 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 42 248 232 232 232 488), lower := (rows 289 7 21 42 16 32 64 128 256), losses := [] }

theorem u22928 : Upper (D 8) (R 8) [288,5,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22929 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 74 248 232 232 232 488), lower := (rows 289 7 21 74 16 32 64 128 256), losses := [] }

theorem u22929 : Upper (D 8) (R 8) [288,5,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22930 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 104 250 234 234 234 490), lower := (rows 289 7 21 104 16 32 64 128 256), losses := [] }

theorem u22930 : Upper (D 8) (R 8) [288,5,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22931 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 200 250 234 234 234 490), lower := (rows 289 7 21 200 16 32 64 128 256), losses := [] }

theorem u22931 : Upper (D 8) (R 8) [288,5,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22932 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 22 73 248 232 232 232 488), lower := (rows 289 7 22 73 16 32 64 128 256), losses := [] }

theorem u22932 : Upper (D 8) (R 8) [288,5,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22933_9 : Upper (D 8) (R 8) [288,5,18,96,9] 13 :=
  permutation_upper _ _ _ [288,5,10,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17067

theorem m22933_33 : Upper (D 8) (R 8) [288,5,18,96,33] 13 :=
  permutation_upper _ _ _ [288,5,10,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17069

theorem m22933_40 : Upper (D 8) (R 8) [288,5,18,96,40] 13 :=
  permutation_upper _ _ _ [288,5,10,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17073

theorem m22933_65 : Upper (D 8) (R 8) [288,5,18,96,65] 13 :=
  permutation_upper _ _ _ [288,5,10,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17075

theorem m22933_72 : Upper (D 8) (R 8) [288,5,18,96,72] 13 :=
  permutation_upper _ _ _ [288,5,10,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17080

theorem m22933_96 : Upper (D 8) (R 8) [288,5,18,96,96] 13 :=
  permutation_upper _ _ _ [288,5,10,96,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17086

theorem m22933_129 : Upper (D 8) (R 8) [288,5,18,96,129] 13 :=
  permutation_upper _ _ _ [288,5,10,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17076

theorem m22933_136 : Upper (D 8) (R 8) [288,5,18,96,136] 13 :=
  permutation_upper _ _ _ [288,5,10,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17082

theorem m22933_160 : Upper (D 8) (R 8) [288,5,18,96,160] 13 :=
  permutation_upper _ _ _ [288,5,10,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17088

theorem m22933_192 : Upper (D 8) (R 8) [288,5,18,96,192] 13 :=
  permutation_upper _ _ _ [288,5,10,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17092

def r22933 : Route 9 := (fun mask => (mask,id))

def c22933 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22933 : Upper (D 8) (R 8) [288,5,18,96] 13 := by
  apply FastRouting.sound _ _ [288,5,18,96] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22933 c22933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22933_9
  · exact m22933_33
  · exact m22933_40
  · exact m22933_65
  · exact m22933_72
  · exact m22933_96
  · exact m22933_129
  · exact m22933_136
  · exact m22933_160
  · exact m22933_192

theorem m22934_9 : Upper (D 8) (R 8) [288,5,18,192,9] 13 :=
  permutation_upper _ _ _ [288,5,10,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17068

theorem m22934_33 : Upper (D 8) (R 8) [288,5,18,192,33] 13 :=
  permutation_upper _ _ _ [288,5,10,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17070

theorem m22934_40 : Upper (D 8) (R 8) [288,5,18,192,40] 13 :=
  permutation_upper _ _ _ [288,5,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17074

theorem m22934_65 : Upper (D 8) (R 8) [288,5,18,192,65] 13 :=
  permutation_upper _ _ _ [288,5,10,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17077

theorem m22934_72 : Upper (D 8) (R 8) [288,5,18,192,72] 13 :=
  permutation_upper _ _ _ [288,5,10,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17083

theorem m22934_96 : Upper (D 8) (R 8) [288,5,18,192,96] 13 :=
  permutation_upper _ _ _ [288,5,10,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17089

theorem m22934_192 : Upper (D 8) (R 8) [288,5,18,192,192] 13 :=
  permutation_upper _ _ _ [288,5,10,192,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17093

def r22934 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22934 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22934 : Upper (D 8) (R 8) [288,5,18,192] 13 := by
  apply FastRouting.sound _ _ [288,5,18,192] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22934 c22934
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22934_9
  · exact m22934_33
  · exact m22934_40
  · exact m22934_65
  · exact m22934_72
  · exact m22934_96
  · exact m22934_192

def b22935 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 28 41 242 226 226 226 482), lower := (rows 289 7 28 41 16 32 64 128 256), losses := [] }

theorem u22935 : Upper (D 8) (R 8) [288,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22936_33 : Upper (D 8) (R 8) [288,5,24,34,33] 13 :=
  permutation_upper _ _ _ [288,5,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17094

def r22936 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22936 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22936 : Upper (D 8) (R 8) [288,5,24,34] 13 := by
  apply FastRouting.sound _ _ [288,5,24,34] 13 (by decide) (choices 2) [33,65,96,192] r22936 c22936
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22936_33
  · exact u17098
  · exact u17099
  · exact u17100

def b22937 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 28 73 242 226 226 226 482), lower := (rows 289 7 28 73 16 32 64 128 256), losses := [] }

theorem u22937 : Upper (D 8) (R 8) [288,5,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22938_33 : Upper (D 8) (R 8) [288,5,24,66,33] 13 :=
  permutation_upper _ _ _ [288,5,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17095

theorem m22938_65 : Upper (D 8) (R 8) [288,5,24,66,65] 13 :=
  permutation_upper _ _ _ [288,5,24,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17101

theorem m22938_129 : Upper (D 8) (R 8) [288,5,24,66,129] 13 :=
  permutation_upper _ _ _ [288,5,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17103

def r22938 : Route 9 := (fun mask => (mask,id))

def c22938 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22938 : Upper (D 8) (R 8) [288,5,24,66] 13 := by
  apply FastRouting.sound _ _ [288,5,24,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22938 c22938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22938_33
  · exact m22938_65
  · exact u17106
  · exact m22938_129
  · exact u17107
  · exact u17108

theorem m22939_3 : Upper (D 8) (R 8) [288,5,24,96,3] 13 :=
  permutation_upper _ _ _ [288,5,9,18,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17047

theorem m22939_33 : Upper (D 8) (R 8) [288,5,24,96,33] 13 :=
  permutation_upper _ _ _ [288,5,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17096

theorem m22939_34 : Upper (D 8) (R 8) [288,5,24,96,34] 13 :=
  permutation_upper _ _ _ [288,5,24,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17099

theorem m22939_65 : Upper (D 8) (R 8) [288,5,24,96,65] 13 :=
  permutation_upper _ _ _ [288,5,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17102

theorem m22939_66 : Upper (D 8) (R 8) [288,5,24,96,66] 13 :=
  permutation_upper _ _ _ [288,5,24,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17106

theorem m22939_129 : Upper (D 8) (R 8) [288,5,24,96,129] 13 :=
  permutation_upper _ _ _ [288,5,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17104

theorem m22939_130 : Upper (D 8) (R 8) [288,5,24,96,130] 13 :=
  permutation_upper _ _ _ [288,5,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17107

def r22939 : Route 9 := (fun mask => (mask,id))

def c22939 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22939 : Upper (D 8) (R 8) [288,5,24,96] 13 := by
  apply FastRouting.sound _ _ [288,5,24,96] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r22939 c22939
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22939_3
  · exact m22939_33
  · exact m22939_34
  · exact m22939_65
  · exact m22939_66
  · exact u17109
  · exact m22939_129
  · exact m22939_130
  · exact u17110
  · exact u17111

theorem m22940_3 : Upper (D 8) (R 8) [288,5,24,192,3] 13 :=
  permutation_upper _ _ _ [288,5,9,18,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17048

theorem m22940_33 : Upper (D 8) (R 8) [288,5,24,192,33] 13 :=
  permutation_upper _ _ _ [288,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17097

theorem m22940_34 : Upper (D 8) (R 8) [288,5,24,192,34] 13 :=
  permutation_upper _ _ _ [288,5,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17100

theorem m22940_65 : Upper (D 8) (R 8) [288,5,24,192,65] 13 :=
  permutation_upper _ _ _ [288,5,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17105

theorem m22940_66 : Upper (D 8) (R 8) [288,5,24,192,66] 13 :=
  permutation_upper _ _ _ [288,5,24,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17108

theorem m22940_96 : Upper (D 8) (R 8) [288,5,24,192,96] 13 :=
  permutation_upper _ _ _ [288,5,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17111

def r22940 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22940 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22940 : Upper (D 8) (R 8) [288,5,24,192] 13 := by
  apply FastRouting.sound _ _ [288,5,24,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22940 c22940
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22940_3
  · exact m22940_33
  · exact m22940_34
  · exact m22940_65
  · exact m22940_66
  · exact m22940_96
  · exact u17112

def b22941 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 248 232 232 232 488), lower := (rows 289 7 37 26 16 32 64 128 256), losses := [] }

theorem u22941 : Upper (D 8) (R 8) [288,5,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22942 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 42 216 248 216 216 472), lower := (rows 289 7 37 42 16 32 64 128 256), losses := [] }

theorem u22942 : Upper (D 8) (R 8) [288,5,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22943 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 74 248 248 248 248 504), lower := (rows 289 7 37 74 16 32 64 128 256), losses := [] }

theorem u22943 : Upper (D 8) (R 8) [288,5,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22944 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 104 218 250 218 218 474), lower := (rows 289 7 37 104 16 32 64 128 256), losses := [] }

theorem u22944 : Upper (D 8) (R 8) [288,5,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22945 : PairBound 9 := { available := 250, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 200 250 250 250 250 506), lower := (rows 289 7 37 200 16 32 64 128 256), losses := [] }

theorem u22945 : Upper (D 8) (R 8) [288,5,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22946 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 248 248 248 248 504), lower := (rows 289 7 38 73 16 32 64 128 256), losses := [] }

theorem u22946 : Upper (D 8) (R 8) [288,5,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22947 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 104 217 249 217 217 473), lower := (rows 289 7 38 104 16 32 64 128 256), losses := [] }

theorem u22947 : Upper (D 8) (R 8) [288,5,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22948 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 200 249 249 249 249 505), lower := (rows 289 7 38 200 16 32 64 128 256), losses := [] }

theorem u22948 : Upper (D 8) (R 8) [288,5,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22949 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 25 242 226 226 226 482), lower := (rows 289 7 44 25 16 32 64 128 256), losses := [] }

theorem u22949 : Upper (D 8) (R 8) [288,5,40,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22950 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22950 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22950 : Upper (D 8) (R 8) [288,5,40,18] 13 := by
  apply FastRouting.sound _ _ [288,5,40,18] 13 (by decide) (choices 2) [33,65,96,192] r22950 c22950
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17146
  · exact u17147
  · exact u17148
  · exact u17149

def b22951 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 44 41 210 242 210 210 466), lower := (rows 289 7 44 41 16 32 64 128 256), losses := [] }

theorem u22951 : Upper (D 8) (R 8) [288,5,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22952 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 44 42 209 241 209 209 465), lower := (rows 289 7 44 42 16 32 64 128 256), losses := [] }

theorem u22952 : Upper (D 8) (R 8) [288,5,40,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22953 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 56 211 227 195 195 451), lower := (rows 289 7 44 56 16 32 64 128 256), losses := [] }

theorem u22953 : Upper (D 8) (R 8) [288,5,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22954 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 73 242 242 242 242 498), lower := (rows 289 7 44 73 16 32 64 128 256), losses := [] }

theorem u22954 : Upper (D 8) (R 8) [288,5,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22955 : Route 9 := (fun mask => (mask,id))

def c22955 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22955 : Upper (D 8) (R 8) [288,5,40,66] 13 := by
  apply FastRouting.sound _ _ [288,5,40,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22955 c22955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u17163
  · exact u17164
  · exact u17165
  · exact u17166
  · exact u17167
  · exact u17168

theorem m22956_3 : Upper (D 8) (R 8) [288,5,40,80,3] 13 :=
  permutation_upper _ _ _ [288,5,9,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17051

def r22956 : Route 9 := (fun mask => (mask,id))

def c22956 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22956 : Upper (D 8) (R 8) [288,5,40,80] 13 := by
  apply FastRouting.sound _ _ [288,5,40,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r22956 c22956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22956_3
  · exact u17169
  · exact u17170
  · exact u17171
  · exact u17172
  · exact u17173
  · exact u17174
  · exact u17175
  · exact u17176
  · exact u17177

def b22957 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 104 211 243 211 211 467), lower := (rows 289 7 44 104 16 32 64 128 256), losses := [] }

theorem u22957 : Upper (D 8) (R 8) [288,5,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22958_3 : Upper (D 8) (R 8) [288,5,40,192,3] 13 :=
  permutation_upper _ _ _ [288,5,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17052

def r22958 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22958 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22958 : Upper (D 8) (R 8) [288,5,40,192] 13 := by
  apply FastRouting.sound _ _ [288,5,40,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22958 c22958
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22958_3
  · exact u17183
  · exact u17184
  · exact u17185
  · exact u17186
  · exact u17187
  · exact u17188

theorem m22959_9 : Upper (D 8) (R 8) [288,5,48,34,9] 13 :=
  permutation_upper _ _ _ [288,5,40,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17142

theorem m22959_65 : Upper (D 8) (R 8) [288,5,48,34,65] 13 :=
  permutation_upper _ _ _ [288,5,40,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17157

theorem m22959_72 : Upper (D 8) (R 8) [288,5,48,34,72] 13 :=
  permutation_upper _ _ _ [288,5,40,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17170

theorem m22959_192 : Upper (D 8) (R 8) [288,5,48,34,192] 13 :=
  permutation_upper _ _ _ [288,5,40,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17184

def r22959 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22959 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22959 : Upper (D 8) (R 8) [288,5,48,34] 13 := by
  apply FastRouting.sound _ _ [288,5,48,34] 13 (by decide) (choices 2) [9,65,72,192] r22959 c22959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22959_9
  · exact m22959_65
  · exact m22959_72
  · exact m22959_192

theorem m22960_10 : Upper (D 8) (R 8) [288,5,48,65,10] 13 :=
  permutation_upper _ _ _ [288,5,40,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17147

theorem m22960_34 : Upper (D 8) (R 8) [288,5,48,65,34] 13 :=
  permutation_upper _ _ _ [288,5,40,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17152

theorem m22960_40 : Upper (D 8) (R 8) [288,5,48,65,40] 13 :=
  permutation_upper _ _ _ [288,5,40,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17154

theorem m22960_66 : Upper (D 8) (R 8) [288,5,48,65,66] 13 :=
  permutation_upper _ _ _ [288,5,40,66,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17164

theorem m22960_72 : Upper (D 8) (R 8) [288,5,48,65,72] 13 :=
  permutation_upper _ _ _ [288,5,40,80,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17171

theorem m22960_96 : Upper (D 8) (R 8) [288,5,48,65,96] 13 :=
  permutation_upper _ _ _ [288,5,40,96,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17178

theorem m22960_130 : Upper (D 8) (R 8) [288,5,48,65,130] 13 :=
  permutation_upper _ _ _ [288,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17166

theorem m22960_136 : Upper (D 8) (R 8) [288,5,48,65,136] 13 :=
  permutation_upper _ _ _ [288,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17174

theorem m22960_160 : Upper (D 8) (R 8) [288,5,48,65,160] 13 :=
  permutation_upper _ _ _ [288,5,40,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17180

theorem m22960_192 : Upper (D 8) (R 8) [288,5,48,65,192] 13 :=
  permutation_upper _ _ _ [288,5,40,192,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17185

def r22960 : Route 9 := (fun mask => (mask,id))

def c22960 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22960 : Upper (D 8) (R 8) [288,5,48,65] 13 := by
  apply FastRouting.sound _ _ [288,5,48,65] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r22960 c22960
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22960_10
  · exact m22960_34
  · exact m22960_40
  · exact m22960_66
  · exact m22960_72
  · exact m22960_96
  · exact m22960_130
  · exact m22960_136
  · exact m22960_160
  · exact m22960_192

theorem m22961_9 : Upper (D 8) (R 8) [288,5,48,66,9] 13 :=
  permutation_upper _ _ _ [288,5,40,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17143

theorem m22961_33 : Upper (D 8) (R 8) [288,5,48,66,33] 13 :=
  permutation_upper _ _ _ [288,5,40,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17150

theorem m22961_40 : Upper (D 8) (R 8) [288,5,48,66,40] 13 :=
  permutation_upper _ _ _ [288,5,40,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17155

theorem m22961_65 : Upper (D 8) (R 8) [288,5,48,66,65] 13 :=
  permutation_upper _ _ _ [288,5,40,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17158

theorem m22961_72 : Upper (D 8) (R 8) [288,5,48,66,72] 13 :=
  permutation_upper _ _ _ [288,5,40,80,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17172

theorem m22961_96 : Upper (D 8) (R 8) [288,5,48,66,96] 13 :=
  permutation_upper _ _ _ [288,5,40,96,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17179

theorem m22961_129 : Upper (D 8) (R 8) [288,5,48,66,129] 13 :=
  permutation_upper _ _ _ [288,5,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17160

theorem m22961_136 : Upper (D 8) (R 8) [288,5,48,66,136] 13 :=
  permutation_upper _ _ _ [288,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17175

theorem m22961_160 : Upper (D 8) (R 8) [288,5,48,66,160] 13 :=
  permutation_upper _ _ _ [288,5,40,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17181

theorem m22961_192 : Upper (D 8) (R 8) [288,5,48,66,192] 13 :=
  permutation_upper _ _ _ [288,5,40,192,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17186

def r22961 : Route 9 := (fun mask => (mask,id))

def c22961 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22961 : Upper (D 8) (R 8) [288,5,48,66] 13 := by
  apply FastRouting.sound _ _ [288,5,48,66] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22961 c22961
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22961_9
  · exact m22961_33
  · exact m22961_40
  · exact m22961_65
  · exact m22961_72
  · exact m22961_96
  · exact m22961_129
  · exact m22961_136
  · exact m22961_160
  · exact m22961_192

theorem m22962_3 : Upper (D 8) (R 8) [288,5,48,96,3] 13 :=
  permutation_upper _ _ _ [288,5,9,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17049

theorem m22962_9 : Upper (D 8) (R 8) [288,5,48,96,9] 13 :=
  permutation_upper _ _ _ [288,5,40,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17144

theorem m22962_10 : Upper (D 8) (R 8) [288,5,48,96,10] 13 :=
  permutation_upper _ _ _ [288,5,40,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17148

theorem m22962_65 : Upper (D 8) (R 8) [288,5,48,96,65] 13 :=
  permutation_upper _ _ _ [288,5,40,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17159

theorem m22962_66 : Upper (D 8) (R 8) [288,5,48,96,66] 13 :=
  permutation_upper _ _ _ [288,5,40,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17165

theorem m22962_72 : Upper (D 8) (R 8) [288,5,48,96,72] 13 :=
  permutation_upper _ _ _ [288,5,40,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17173

theorem m22962_129 : Upper (D 8) (R 8) [288,5,48,96,129] 13 :=
  permutation_upper _ _ _ [288,5,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17161

theorem m22962_130 : Upper (D 8) (R 8) [288,5,48,96,130] 13 :=
  permutation_upper _ _ _ [288,5,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17167

theorem m22962_136 : Upper (D 8) (R 8) [288,5,48,96,136] 13 :=
  permutation_upper _ _ _ [288,5,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17176

theorem m22962_192 : Upper (D 8) (R 8) [288,5,48,96,192] 13 :=
  permutation_upper _ _ _ [288,5,40,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17187

def r22962 : Route 9 := (fun mask => (mask,id))

def c22962 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22962 : Upper (D 8) (R 8) [288,5,48,96] 13 := by
  apply FastRouting.sound _ _ [288,5,48,96] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r22962 c22962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22962_3
  · exact m22962_9
  · exact m22962_10
  · exact m22962_65
  · exact m22962_66
  · exact m22962_72
  · exact m22962_129
  · exact m22962_130
  · exact m22962_136
  · exact m22962_192

theorem m22963_3 : Upper (D 8) (R 8) [288,5,48,192,3] 13 :=
  permutation_upper _ _ _ [288,5,9,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17050

theorem m22963_9 : Upper (D 8) (R 8) [288,5,48,192,9] 13 :=
  permutation_upper _ _ _ [288,5,40,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17145

theorem m22963_10 : Upper (D 8) (R 8) [288,5,48,192,10] 13 :=
  permutation_upper _ _ _ [288,5,40,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17149

theorem m22963_33 : Upper (D 8) (R 8) [288,5,48,192,33] 13 :=
  permutation_upper _ _ _ [288,5,40,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17151

theorem m22963_34 : Upper (D 8) (R 8) [288,5,48,192,34] 13 :=
  permutation_upper _ _ _ [288,5,40,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17153

theorem m22963_40 : Upper (D 8) (R 8) [288,5,48,192,40] 13 :=
  permutation_upper _ _ _ [288,5,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17156

theorem m22963_65 : Upper (D 8) (R 8) [288,5,48,192,65] 13 :=
  permutation_upper _ _ _ [288,5,40,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17162

theorem m22963_66 : Upper (D 8) (R 8) [288,5,48,192,66] 13 :=
  permutation_upper _ _ _ [288,5,40,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17168

theorem m22963_72 : Upper (D 8) (R 8) [288,5,48,192,72] 13 :=
  permutation_upper _ _ _ [288,5,40,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17177

theorem m22963_96 : Upper (D 8) (R 8) [288,5,48,192,96] 13 :=
  permutation_upper _ _ _ [288,5,40,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17182

theorem m22963_192 : Upper (D 8) (R 8) [288,5,48,192,192] 13 :=
  permutation_upper _ _ _ [288,5,40,192,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17188

def r22963 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22963 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22963 : Upper (D 8) (R 8) [288,5,48,192] 13 := by
  apply FastRouting.sound _ _ [288,5,48,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r22963 c22963
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22963_3
  · exact m22963_9
  · exact m22963_10
  · exact m22963_33
  · exact m22963_34
  · exact m22963_40
  · exact m22963_65
  · exact m22963_66
  · exact m22963_72
  · exact m22963_96
  · exact m22963_192

def b22964 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 248 232 232 232 488), lower := (rows 289 7 69 26 16 32 64 128 256), losses := [] }

theorem u22964 : Upper (D 8) (R 8) [288,5,65,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22965 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 248 248 248 248 504), lower := (rows 289 7 69 42 16 32 64 128 256), losses := [] }

theorem u22965 : Upper (D 8) (R 8) [288,5,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22966 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 74 184 184 248 184 440), lower := (rows 289 7 69 74 16 32 64 128 256), losses := [] }

theorem u22966 : Upper (D 8) (R 8) [288,5,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22967 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 104 186 186 250 186 442), lower := (rows 289 7 69 104 16 32 64 128 256), losses := [] }

theorem u22967 : Upper (D 8) (R 8) [288,5,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22968 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 138 248 248 248 248 504), lower := (rows 289 7 69 138 16 32 64 128 256), losses := [] }

theorem u22968 : Upper (D 8) (R 8) [288,5,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22969 : PairBound 9 := { available := 250, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 168 250 250 250 250 506), lower := (rows 289 7 69 168 16 32 64 128 256), losses := [] }

theorem u22969 : Upper (D 8) (R 8) [288,5,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22970 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 200 186 186 250 186 442), lower := (rows 289 7 69 200 16 32 64 128 256), losses := [] }

theorem u22970 : Upper (D 8) (R 8) [288,5,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22971 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 70 25 248 232 232 232 488), lower := (rows 289 7 70 25 16 32 64 128 256), losses := [] }

theorem u22971 : Upper (D 8) (R 8) [288,5,66,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22972 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 70 41 248 248 248 248 504), lower := (rows 289 7 70 41 16 32 64 128 256), losses := [] }

theorem u22972 : Upper (D 8) (R 8) [288,5,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22973_9 : Upper (D 8) (R 8) [288,5,66,48,9] 13 :=
  permutation_upper _ _ _ [288,5,34,17,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17129

theorem m22973_33 : Upper (D 8) (R 8) [288,5,66,48,33] 13 :=
  permutation_upper _ _ _ [288,5,66,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17220

def r22973 : Route 9 := (fun mask => (mask,id))

def c22973 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22973 : Upper (D 8) (R 8) [288,5,66,48] 13 := by
  apply FastRouting.sound _ _ [288,5,66,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22973 c22973
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22973_9
  · exact m22973_33
  · exact u17223
  · exact u17224
  · exact u17225
  · exact u17226
  · exact u17227
  · exact u17228
  · exact u17229
  · exact u17230

def b22974 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 73 184 184 248 184 440), lower := (rows 289 7 70 73 16 32 64 128 256), losses := [] }

theorem u22974 : Upper (D 8) (R 8) [288,5,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22975 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 88 185 169 233 169 425), lower := (rows 289 7 70 88 16 32 64 128 256), losses := [] }

theorem u22975 : Upper (D 8) (R 8) [288,5,66,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22976 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 104 185 185 249 185 441), lower := (rows 289 7 70 104 16 32 64 128 256), losses := [] }

theorem u22976 : Upper (D 8) (R 8) [288,5,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22977 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 70 137 248 248 248 248 504), lower := (rows 289 7 70 137 16 32 64 128 256), losses := [] }

theorem u22977 : Upper (D 8) (R 8) [288,5,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22978_9 : Upper (D 8) (R 8) [288,5,66,144,9] 13 :=
  permutation_upper _ _ _ [288,5,66,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17217

theorem m22978_33 : Upper (D 8) (R 8) [288,5,66,144,33] 13 :=
  permutation_upper _ _ _ [288,5,66,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17221

theorem m22978_40 : Upper (D 8) (R 8) [288,5,66,144,40] 13 :=
  permutation_upper _ _ _ [288,5,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17228

theorem m22978_65 : Upper (D 8) (R 8) [288,5,66,144,65] 13 :=
  permutation_upper _ _ _ [288,5,66,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17231

theorem m22978_72 : Upper (D 8) (R 8) [288,5,66,144,72] 13 :=
  permutation_upper _ _ _ [288,5,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17234

theorem m22978_96 : Upper (D 8) (R 8) [288,5,66,144,96] 13 :=
  permutation_upper _ _ _ [288,5,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17237

theorem m22978_129 : Upper (D 8) (R 8) [288,5,66,144,129] 13 :=
  permutation_upper _ _ _ [288,5,66,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17239

def r22978 : Route 9 := (fun mask => (mask,id))

def c22978 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22978 : Upper (D 8) (R 8) [288,5,66,144] 13 := by
  apply FastRouting.sound _ _ [288,5,66,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22978 c22978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22978_9
  · exact m22978_33
  · exact m22978_40
  · exact m22978_65
  · exact m22978_72
  · exact m22978_96
  · exact m22978_129
  · exact u17242
  · exact u17243
  · exact u17244

theorem m22979_9 : Upper (D 8) (R 8) [288,5,66,160,9] 13 :=
  permutation_upper _ _ _ [288,5,66,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17218

theorem m22979_33 : Upper (D 8) (R 8) [288,5,66,160,33] 13 :=
  permutation_upper _ _ _ [288,5,66,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17222

theorem m22979_40 : Upper (D 8) (R 8) [288,5,66,160,40] 13 :=
  permutation_upper _ _ _ [288,5,66,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17229

theorem m22979_65 : Upper (D 8) (R 8) [288,5,66,160,65] 13 :=
  permutation_upper _ _ _ [288,5,66,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17232

theorem m22979_72 : Upper (D 8) (R 8) [288,5,66,160,72] 13 :=
  permutation_upper _ _ _ [288,5,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17235

theorem m22979_96 : Upper (D 8) (R 8) [288,5,66,160,96] 13 :=
  permutation_upper _ _ _ [288,5,66,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17238

theorem m22979_129 : Upper (D 8) (R 8) [288,5,66,160,129] 13 :=
  permutation_upper _ _ _ [288,5,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17240

theorem m22979_136 : Upper (D 8) (R 8) [288,5,66,160,136] 13 :=
  permutation_upper _ _ _ [288,5,66,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17243

def r22979 : Route 9 := (fun mask => (mask,id))

def c22979 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22979 : Upper (D 8) (R 8) [288,5,66,160] 13 := by
  apply FastRouting.sound _ _ [288,5,66,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22979 c22979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22979_9
  · exact m22979_33
  · exact m22979_40
  · exact m22979_65
  · exact m22979_72
  · exact m22979_96
  · exact m22979_129
  · exact m22979_136
  · exact u17245
  · exact u17246

#print axioms u22979
end Delivery.IrregularNine14.P08
