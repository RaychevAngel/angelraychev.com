import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0133
import IrregularNine14P08C0134
import IrregularNine14P08C0135
import IrregularNine14P08C0136

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r19140 : Route 9 := (fun mask => (mask,id))

def c19140 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19140 : Upper (D 8) (R 8) [6,96,264,48] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19140 c19140
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8013
  · exact u8014
  · exact u8015
  · exact u8016
  · exact u8017
  · exact u8018

def b19141 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 268 73 177 177 241 177 433), lower := (rows 7 98 268 73 16 32 64 128 256), losses := [] }

theorem u19141 : Upper (D 8) (R 8) [6,96,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19142 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 268 88 177 161 225 161 417), lower := (rows 7 98 268 88 16 32 64 128 256), losses := [] }

theorem u19142 : Upper (D 8) (R 8) [6,96,264,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19143 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 268 104 177 177 241 177 433), lower := (rows 7 98 268 104 16 32 64 128 256), losses := [] }

theorem u19143 : Upper (D 8) (R 8) [6,96,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19144 : Route 9 := (fun mask => (mask,id))

def c19144 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19144 : Upper (D 8) (R 8) [6,96,264,129] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19144 c19144
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8019
  · exact u8020
  · exact u8021
  · exact u8022
  · exact u8023
  · exact u8024

def r19145 : Route 9 := (fun mask => (mask,id))

def c19145 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19145 : Upper (D 8) (R 8) [6,96,264,144] 13 := by
  apply FastRouting.sound _ _ [6,96,264,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19145 c19145
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8025
  · exact u8026
  · exact u8027
  · exact u8028
  · exact u8029
  · exact u8030

def r19146 : Route 9 := (fun mask => (mask,id))

def c19146 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19146 : Upper (D 8) (R 8) [6,96,264,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19146 c19146
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8031
  · exact u8032
  · exact u8033
  · exact u8034
  · exact u8035
  · exact u8036

def b19147 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 268 200 177 177 241 177 433), lower := (rows 7 98 268 200 16 32 64 128 256), losses := [] }

theorem u19147 : Upper (D 8) (R 8) [6,96,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19148 : Route 9 := (fun mask => (mask,id))

def c19148 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19148 : Upper (D 8) (R 8) [6,96,288,17] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19148 c19148
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8037
  · exact u8038
  · exact u8039
  · exact u8040
  · exact u8041
  · exact u8042
  · exact u8043
  · exact u8044
  · exact u8045
  · exact u8046

def b19149 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 292 41 217 249 217 217 473), lower := (rows 7 98 292 41 16 32 64 128 256), losses := [] }

theorem u19149 : Upper (D 8) (R 8) [6,96,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19150_9 : Upper (D 8) (R 8) [6,96,288,48,9] 13 :=
  permutation_upper _ _ _ [6,96,288,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8039

def r19150 : Route 9 := (fun mask => (mask,id))

def c19150 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19150 : Upper (D 8) (R 8) [6,96,288,48] 13 := by
  apply FastRouting.sound _ _ [6,96,288,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r19150 c19150
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19150_9
  · exact u8051
  · exact u8052
  · exact u8053
  · exact u8054
  · exact u8055

def b19151 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 292 73 185 185 249 185 441), lower := (rows 7 98 292 73 16 32 64 128 256), losses := [] }

theorem u19151 : Upper (D 8) (R 8) [6,96,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19152_9 : Upper (D 8) (R 8) [6,96,288,80,9] 13 :=
  permutation_upper _ _ _ [6,96,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8041

theorem m19152_33 : Upper (D 8) (R 8) [6,96,288,80,33] 13 :=
  permutation_upper _ _ _ [6,96,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8047

theorem m19152_40 : Upper (D 8) (R 8) [6,96,288,80,40] 13 :=
  permutation_upper _ _ _ [6,96,288,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8052

def r19152 : Route 9 := (fun mask => (mask,id))

def c19152 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19152 : Upper (D 8) (R 8) [6,96,288,80] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19152 c19152
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19152_9
  · exact m19152_33
  · exact m19152_40
  · exact u8059
  · exact u8060
  · exact u8061

def b19153 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 292 104 153 185 217 153 409), lower := (rows 7 98 292 104 16 32 64 128 256), losses := [] }

theorem u19153 : Upper (D 8) (R 8) [6,96,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19154_9 : Upper (D 8) (R 8) [6,96,288,129,9] 13 :=
  permutation_upper _ _ _ [6,96,288,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8043

theorem m19154_33 : Upper (D 8) (R 8) [6,96,288,129,33] 13 :=
  permutation_upper _ _ _ [6,96,288,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8048

theorem m19154_40 : Upper (D 8) (R 8) [6,96,288,129,40] 13 :=
  permutation_upper _ _ _ [6,96,288,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8053

theorem m19154_65 : Upper (D 8) (R 8) [6,96,288,129,65] 13 :=
  permutation_upper _ _ _ [6,96,288,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8056

theorem m19154_72 : Upper (D 8) (R 8) [6,96,288,129,72] 13 :=
  permutation_upper _ _ _ [6,96,288,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8059

theorem m19154_96 : Upper (D 8) (R 8) [6,96,288,129,96] 13 :=
  permutation_upper _ _ _ [6,96,288,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8062

def r19154 : Route 9 := (fun mask => (mask,id))

def c19154 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19154 : Upper (D 8) (R 8) [6,96,288,129] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19154 c19154
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19154_9
  · exact m19154_33
  · exact m19154_40
  · exact m19154_65
  · exact m19154_72
  · exact m19154_96
  · exact u8064
  · exact u8065
  · exact u8066
  · exact u8067

theorem m19155_9 : Upper (D 8) (R 8) [6,96,288,144,9] 13 :=
  permutation_upper _ _ _ [6,96,288,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8044

theorem m19155_33 : Upper (D 8) (R 8) [6,96,288,144,33] 13 :=
  permutation_upper _ _ _ [6,96,288,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8049

theorem m19155_40 : Upper (D 8) (R 8) [6,96,288,144,40] 13 :=
  permutation_upper _ _ _ [6,96,288,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8054

theorem m19155_65 : Upper (D 8) (R 8) [6,96,288,144,65] 13 :=
  permutation_upper _ _ _ [6,96,288,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8057

theorem m19155_72 : Upper (D 8) (R 8) [6,96,288,144,72] 13 :=
  permutation_upper _ _ _ [6,96,288,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8060

theorem m19155_96 : Upper (D 8) (R 8) [6,96,288,144,96] 13 :=
  permutation_upper _ _ _ [6,96,288,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8063

theorem m19155_129 : Upper (D 8) (R 8) [6,96,288,144,129] 13 :=
  permutation_upper _ _ _ [6,96,288,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8065

def r19155 : Route 9 := (fun mask => (mask,id))

def c19155 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19155 : Upper (D 8) (R 8) [6,96,288,144] 13 := by
  apply FastRouting.sound _ _ [6,96,288,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19155 c19155
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19155_9
  · exact m19155_33
  · exact m19155_40
  · exact m19155_65
  · exact m19155_72
  · exact m19155_96
  · exact m19155_129
  · exact u8068
  · exact u8069
  · exact u8070

theorem m19156_9 : Upper (D 8) (R 8) [6,96,288,160,9] 13 :=
  permutation_upper _ _ _ [6,96,288,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8045

theorem m19156_65 : Upper (D 8) (R 8) [6,96,288,160,65] 13 :=
  permutation_upper _ _ _ [6,96,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8058

theorem m19156_72 : Upper (D 8) (R 8) [6,96,288,160,72] 13 :=
  permutation_upper _ _ _ [6,96,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8061

theorem m19156_129 : Upper (D 8) (R 8) [6,96,288,160,129] 13 :=
  permutation_upper _ _ _ [6,96,288,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8066

theorem m19156_136 : Upper (D 8) (R 8) [6,96,288,160,136] 13 :=
  permutation_upper _ _ _ [6,96,288,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8069

def r19156 : Route 9 := (fun mask => (mask,id))

def c19156 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19156 : Upper (D 8) (R 8) [6,96,288,160] 13 := by
  apply FastRouting.sound _ _ [6,96,288,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r19156 c19156
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19156_9
  · exact m19156_65
  · exact m19156_72
  · exact m19156_129
  · exact m19156_136
  · exact u8071

theorem m19157_9 : Upper (D 8) (R 8) [6,96,288,192,9] 13 :=
  permutation_upper _ _ _ [6,96,288,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8046

theorem m19157_33 : Upper (D 8) (R 8) [6,96,288,192,33] 13 :=
  permutation_upper _ _ _ [6,96,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8050

theorem m19157_40 : Upper (D 8) (R 8) [6,96,288,192,40] 13 :=
  permutation_upper _ _ _ [6,96,288,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8055

theorem m19157_129 : Upper (D 8) (R 8) [6,96,288,192,129] 13 :=
  permutation_upper _ _ _ [6,96,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8067

theorem m19157_136 : Upper (D 8) (R 8) [6,96,288,192,136] 13 :=
  permutation_upper _ _ _ [6,96,288,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8070

theorem m19157_160 : Upper (D 8) (R 8) [6,96,288,192,160] 13 :=
  permutation_upper _ _ _ [6,96,288,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8071

def r19157 : Route 9 := (fun mask => (mask,id))

def c19157 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19157 : Upper (D 8) (R 8) [6,96,288,192] 13 := by
  apply FastRouting.sound _ _ [6,96,288,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19157 c19157
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19157_9
  · exact m19157_33
  · exact m19157_40
  · exact m19157_129
  · exact m19157_136
  · exact m19157_160

def r19158 : Route 9 := (fun mask => (mask,id))

def c19158 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19158 : Upper (D 8) (R 8) [6,96,384,17] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19158 c19158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8072
  · exact u8073
  · exact u8074
  · exact u8075
  · exact u8076
  · exact u8077
  · exact u8078
  · exact u8079
  · exact u8080
  · exact u8081

theorem m19159_9 : Upper (D 8) (R 8) [6,96,384,33,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8073

def r19159 : Route 9 := (fun mask => (mask,id))

def c19159 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19159 : Upper (D 8) (R 8) [6,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19159 c19159
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19159_9
  · exact u8082
  · exact u8083
  · exact u8084
  · exact u8085
  · exact u8086
  · exact u8087
  · exact u8088
  · exact u8089
  · exact u8090

theorem m19160_9 : Upper (D 8) (R 8) [6,96,384,48,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8074

theorem m19160_33 : Upper (D 8) (R 8) [6,96,384,48,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8083

def r19160 : Route 9 := (fun mask => (mask,id))

def c19160 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19160 : Upper (D 8) (R 8) [6,96,384,48] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19160 c19160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19160_9
  · exact m19160_33
  · exact u8091
  · exact u8092
  · exact u8093
  · exact u8094
  · exact u8095
  · exact u8096
  · exact u8097
  · exact u8098

def b19161 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 388 73 185 185 249 185 441), lower := (rows 7 98 388 73 16 32 64 128 256), losses := [] }

theorem u19161 : Upper (D 8) (R 8) [6,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19162_9 : Upper (D 8) (R 8) [6,96,384,80,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8076

theorem m19162_33 : Upper (D 8) (R 8) [6,96,384,80,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8085

theorem m19162_40 : Upper (D 8) (R 8) [6,96,384,80,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8093

def r19162 : Route 9 := (fun mask => (mask,id))

def c19162 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19162 : Upper (D 8) (R 8) [6,96,384,80] 13 := by
  apply FastRouting.sound _ _ [6,96,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19162 c19162
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19162_9
  · exact m19162_33
  · exact m19162_40
  · exact u8101
  · exact u8102
  · exact u8103

def b19163 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 104 185 185 249 185 441), lower := (rows 7 98 388 104 16 32 64 128 256), losses := [] }

theorem u19163 : Upper (D 8) (R 8) [6,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19164 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 137 121 121 121 249 377), lower := (rows 7 98 388 137 16 32 64 128 256), losses := [] }

theorem u19164 : Upper (D 8) (R 8) [6,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19165_9 : Upper (D 8) (R 8) [6,96,384,144,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8079

theorem m19165_33 : Upper (D 8) (R 8) [6,96,384,144,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8088

theorem m19165_40 : Upper (D 8) (R 8) [6,96,384,144,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8096

theorem m19165_65 : Upper (D 8) (R 8) [6,96,384,144,65] 13 :=
  permutation_upper _ _ _ [6,96,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8099

theorem m19165_72 : Upper (D 8) (R 8) [6,96,384,144,72] 13 :=
  permutation_upper _ _ _ [6,96,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8102

theorem m19165_96 : Upper (D 8) (R 8) [6,96,384,144,96] 13 :=
  permutation_upper _ _ _ [6,96,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8104

def r19165 : Route 9 := (fun mask => (mask,id))

def c19165 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19165 : Upper (D 8) (R 8) [6,96,384,144] 13 := by
  apply FastRouting.sound _ _ [6,96,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19165 c19165
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19165_9
  · exact m19165_33
  · exact m19165_40
  · exact m19165_65
  · exact m19165_72
  · exact m19165_96

theorem m19166_9 : Upper (D 8) (R 8) [6,96,384,160,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8080

theorem m19166_33 : Upper (D 8) (R 8) [6,96,384,160,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8089

theorem m19166_40 : Upper (D 8) (R 8) [6,96,384,160,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8097

theorem m19166_65 : Upper (D 8) (R 8) [6,96,384,160,65] 13 :=
  permutation_upper _ _ _ [6,96,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8100

theorem m19166_72 : Upper (D 8) (R 8) [6,96,384,160,72] 13 :=
  permutation_upper _ _ _ [6,96,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8103

theorem m19166_96 : Upper (D 8) (R 8) [6,96,384,160,96] 13 :=
  permutation_upper _ _ _ [6,96,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8105

def r19166 : Route 9 := (fun mask => (mask,id))

def c19166 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19166 : Upper (D 8) (R 8) [6,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19166 c19166
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19166_9
  · exact m19166_33
  · exact m19166_40
  · exact m19166_65
  · exact m19166_72
  · exact m19166_96

theorem m19167_9 : Upper (D 8) (R 8) [6,96,384,192,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8081

theorem m19167_33 : Upper (D 8) (R 8) [6,96,384,192,33] 13 :=
  permutation_upper _ _ _ [6,96,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8090

theorem m19167_40 : Upper (D 8) (R 8) [6,96,384,192,40] 13 :=
  permutation_upper _ _ _ [6,96,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8098

def r19167 : Route 9 := (fun mask => (mask,id))

def c19167 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19167 : Upper (D 8) (R 8) [6,96,384,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,192] 13 (by decide) (choices 2) [9,33,40] r19167 c19167
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19167_9
  · exact m19167_33
  · exact m19167_40

def b19168 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 25 248 232 232 232 488), lower := (rows 7 194 261 25 16 32 64 128 256), losses := [] }

theorem u19168 : Upper (D 8) (R 8) [6,192,257,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19169 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 41 248 248 248 248 504), lower := (rows 7 194 261 41 16 32 64 128 256), losses := [] }

theorem u19169 : Upper (D 8) (R 8) [6,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19170_9 : Upper (D 8) (R 8) [6,192,257,48,9] 13 :=
  permutation_upper _ _ _ [6,192,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8106

theorem m19170_33 : Upper (D 8) (R 8) [6,192,257,48,33] 13 :=
  permutation_upper _ _ _ [6,192,257,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8109

def r19170 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19170 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19170 : Upper (D 8) (R 8) [6,192,257,48] 13 := by
  apply FastRouting.sound _ _ [6,192,257,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r19170 c19170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19170_9
  · exact m19170_33
  · exact u8112
  · exact u8113
  · exact u8114
  · exact u8115
  · exact u8116

def b19171 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 73 184 184 248 184 440), lower := (rows 7 194 261 73 16 32 64 128 256), losses := [] }

theorem u19171 : Upper (D 8) (R 8) [6,192,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19172_9 : Upper (D 8) (R 8) [6,192,257,80,9] 13 :=
  permutation_upper _ _ _ [6,192,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8107

theorem m19172_33 : Upper (D 8) (R 8) [6,192,257,80,33] 13 :=
  permutation_upper _ _ _ [6,192,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8110

theorem m19172_40 : Upper (D 8) (R 8) [6,192,257,80,40] 13 :=
  permutation_upper _ _ _ [6,192,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8114

theorem m19172_129 : Upper (D 8) (R 8) [6,192,257,80,129] 13 :=
  permutation_upper _ _ _ [6,192,257,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8117

def r19172 : Route 9 := (fun mask => (mask,id))

def c19172 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19172 : Upper (D 8) (R 8) [6,192,257,80] 13 := by
  apply FastRouting.sound _ _ [6,192,257,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19172 c19172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19172_9
  · exact m19172_33
  · exact m19172_40
  · exact m19172_129
  · exact u8119
  · exact u8120

theorem m19173_9 : Upper (D 8) (R 8) [6,192,257,96,9] 13 :=
  permutation_upper _ _ _ [6,192,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8108

theorem m19173_33 : Upper (D 8) (R 8) [6,192,257,96,33] 13 :=
  permutation_upper _ _ _ [6,192,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8111

theorem m19173_40 : Upper (D 8) (R 8) [6,192,257,96,40] 13 :=
  permutation_upper _ _ _ [6,192,257,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8115

theorem m19173_129 : Upper (D 8) (R 8) [6,192,257,96,129] 13 :=
  permutation_upper _ _ _ [6,192,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8118

theorem m19173_136 : Upper (D 8) (R 8) [6,192,257,96,136] 13 :=
  permutation_upper _ _ _ [6,192,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8120

def r19173 : Route 9 := (fun mask => (mask,id))

def c19173 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19173 : Upper (D 8) (R 8) [6,192,257,96] 13 := by
  apply FastRouting.sound _ _ [6,192,257,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19173 c19173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19173_9
  · exact m19173_33
  · exact m19173_40
  · exact m19173_129
  · exact m19173_136
  · exact u8121

def b19174 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 261 200 57 57 121 185 313), lower := (rows 7 194 261 200 16 32 64 128 256), losses := [] }

theorem u19174 : Upper (D 8) (R 8) [6,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19175 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19175 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19175 : Upper (D 8) (R 8) [6,192,264,17] 13 := by
  apply FastRouting.sound _ _ [6,192,264,17] 13 (by decide) (choices 2) [33,65,96,192] r19175 c19175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8122
  · exact u8123
  · exact u8124
  · exact u8125

def r19176 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19176 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19176 : Upper (D 8) (R 8) [6,192,264,33] 13 := by
  apply FastRouting.sound _ _ [6,192,264,33] 13 (by decide) (choices 2) [33,65,96,192] r19176 c19176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8126
  · exact u8127
  · exact u8128
  · exact u8129

def r19177 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19177 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19177 : Upper (D 8) (R 8) [6,192,264,48] 13 := by
  apply FastRouting.sound _ _ [6,192,264,48] 13 (by decide) (choices 2) [33,65,96,192] r19177 c19177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8130
  · exact u8131
  · exact u8132
  · exact u8133

def b19178 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 268 73 177 177 241 177 433), lower := (rows 7 194 268 73 16 32 64 128 256), losses := [] }

theorem u19178 : Upper (D 8) (R 8) [6,192,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19179 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 194 268 88 177 161 225 161 417), lower := (rows 7 194 268 88 16 32 64 128 256), losses := [] }

theorem u19179 : Upper (D 8) (R 8) [6,192,264,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19180 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 194 268 104 177 177 241 177 433), lower := (rows 7 194 268 104 16 32 64 128 256), losses := [] }

theorem u19180 : Upper (D 8) (R 8) [6,192,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19181 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 268 200 49 49 113 177 305), lower := (rows 7 194 268 200 16 32 64 128 256), losses := [] }

theorem u19181 : Upper (D 8) (R 8) [6,192,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19182 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19182 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19182 : Upper (D 8) (R 8) [6,192,288,17] 13 := by
  apply FastRouting.sound _ _ [6,192,288,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r19182 c19182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8134
  · exact u8135
  · exact u8136
  · exact u8137
  · exact u8138
  · exact u8139
  · exact u8140

theorem m19183_9 : Upper (D 8) (R 8) [6,192,288,33,9] 13 :=
  permutation_upper _ _ _ [6,192,288,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8135

def r19183 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19183 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19183 : Upper (D 8) (R 8) [6,192,288,33] 13 := by
  apply FastRouting.sound _ _ [6,192,288,33] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r19183 c19183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19183_9
  · exact u8141
  · exact u8142
  · exact u8143
  · exact u8144
  · exact u8145
  · exact u8146

theorem m19184_9 : Upper (D 8) (R 8) [6,192,288,48,9] 13 :=
  permutation_upper _ _ _ [6,192,288,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8136

theorem m19184_33 : Upper (D 8) (R 8) [6,192,288,48,33] 13 :=
  permutation_upper _ _ _ [6,192,288,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8142

def r19184 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19184 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19184 : Upper (D 8) (R 8) [6,192,288,48] 13 := by
  apply FastRouting.sound _ _ [6,192,288,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r19184 c19184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19184_9
  · exact m19184_33
  · exact u8147
  · exact u8148
  · exact u8149
  · exact u8150
  · exact u8151

def b19185 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 292 73 185 185 249 185 441), lower := (rows 7 194 292 73 16 32 64 128 256), losses := [] }

theorem u19185 : Upper (D 8) (R 8) [6,192,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19186_9 : Upper (D 8) (R 8) [6,192,288,80,9] 13 :=
  permutation_upper _ _ _ [6,192,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8138

theorem m19186_33 : Upper (D 8) (R 8) [6,192,288,80,33] 13 :=
  permutation_upper _ _ _ [6,192,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8144

theorem m19186_40 : Upper (D 8) (R 8) [6,192,288,80,40] 13 :=
  permutation_upper _ _ _ [6,192,288,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8149

theorem m19186_129 : Upper (D 8) (R 8) [6,192,288,80,129] 13 :=
  permutation_upper _ _ _ [6,192,288,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8152

def r19186 : Route 9 := (fun mask => (mask,id))

def c19186 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19186 : Upper (D 8) (R 8) [6,192,288,80] 13 := by
  apply FastRouting.sound _ _ [6,192,288,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19186 c19186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19186_9
  · exact m19186_33
  · exact m19186_40
  · exact m19186_129
  · exact u8154
  · exact u8155

theorem m19187_9 : Upper (D 8) (R 8) [6,192,288,96,9] 13 :=
  permutation_upper _ _ _ [6,192,288,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8139

theorem m19187_33 : Upper (D 8) (R 8) [6,192,288,96,33] 13 :=
  permutation_upper _ _ _ [6,192,288,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8145

theorem m19187_40 : Upper (D 8) (R 8) [6,192,288,96,40] 13 :=
  permutation_upper _ _ _ [6,192,288,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8150

theorem m19187_129 : Upper (D 8) (R 8) [6,192,288,96,129] 13 :=
  permutation_upper _ _ _ [6,192,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8153

theorem m19187_136 : Upper (D 8) (R 8) [6,192,288,96,136] 13 :=
  permutation_upper _ _ _ [6,192,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8155

def r19187 : Route 9 := (fun mask => (mask,id))

def c19187 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19187 : Upper (D 8) (R 8) [6,192,288,96] 13 := by
  apply FastRouting.sound _ _ [6,192,288,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19187 c19187
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19187_9
  · exact m19187_33
  · exact m19187_40
  · exact m19187_129
  · exact m19187_136
  · exact u8156

def b19188 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 292 200 57 57 121 185 313), lower := (rows 7 194 292 200 16 32 64 128 256), losses := [] }

theorem u19188 : Upper (D 8) (R 8) [6,192,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19189 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 28 41 496 480 480 480 480), lower := (rows 35 7 28 41 16 32 64 128 256), losses := [] }

theorem u19189 : Upper (D 8) (R 8) [34,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19190 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 73 496 480 480 480 480), lower := (rows 35 7 28 73 16 32 64 128 256), losses := [] }

theorem u19190 : Upper (D 8) (R 8) [34,5,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19191_33 : Upper (D 8) (R 8) [34,5,24,96,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8157

theorem m19191_65 : Upper (D 8) (R 8) [34,5,24,96,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8161

theorem m19191_129 : Upper (D 8) (R 8) [34,5,24,96,129] 13 :=
  permutation_upper _ _ _ [34,5,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8162

def r19191 : Route 9 := (fun mask => (mask,id))

def c19191 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19191 : Upper (D 8) (R 8) [34,5,24,96] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19191 c19191
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19191_33
  · exact m19191_65
  · exact u8167
  · exact m19191_129
  · exact u8168
  · exact u8169
  · exact u8170
  · exact u8171
  · exact u8172
  · exact u8173

theorem m19192_33 : Upper (D 8) (R 8) [34,5,24,192,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8158

theorem m19192_65 : Upper (D 8) (R 8) [34,5,24,192,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8163

theorem m19192_96 : Upper (D 8) (R 8) [34,5,24,192,96] 13 :=
  permutation_upper _ _ _ [34,5,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8169

def r19192 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19192 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19192 : Upper (D 8) (R 8) [34,5,24,192] 13 := by
  apply FastRouting.sound _ _ [34,5,24,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r19192 c19192
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19192_33
  · exact m19192_65
  · exact m19192_96
  · exact u8174
  · exact u8175
  · exact u8176
  · exact u8177

def b19193 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 265 240 224 224 224 480), lower := (rows 35 7 28 265 16 32 64 128 256), losses := [] }

theorem u19193 : Upper (D 8) (R 8) [34,5,24,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19194_33 : Upper (D 8) (R 8) [34,5,24,288,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8159

theorem m19194_65 : Upper (D 8) (R 8) [34,5,24,288,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8164

theorem m19194_96 : Upper (D 8) (R 8) [34,5,24,288,96] 13 :=
  permutation_upper _ _ _ [34,5,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8171

theorem m19194_192 : Upper (D 8) (R 8) [34,5,24,288,192] 13 :=
  permutation_upper _ _ _ [34,5,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8176

def r19194 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19194 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19194 : Upper (D 8) (R 8) [34,5,24,288] 13 := by
  apply FastRouting.sound _ _ [34,5,24,288] 13 (by decide) (choices 2) [33,65,96,192] r19194 c19194
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m19194_33
  · exact m19194_65
  · exact m19194_96
  · exact m19194_192

theorem m19195_33 : Upper (D 8) (R 8) [34,5,24,320,33] 13 :=
  permutation_upper _ _ _ [34,5,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8160

theorem m19195_65 : Upper (D 8) (R 8) [34,5,24,320,65] 13 :=
  permutation_upper _ _ _ [34,5,24,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8165

theorem m19195_96 : Upper (D 8) (R 8) [34,5,24,320,96] 13 :=
  permutation_upper _ _ _ [34,5,24,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8172

theorem m19195_129 : Upper (D 8) (R 8) [34,5,24,320,129] 13 :=
  permutation_upper _ _ _ [34,5,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8166

theorem m19195_160 : Upper (D 8) (R 8) [34,5,24,320,160] 13 :=
  permutation_upper _ _ _ [34,5,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8173

theorem m19195_192 : Upper (D 8) (R 8) [34,5,24,320,192] 13 :=
  permutation_upper _ _ _ [34,5,24,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8177

def r19195 : Route 9 := (fun mask => (mask,id))

def c19195 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19195 : Upper (D 8) (R 8) [34,5,24,320] 13 := by
  apply FastRouting.sound _ _ [34,5,24,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19195 c19195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19195_33
  · exact m19195_65
  · exact m19195_96
  · exact m19195_129
  · exact m19195_160
  · exact m19195_192

def b19196 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 25 496 480 480 480 480), lower := (rows 35 7 76 25 16 32 64 128 256), losses := [] }

theorem u19196 : Upper (D 8) (R 8) [34,5,72,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19197 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 41 496 496 496 496 496), lower := (rows 35 7 76 41 16 32 64 128 256), losses := [] }

theorem u19197 : Upper (D 8) (R 8) [34,5,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19198 : Route 9 := (fun mask => (mask,id))

def c19198 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19198 : Upper (D 8) (R 8) [34,5,72,48] 13 := by
  apply FastRouting.sound _ _ [34,5,72,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19198 c19198
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8178
  · exact u8179
  · exact u8180
  · exact u8181
  · exact u8182
  · exact u8183
  · exact u8184
  · exact u8185
  · exact u8186
  · exact u8187

def b19199 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 73 432 432 496 432 432), lower := (rows 35 7 76 73 16 32 64 128 256), losses := [] }

theorem u19199 : Upper (D 8) (R 8) [34,5,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u19199
end Delivery.IrregularNine14.P08
