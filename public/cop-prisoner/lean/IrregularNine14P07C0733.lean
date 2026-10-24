import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0680
import IrregularNine14P07C0681
import IrregularNine14P07C0682
import IrregularNine14P07C0683
import IrregularNine14P07C0684
import IrregularNine14P07C0685
import IrregularNine14P07C0686
import IrregularNine14P07C0687
import IrregularNine14P07C0688

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b43980 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 386 44 138 87 119 87 215 343), lower := (rows 97 386 44 138 16 32 64 128 256), losses := [] }

theorem u43980 : Upper (D 7) (R 7) [96,384,40,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43981 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7),(1,5),(4,5),(4,7)], upper := (rows 97 386 44 140 83 115 83 211 339), lower := (rows 97 386 44 140 16 32 64 128 256), losses := [] }

theorem u43981 : Upper (D 7) (R 7) [96,384,40,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43982_3 : Upper (D 7) (R 7) [96,384,40,144,3] 13 :=
  permutation_upper _ _ _ [96,384,3,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40844

theorem m43982_5 : Upper (D 7) (R 7) [96,384,40,144,5] 13 :=
  permutation_upper _ _ _ [96,384,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40900

theorem m43982_6 : Upper (D 7) (R 7) [96,384,40,144,6] 13 :=
  permutation_upper _ _ _ [96,384,10,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40954

theorem m43982_65 : Upper (D 7) (R 7) [96,384,40,144,65] 13 :=
  permutation_upper _ _ _ [96,384,33,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40993

theorem m43982_66 : Upper (D 7) (R 7) [96,384,40,144,66] 13 :=
  permutation_upper _ _ _ [96,384,34,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41001

theorem m43982_68 : Upper (D 7) (R 7) [96,384,40,144,68] 13 :=
  permutation_upper _ _ _ [96,384,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41006

def r43982 : Route 9 := (fun mask => (mask,id))

def c43982 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43982 : Upper (D 7) (R 7) [96,384,40,144] 13 := by
  apply FastRouting.sound _ _ [96,384,40,144] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43982 c43982
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43982_3
  · exact m43982_5
  · exact m43982_6
  · exact m43982_65
  · exact m43982_66
  · exact m43982_68

theorem m43983_3 : Upper (D 7) (R 7) [96,384,40,192,3] 13 :=
  permutation_upper _ _ _ [96,384,3,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40846

theorem m43983_5 : Upper (D 7) (R 7) [96,384,40,192,5] 13 :=
  permutation_upper _ _ _ [96,384,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40901

theorem m43983_6 : Upper (D 7) (R 7) [96,384,40,192,6] 13 :=
  permutation_upper _ _ _ [96,384,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40955

def r43983 : Route 9 := (fun mask => (mask,id))

def c43983 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43983 : Upper (D 7) (R 7) [96,384,40,192] 13 := by
  apply FastRouting.sound _ _ [96,384,40,192] 13 (by decide) (choices 2) [3,5,6] r43983 c43983
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43983_3
  · exact m43983_5
  · exact m43983_6

theorem m43984_3 : Upper (D 7) (R 7) [96,384,48,129,3] 13 :=
  permutation_upper _ _ _ [96,384,3,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40837

theorem m43984_5 : Upper (D 7) (R 7) [96,384,48,129,5] 13 :=
  permutation_upper _ _ _ [96,384,9,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40892

theorem m43984_6 : Upper (D 7) (R 7) [96,384,48,129,6] 13 :=
  permutation_upper _ _ _ [96,384,10,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40946

theorem m43984_9 : Upper (D 7) (R 7) [96,384,48,129,9] 13 :=
  permutation_upper _ _ _ [96,384,9,129,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40907

theorem m43984_10 : Upper (D 7) (R 7) [96,384,48,129,10] 13 :=
  permutation_upper _ _ _ [96,384,10,129,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40960

theorem m43984_12 : Upper (D 7) (R 7) [96,384,48,129,12] 13 :=
  permutation_upper _ _ _ [96,384,24,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40982

theorem m43984_65 : Upper (D 7) (R 7) [96,384,48,129,65] 13 :=
  permutation_upper _ _ _ [96,384,33,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40990

theorem m43984_66 : Upper (D 7) (R 7) [96,384,48,129,66] 13 :=
  permutation_upper _ _ _ [96,384,34,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40996

theorem m43984_68 : Upper (D 7) (R 7) [96,384,48,129,68] 13 :=
  permutation_upper _ _ _ [96,384,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41003

theorem m43984_72 : Upper (D 7) (R 7) [96,384,48,129,72] 13 :=
  permutation_upper _ _ _ [96,384,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41004

def r43984 : Route 9 := (fun mask => (mask,id))

def c43984 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43984 : Upper (D 7) (R 7) [96,384,48,129] 13 := by
  apply FastRouting.sound _ _ [96,384,48,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43984 c43984
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43984_3
  · exact m43984_5
  · exact m43984_6
  · exact m43984_9
  · exact m43984_10
  · exact m43984_12
  · exact m43984_65
  · exact m43984_66
  · exact m43984_68
  · exact m43984_72

theorem m43985_3 : Upper (D 7) (R 7) [96,384,48,132,3] 13 :=
  permutation_upper _ _ _ [96,384,3,36,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40839

theorem m43985_9 : Upper (D 7) (R 7) [96,384,48,132,9] 13 :=
  permutation_upper _ _ _ [96,384,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40917

theorem m43985_10 : Upper (D 7) (R 7) [96,384,48,132,10] 13 :=
  permutation_upper _ _ _ [96,384,10,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40966

theorem m43985_65 : Upper (D 7) (R 7) [96,384,48,132,65] 13 :=
  permutation_upper _ _ _ [96,384,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40991

theorem m43985_66 : Upper (D 7) (R 7) [96,384,48,132,66] 13 :=
  permutation_upper _ _ _ [96,384,34,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40998

theorem m43985_72 : Upper (D 7) (R 7) [96,384,48,132,72] 13 :=
  permutation_upper _ _ _ [96,384,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41006

def r43985 : Route 9 := (fun mask => (mask,id))

def c43985 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43985 : Upper (D 7) (R 7) [96,384,48,132] 13 := by
  apply FastRouting.sound _ _ [96,384,48,132] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43985 c43985
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43985_3
  · exact m43985_9
  · exact m43985_10
  · exact m43985_65
  · exact m43985_66
  · exact m43985_72

theorem m43986_3 : Upper (D 7) (R 7) [96,384,48,192,3] 13 :=
  permutation_upper _ _ _ [96,384,3,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40840

theorem m43986_5 : Upper (D 7) (R 7) [96,384,48,192,5] 13 :=
  permutation_upper _ _ _ [96,384,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40893

theorem m43986_6 : Upper (D 7) (R 7) [96,384,48,192,6] 13 :=
  permutation_upper _ _ _ [96,384,10,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40948

theorem m43986_9 : Upper (D 7) (R 7) [96,384,48,192,9] 13 :=
  permutation_upper _ _ _ [96,384,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40922

theorem m43986_10 : Upper (D 7) (R 7) [96,384,48,192,10] 13 :=
  permutation_upper _ _ _ [96,384,10,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40970

theorem m43986_12 : Upper (D 7) (R 7) [96,384,48,192,12] 13 :=
  permutation_upper _ _ _ [96,384,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40984

def r43986 : Route 9 := (fun mask => (mask,id))

def c43986 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43986 : Upper (D 7) (R 7) [96,384,48,192] 13 := by
  apply FastRouting.sound _ _ [96,384,48,192] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43986 c43986
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43986_3
  · exact m43986_5
  · exact m43986_6
  · exact m43986_9
  · exact m43986_10
  · exact m43986_12

def b43987 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 4, targets := 130 },{ cop := 2, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 386 100 137 31 63 95 159 287), lower := (rows 97 386 100 137 16 32 64 128 256), losses := [] }

theorem u43987 : Upper (D 7) (R 7) [96,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43988 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 4, targets := 130 },{ cop := 2, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 386 100 140 27 59 91 155 283), lower := (rows 97 386 100 140 16 32 64 128 256), losses := [] }

theorem u43988 : Upper (D 7) (R 7) [96,384,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43989 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 7, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(1,5)], upper := (rows 7 11 7 504 496 496 496 496 496), lower := (rows 7 11 7 8 16 32 64 128 256), losses := [] }

theorem u43989 : Upper (D 7) (R 7) [6,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43990 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c43990 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43990 : Upper (D 7) (R 7) [6,9,17] 13 := by
  apply FastRouting.sound _ _ [6,9,17] 13 (by decide) (choices 2) [34,96,258,288] r43990 c43990
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u41011
  · exact u41012
  · exact u41013
  · exact u41014

def b43991 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 22 489 497 481 481 481 481), lower := (rows 7 11 22 8 16 32 64 128 256), losses := [] }

theorem u43991 : Upper (D 7) (R 7) [6,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43992_18 : Upper (D 7) (R 7) [6,9,33,18] 13 :=
  permutation_upper _ _ _ [6,9,17,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41011

def r43992 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43992 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u43992 : Upper (D 7) (R 7) [6,9,33] 13 := by
  apply FastRouting.sound _ _ [6,9,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192,258,272,288,320] r43992 c43992
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43992_18
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

def b43993 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 38 505 497 497 497 497 497), lower := (rows 7 11 38 8 16 32 64 128 256), losses := [] }

theorem u43993 : Upper (D 7) (R 7) [6,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43994_3 : Upper (D 7) (R 7) [6,9,48,3] 13 :=
  permutation_upper _ _ _ [6,9,3,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41007

theorem m43994_33 : Upper (D 7) (R 7) [6,9,48,33] 13 :=
  permutation_upper _ _ _ [6,9,34,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41027

theorem m43994_34 : Upper (D 7) (R 7) [6,9,48,34] 13 :=
  permutation_upper _ _ _ [6,9,33,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41018

theorem m43994_65 : Upper (D 7) (R 7) [6,9,48,65] 13 :=
  permutation_upper _ _ _ [6,9,34,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41028

theorem m43994_66 : Upper (D 7) (R 7) [6,9,48,66] 13 :=
  permutation_upper _ _ _ [6,9,33,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41020

def r43994 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43994 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43994 : Upper (D 7) (R 7) [6,9,48] 13 := by
  apply FastRouting.sound _ _ [6,9,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r43994 c43994
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43994_3
  · exact m43994_33
  · exact m43994_34
  · exact m43994_65
  · exact m43994_66
  · exact u41034
  · exact u41035
  · exact u41036
  · exact u41037
  · exact u41038
  · exact u41039

theorem m43995_3 : Upper (D 7) (R 7) [6,9,96,3] 13 :=
  permutation_upper _ _ _ [6,9,3,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41008

theorem m43995_17 : Upper (D 7) (R 7) [6,9,96,17] 13 :=
  permutation_upper _ _ _ [6,9,18,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41015

theorem m43995_18 : Upper (D 7) (R 7) [6,9,96,18] 13 :=
  permutation_upper _ _ _ [6,9,17,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41012

theorem m43995_33 : Upper (D 7) (R 7) [6,9,96,33] 13 :=
  permutation_upper _ _ _ [6,9,34,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41029

theorem m43995_34 : Upper (D 7) (R 7) [6,9,96,34] 13 :=
  permutation_upper _ _ _ [6,9,33,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41021

theorem m43995_48 : Upper (D 7) (R 7) [6,9,96,48] 13 :=
  permutation_upper _ _ _ [6,9,48,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41034

theorem m43995_129 : Upper (D 7) (R 7) [6,9,96,129] 13 :=
  permutation_upper _ _ _ [6,9,34,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41030

theorem m43995_130 : Upper (D 7) (R 7) [6,9,96,130] 13 :=
  permutation_upper _ _ _ [6,9,33,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41022

theorem m43995_144 : Upper (D 7) (R 7) [6,9,96,144] 13 :=
  permutation_upper _ _ _ [6,9,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41035

def r43995 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43995 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u43995 : Upper (D 7) (R 7) [6,9,96] 13 := by
  apply FastRouting.sound _ _ [6,9,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160,257,258,272,288,384] r43995 c43995
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43995_3
  · exact m43995_17
  · exact m43995_18
  · exact m43995_33
  · exact m43995_34
  · exact m43995_48
  · exact u41040
  · exact m43995_129
  · exact m43995_130
  · exact m43995_144
  · exact u41041
  · exact u41042
  · exact u41043
  · exact u41044
  · exact u41045
  · exact u41046

theorem m43996_18 : Upper (D 7) (R 7) [6,9,257,18] 13 :=
  permutation_upper _ _ _ [6,9,17,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41013

theorem m43996_34 : Upper (D 7) (R 7) [6,9,257,34] 13 :=
  permutation_upper _ _ _ [6,9,33,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41023

theorem m43996_48 : Upper (D 7) (R 7) [6,9,257,48] 13 :=
  permutation_upper _ _ _ [6,9,48,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41037

theorem m43996_96 : Upper (D 7) (R 7) [6,9,257,96] 13 :=
  permutation_upper _ _ _ [6,9,96,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41043

def r43996 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c43996 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43996 : Upper (D 7) (R 7) [6,9,257] 13 := by
  apply FastRouting.sound _ _ [6,9,257] 13 (by decide) (choices 2) [18,34,48,96] r43996 c43996
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m43996_18
  · exact m43996_34
  · exact m43996_48
  · exact m43996_96

def b43997 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 262 249 241 241 241 241 497), lower := (rows 7 11 262 8 16 32 64 128 256), losses := [] }

theorem u43997 : Upper (D 7) (R 7) [6,9,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43998_3 : Upper (D 7) (R 7) [6,9,272,3] 13 :=
  permutation_upper _ _ _ [6,9,3,272] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41009

theorem m43998_33 : Upper (D 7) (R 7) [6,9,272,33] 13 :=
  permutation_upper _ _ _ [6,9,34,272] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41031

theorem m43998_34 : Upper (D 7) (R 7) [6,9,272,34] 13 :=
  permutation_upper _ _ _ [6,9,33,272] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41024

theorem m43998_96 : Upper (D 7) (R 7) [6,9,272,96] 13 :=
  permutation_upper _ _ _ [6,9,96,272] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41044

def r43998 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c43998 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43998 : Upper (D 7) (R 7) [6,9,272] 13 := by
  apply FastRouting.sound _ _ [6,9,272] 13 (by decide) (choices 2) [3,33,34,96] r43998 c43998
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m43998_3
  · exact m43998_33
  · exact m43998_34
  · exact m43998_96

theorem m43999_3 : Upper (D 7) (R 7) [6,9,288,3] 13 :=
  permutation_upper _ _ _ [6,9,3,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41010

theorem m43999_17 : Upper (D 7) (R 7) [6,9,288,17] 13 :=
  permutation_upper _ _ _ [6,9,18,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41016

theorem m43999_18 : Upper (D 7) (R 7) [6,9,288,18] 13 :=
  permutation_upper _ _ _ [6,9,17,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41014

theorem m43999_33 : Upper (D 7) (R 7) [6,9,288,33] 13 :=
  permutation_upper _ _ _ [6,9,34,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41032

theorem m43999_34 : Upper (D 7) (R 7) [6,9,288,34] 13 :=
  permutation_upper _ _ _ [6,9,33,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41025

theorem m43999_48 : Upper (D 7) (R 7) [6,9,288,48] 13 :=
  permutation_upper _ _ _ [6,9,48,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41038

theorem m43999_65 : Upper (D 7) (R 7) [6,9,288,65] 13 :=
  permutation_upper _ _ _ [6,9,34,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41033

theorem m43999_66 : Upper (D 7) (R 7) [6,9,288,66] 13 :=
  permutation_upper _ _ _ [6,9,33,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41026

theorem m43999_80 : Upper (D 7) (R 7) [6,9,288,80] 13 :=
  permutation_upper _ _ _ [6,9,48,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41039

theorem m43999_96 : Upper (D 7) (R 7) [6,9,288,96] 13 :=
  permutation_upper _ _ _ [6,9,96,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41045

theorem m43999_192 : Upper (D 7) (R 7) [6,9,288,192] 13 :=
  permutation_upper _ _ _ [6,9,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41046

def r43999 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43999 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43999 : Upper (D 7) (R 7) [6,9,288] 13 := by
  apply FastRouting.sound _ _ [6,9,288] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r43999 c43999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43999_3
  · exact m43999_17
  · exact m43999_18
  · exact m43999_33
  · exact m43999_34
  · exact m43999_48
  · exact m43999_65
  · exact m43999_66
  · exact m43999_80
  · exact m43999_96
  · exact m43999_192

def b44000 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 26 7 489 497 481 481 481 481), lower := (rows 7 26 7 8 16 32 64 128 256), losses := [] }

theorem u44000 : Upper (D 7) (R 7) [6,24,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44001 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44001 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44001 : Upper (D 7) (R 7) [6,24,33] 13 := by
  apply FastRouting.sound _ _ [6,24,33] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r44001 c44001
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41047
  · exact u41048
  · exact u41049
  · exact u41050
  · exact u41051
  · exact u41052
  · exact u41053
  · exact u41054
  · exact u41055
  · exact u41056
  · exact u41057

def b44002 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 26 38 489 497 481 481 481 481), lower := (rows 7 26 38 8 16 32 64 128 256), losses := [] }

theorem u44002 : Upper (D 7) (R 7) [6,24,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44003 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44003 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44003 : Upper (D 7) (R 7) [6,24,96] 13 := by
  apply FastRouting.sound _ _ [6,24,96] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r44003 c44003
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44004 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44004 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44004 : Upper (D 7) (R 7) [6,24,257] 13 := by
  apply FastRouting.sound _ _ [6,24,257] 13 (by decide) (choices 2) [3,33,34,96] r44004 c44004
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u41069
  · exact u41070
  · exact u41071
  · exact u41072

def b44005 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 232, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 26 262 233 241 225 225 225 481), lower := (rows 7 26 262 8 16 32 64 128 256), losses := [] }

theorem u44005 : Upper (D 7) (R 7) [6,24,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44006 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44006 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44006 : Upper (D 7) (R 7) [6,24,288] 13 := by
  apply FastRouting.sound _ _ [6,24,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r44006 c44006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41073
  · exact u41074
  · exact u41075
  · exact u41076
  · exact u41077
  · exact u41078
  · exact u41079

def b44007 : PairBound 9 := { available := 504, camps := [{ cop := 1, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 35 7 504 504 504 504 504 504), lower := (rows 7 35 7 8 16 32 64 128 256), losses := [] }

theorem u44007 : Upper (D 7) (R 7) [6,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44008 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44008 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44008 : Upper (D 7) (R 7) [6,33,9] 13 := by
  apply FastRouting.sound _ _ [6,33,9] 13 (by decide) (choices 2) [18,34,48,66,80,96,192,258,272,288,320] r44008 c44008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b44009 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 35 14 505 497 497 497 497 497), lower := (rows 7 35 14 8 16 32 64 128 256), losses := [] }

theorem u44009 : Upper (D 7) (R 7) [6,33,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44010 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44010 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44010 : Upper (D 7) (R 7) [6,33,24] 13 := by
  apply FastRouting.sound _ _ [6,33,24] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r44010 c44010
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41091
  · exact u41092
  · exact u41093
  · exact u41094
  · exact u41095
  · exact u41096
  · exact u41097
  · exact u41098
  · exact u41099
  · exact u41100
  · exact u41101

def b44011 : PairBound 9 := { available := 474, camps := [{ cop := 5, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 37 474 474 506 474 474 474), lower := (rows 7 35 37 8 16 32 64 128 256), losses := [] }

theorem u44011 : Upper (D 7) (R 7) [6,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44012 : PairBound 9 := { available := 473, camps := [{ cop := 5, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 38 473 473 505 473 473 473), lower := (rows 7 35 38 8 16 32 64 128 256), losses := [] }

theorem u44012 : Upper (D 7) (R 7) [6,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44013 : PairBound 9 := { available := 467, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 44 475 467 499 467 467 467), lower := (rows 7 35 44 8 16 32 64 128 256), losses := [] }

theorem u44013 : Upper (D 7) (R 7) [6,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44014 : Route 9 := (fun mask => (mask,id))

def c44014 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44014 : Upper (D 7) (R 7) [6,33,65] 13 := by
  apply FastRouting.sound _ _ [6,33,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192,258,272,288,320,384] r44014 c44014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41102
  · exact u41103
  · exact u41104
  · exact u41105
  · exact u41106
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

def b44015 : PairBound 9 := { available := 505, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 35 70 505 505 505 505 505 505), lower := (rows 7 35 70 8 16 32 64 128 256), losses := [] }

theorem u44015 : Upper (D 7) (R 7) [6,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44016 : Route 9 := (fun mask => (mask,id))

def c44016 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44016 : Upper (D 7) (R 7) [6,33,72] 13 := by
  apply FastRouting.sound _ _ [6,33,72] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192,257,258,272,288,320,384] r44016 c44016
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41117
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
  · exact u41130
  · exact u41131
  · exact u41132
  · exact u41133
  · exact u41134
  · exact u41135
  · exact u41136
  · exact u41137

def b44017 : PairBound 9 := { available := 475, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 100 475 475 507 475 475 475), lower := (rows 7 35 100 8 16 32 64 128 256), losses := [] }

theorem u44017 : Upper (D 7) (R 7) [6,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44018 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44018 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44018 : Upper (D 7) (R 7) [6,33,192] 13 := by
  apply FastRouting.sound _ _ [6,33,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r44018 c44018
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact u41152
  · exact u41153

def r44019 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44019 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44019 : Upper (D 7) (R 7) [6,33,257] 13 := by
  apply FastRouting.sound _ _ [6,33,257] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r44019 c44019
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41154
  · exact u41155
  · exact u41156
  · exact u41157
  · exact u41158
  · exact u41159
  · exact u41160

def b44020 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 35 262 249 249 249 249 249 505), lower := (rows 7 35 262 8 16 32 64 128 256), losses := [] }

theorem u44020 : Upper (D 7) (R 7) [6,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44021 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44021 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44021 : Upper (D 7) (R 7) [6,33,264] 13 := by
  apply FastRouting.sound _ _ [6,33,264] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44021 c44021
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b44022 : PairBound 9 := { available := 219, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 292 219 219 251 219 219 475), lower := (rows 7 35 292 8 16 32 64 128 256), losses := [] }

theorem u44022 : Upper (D 7) (R 7) [6,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44023 : Route 9 := (fun mask => (mask,id))

def c44023 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44023 : Upper (D 7) (R 7) [6,33,320] 13 := by
  apply FastRouting.sound _ _ [6,33,320] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44023 c44023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41172
  · exact u41173
  · exact u41174
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
  · exact u41186

def b44024 : PairBound 9 := { available := 497, camps := [{ cop := 1, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 42 7 505 497 497 497 497 497), lower := (rows 7 42 7 8 16 32 64 128 256), losses := [] }

theorem u44024 : Upper (D 7) (R 7) [6,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44025 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44025 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44025 : Upper (D 7) (R 7) [6,40,17] 13 := by
  apply FastRouting.sound _ _ [6,40,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r44025 c44025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b44026 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 42 22 489 497 481 481 481 481), lower := (rows 7 42 22 8 16 32 64 128 256), losses := [] }

theorem u44026 : Upper (D 7) (R 7) [6,40,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44027 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 37 475 467 499 467 467 467), lower := (rows 7 42 37 8 16 32 64 128 256), losses := [] }

theorem u44027 : Upper (D 7) (R 7) [6,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44028 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 38 473 465 497 465 465 465), lower := (rows 7 42 38 8 16 32 64 128 256), losses := [] }

theorem u44028 : Upper (D 7) (R 7) [6,40,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44029 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44029 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44029 : Upper (D 7) (R 7) [6,40,48] 13 := by
  apply FastRouting.sound _ _ [6,40,48] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r44029 c44029
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41198
  · exact u41199
  · exact u41200
  · exact u41201
  · exact u41202
  · exact u41203
  · exact u41204

def r44030 : Route 9 := (fun mask => (mask,id))

def c44030 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44030 : Upper (D 7) (R 7) [6,40,65] 13 := by
  apply FastRouting.sound _ _ [6,40,65] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192,257,258,272,288,320,384] r44030 c44030
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41205
  · exact u41206
  · exact u41207
  · exact u41208
  · exact u41209
  · exact u41210
  · exact u41211
  · exact u41212
  · exact u41213
  · exact u41214
  · exact u41215
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

def b44031 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 42 70 505 497 497 497 497 497), lower := (rows 7 42 70 8 16 32 64 128 256), losses := [] }

theorem u44031 : Upper (D 7) (R 7) [6,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44032 : Route 9 := (fun mask => (mask,id))

def c44032 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44032 : Upper (D 7) (R 7) [6,40,80] 13 := by
  apply FastRouting.sound _ _ [6,40,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r44032 c44032
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41226
  · exact u41227
  · exact u41228
  · exact u41229
  · exact u41230
  · exact u41231
  · exact u41232
  · exact u41233
  · exact u41234
  · exact u41235
  · exact u41236
  · exact u41237
  · exact u41238
  · exact u41239
  · exact u41240

def r44033 : Route 9 := (fun mask => (mask,id))

def c44033 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44033 : Upper (D 7) (R 7) [6,40,96] 13 := by
  apply FastRouting.sound _ _ [6,40,96] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192,257,258,272,320,384] r44033 c44033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41241
  · exact u41242
  · exact u41243
  · exact u41244
  · exact u41245
  · exact u41246
  · exact u41247
  · exact u41248
  · exact u41249
  · exact u41250
  · exact u41251
  · exact u41252
  · exact u41253
  · exact u41254
  · exact u41255

def r44034 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44034 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44034 : Upper (D 7) (R 7) [6,40,192] 13 := by
  apply FastRouting.sound _ _ [6,40,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r44034 c44034
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41256
  · exact u41257
  · exact u41258
  · exact u41259
  · exact u41260
  · exact u41261
  · exact u41262
  · exact u41263
  · exact u41264
  · exact u41265
  · exact u41266
  · exact u41267
  · exact u41268
  · exact u41269
  · exact u41270
  · exact u41271

def r44035 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44035 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44035 : Upper (D 7) (R 7) [6,40,257] 13 := by
  apply FastRouting.sound _ _ [6,40,257] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44035 c44035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41272
  · exact u41273
  · exact u41274
  · exact u41275
  · exact u41276
  · exact u41277
  · exact u41278
  · exact u41279
  · exact u41280
  · exact u41281
  · exact u41282

def b44036 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 42 262 249 241 241 241 241 497), lower := (rows 7 42 262 8 16 32 64 128 256), losses := [] }

theorem u44036 : Upper (D 7) (R 7) [6,40,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44037 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44037 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44037 : Upper (D 7) (R 7) [6,40,272] 13 := by
  apply FastRouting.sound _ _ [6,40,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r44037 c44037
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41283
  · exact u41284
  · exact u41285
  · exact u41286
  · exact u41287
  · exact u41288
  · exact u41289

def r44038 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44038 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44038 : Upper (D 7) (R 7) [6,40,288] 13 := by
  apply FastRouting.sound _ _ [6,40,288] 13 (by decide) (choices 2) [3,17,18,65,66,80,192] r44038 c44038
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41290
  · exact u41291
  · exact u41292
  · exact u41293
  · exact u41294
  · exact u41295
  · exact u41296

def r44039 : Route 9 := (fun mask => (mask,id))

def c44039 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44039 : Upper (D 7) (R 7) [6,40,320] 13 := by
  apply FastRouting.sound _ _ [6,40,320] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44039 c44039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41297
  · exact u41298
  · exact u41299
  · exact u41300
  · exact u41301
  · exact u41302
  · exact u41303
  · exact u41304
  · exact u41305
  · exact u41306
  · exact u41307
  · exact u41308
  · exact u41309
  · exact u41310
  · exact u41311

#print axioms u44039
end Delivery.IrregularNine14.P07
