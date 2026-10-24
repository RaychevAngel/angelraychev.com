import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0277
import IrregularNine14P08C0278
import IrregularNine14P08C0279
import IrregularNine14P08C0280

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22740 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 37 137 248 248 248 248 504), lower := (rows 259 70 37 137 16 32 64 128 256), losses := [] }

theorem u22740 : Upper (D 8) (R 8) [258,68,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22741_9 : Upper (D 8) (R 8) [258,68,33,144,9] 13 :=
  permutation_upper _ _ _ [258,68,33,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16621

theorem m22741_33 : Upper (D 8) (R 8) [258,68,33,144,33] 13 :=
  permutation_upper _ _ _ [258,68,33,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16627

theorem m22741_40 : Upper (D 8) (R 8) [258,68,33,144,40] 13 :=
  permutation_upper _ _ _ [258,68,33,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16635

theorem m22741_65 : Upper (D 8) (R 8) [258,68,33,144,65] 13 :=
  permutation_upper _ _ _ [258,68,33,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16638

theorem m22741_72 : Upper (D 8) (R 8) [258,68,33,144,72] 13 :=
  permutation_upper _ _ _ [258,68,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16641

theorem m22741_96 : Upper (D 8) (R 8) [258,68,33,144,96] 13 :=
  permutation_upper _ _ _ [258,68,33,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16644

theorem m22741_129 : Upper (D 8) (R 8) [258,68,33,144,129] 13 :=
  permutation_upper _ _ _ [258,68,33,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16646

def r22741 : Route 9 := (fun mask => (mask,id))

def c22741 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22741 : Upper (D 8) (R 8) [258,68,33,144] 13 := by
  apply FastRouting.sound _ _ [258,68,33,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22741 c22741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22741_9
  · exact m22741_33
  · exact m22741_40
  · exact m22741_65
  · exact m22741_72
  · exact m22741_96
  · exact m22741_129
  · exact u16649
  · exact u16650
  · exact u16651

theorem m22742_9 : Upper (D 8) (R 8) [258,68,33,160,9] 13 :=
  permutation_upper _ _ _ [258,68,33,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16622

theorem m22742_33 : Upper (D 8) (R 8) [258,68,33,160,33] 13 :=
  permutation_upper _ _ _ [258,68,33,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16628

theorem m22742_40 : Upper (D 8) (R 8) [258,68,33,160,40] 13 :=
  permutation_upper _ _ _ [258,68,33,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16636

theorem m22742_65 : Upper (D 8) (R 8) [258,68,33,160,65] 13 :=
  permutation_upper _ _ _ [258,68,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16639

theorem m22742_72 : Upper (D 8) (R 8) [258,68,33,160,72] 13 :=
  permutation_upper _ _ _ [258,68,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16642

theorem m22742_96 : Upper (D 8) (R 8) [258,68,33,160,96] 13 :=
  permutation_upper _ _ _ [258,68,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16645

theorem m22742_129 : Upper (D 8) (R 8) [258,68,33,160,129] 13 :=
  permutation_upper _ _ _ [258,68,33,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16647

theorem m22742_136 : Upper (D 8) (R 8) [258,68,33,160,136] 13 :=
  permutation_upper _ _ _ [258,68,33,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16650

def r22742 : Route 9 := (fun mask => (mask,id))

def c22742 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22742 : Upper (D 8) (R 8) [258,68,33,160] 13 := by
  apply FastRouting.sound _ _ [258,68,33,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22742 c22742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22742_9
  · exact m22742_33
  · exact m22742_40
  · exact m22742_65
  · exact m22742_72
  · exact m22742_96
  · exact m22742_129
  · exact m22742_136
  · exact u16652
  · exact u16653

theorem m22743_9 : Upper (D 8) (R 8) [258,68,33,192,9] 13 :=
  permutation_upper _ _ _ [258,68,33,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16623

theorem m22743_33 : Upper (D 8) (R 8) [258,68,33,192,33] 13 :=
  permutation_upper _ _ _ [258,68,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16629

theorem m22743_40 : Upper (D 8) (R 8) [258,68,33,192,40] 13 :=
  permutation_upper _ _ _ [258,68,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16637

theorem m22743_129 : Upper (D 8) (R 8) [258,68,33,192,129] 13 :=
  permutation_upper _ _ _ [258,68,33,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16648

theorem m22743_136 : Upper (D 8) (R 8) [258,68,33,192,136] 13 :=
  permutation_upper _ _ _ [258,68,33,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16651

theorem m22743_160 : Upper (D 8) (R 8) [258,68,33,192,160] 13 :=
  permutation_upper _ _ _ [258,68,33,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16653

def r22743 : Route 9 := (fun mask => (mask,id))

def c22743 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22743 : Upper (D 8) (R 8) [258,68,33,192] 13 := by
  apply FastRouting.sound _ _ [258,68,33,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22743 c22743
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22743_9
  · exact m22743_33
  · exact m22743_40
  · exact m22743_129
  · exact m22743_136
  · exact m22743_160

def r22744 : Route 9 := (fun mask => (mask,id))

def c22744 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22744 : Upper (D 8) (R 8) [258,68,40,17] 13 := by
  apply FastRouting.sound _ _ [258,68,40,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22744 c22744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16654
  · exact u16655
  · exact u16656
  · exact u16657
  · exact u16658
  · exact u16659

def b22745 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 70 44 41 241 241 241 241 497), lower := (rows 259 70 44 41 16 32 64 128 256), losses := [] }

theorem u22745 : Upper (D 8) (R 8) [258,68,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22746 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 70 44 56 241 225 225 225 481), lower := (rows 259 70 44 56 16 32 64 128 256), losses := [] }

theorem u22746 : Upper (D 8) (R 8) [258,68,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22747 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 44 73 177 177 241 177 433), lower := (rows 259 70 44 73 16 32 64 128 256), losses := [] }

theorem u22747 : Upper (D 8) (R 8) [258,68,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22748 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 44 88 177 161 225 161 417), lower := (rows 259 70 44 88 16 32 64 128 256), losses := [] }

theorem u22748 : Upper (D 8) (R 8) [258,68,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22749 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 104 177 177 241 177 433), lower := (rows 259 70 44 104 16 32 64 128 256), losses := [] }

theorem u22749 : Upper (D 8) (R 8) [258,68,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22750 : Route 9 := (fun mask => (mask,id))

def c22750 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22750 : Upper (D 8) (R 8) [258,68,40,129] 13 := by
  apply FastRouting.sound _ _ [258,68,40,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22750 c22750
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16660
  · exact u16661
  · exact u16662
  · exact u16663
  · exact u16664
  · exact u16665

def r22751 : Route 9 := (fun mask => (mask,id))

def c22751 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22751 : Upper (D 8) (R 8) [258,68,40,144] 13 := by
  apply FastRouting.sound _ _ [258,68,40,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22751 c22751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16666
  · exact u16667
  · exact u16668
  · exact u16669
  · exact u16670
  · exact u16671

def b22752 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 70 44 168 241 241 241 241 497), lower := (rows 259 70 44 168 16 32 64 128 256), losses := [] }

theorem u22752 : Upper (D 8) (R 8) [258,68,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22753 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 44 200 177 177 241 177 433), lower := (rows 259 70 44 200 16 32 64 128 256), losses := [] }

theorem u22753 : Upper (D 8) (R 8) [258,68,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22754 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 25 248 232 232 232 488), lower := (rows 259 70 133 25 16 32 64 128 256), losses := [] }

theorem u22754 : Upper (D 8) (R 8) [258,68,129,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22755 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 41 248 248 248 248 504), lower := (rows 259 70 133 41 16 32 64 128 256), losses := [] }

theorem u22755 : Upper (D 8) (R 8) [258,68,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22756_9 : Upper (D 8) (R 8) [258,68,129,48,9] 13 :=
  permutation_upper _ _ _ [258,68,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16672

theorem m22756_33 : Upper (D 8) (R 8) [258,68,129,48,33] 13 :=
  permutation_upper _ _ _ [258,68,129,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16678

def r22756 : Route 9 := (fun mask => (mask,id))

def c22756 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22756 : Upper (D 8) (R 8) [258,68,129,48] 13 := by
  apply FastRouting.sound _ _ [258,68,129,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22756 c22756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22756_9
  · exact m22756_33
  · exact u16684
  · exact u16685
  · exact u16686
  · exact u16687
  · exact u16688
  · exact u16689
  · exact u16690
  · exact u16691

def b22757 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 133 73 184 184 248 184 440), lower := (rows 259 70 133 73 16 32 64 128 256), losses := [] }

theorem u22757 : Upper (D 8) (R 8) [258,68,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22758_9 : Upper (D 8) (R 8) [258,68,129,80,9] 13 :=
  permutation_upper _ _ _ [258,68,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16673

theorem m22758_33 : Upper (D 8) (R 8) [258,68,129,80,33] 13 :=
  permutation_upper _ _ _ [258,68,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16679

theorem m22758_40 : Upper (D 8) (R 8) [258,68,129,80,40] 13 :=
  permutation_upper _ _ _ [258,68,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16686

def r22758 : Route 9 := (fun mask => (mask,id))

def c22758 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22758 : Upper (D 8) (R 8) [258,68,129,80] 13 := by
  apply FastRouting.sound _ _ [258,68,129,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22758 c22758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22758_9
  · exact m22758_33
  · exact m22758_40
  · exact u16694
  · exact u16695
  · exact u16696

theorem m22759_9 : Upper (D 8) (R 8) [258,68,129,96,9] 13 :=
  permutation_upper _ _ _ [258,68,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16674

theorem m22759_33 : Upper (D 8) (R 8) [258,68,129,96,33] 13 :=
  permutation_upper _ _ _ [258,68,129,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16680

theorem m22759_40 : Upper (D 8) (R 8) [258,68,129,96,40] 13 :=
  permutation_upper _ _ _ [258,68,129,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16687

def r22759 : Route 9 := (fun mask => (mask,id))

def c22759 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22759 : Upper (D 8) (R 8) [258,68,129,96] 13 := by
  apply FastRouting.sound _ _ [258,68,129,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22759 c22759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22759_9
  · exact m22759_33
  · exact m22759_40
  · exact u16697
  · exact u16698
  · exact u16699

def b22760 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 70 133 137 120 120 120 248 376), lower := (rows 259 70 133 137 16 32 64 128 256), losses := [] }

theorem u22760 : Upper (D 8) (R 8) [258,68,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22761_9 : Upper (D 8) (R 8) [258,68,129,144,9] 13 :=
  permutation_upper _ _ _ [258,68,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16675

theorem m22761_33 : Upper (D 8) (R 8) [258,68,129,144,33] 13 :=
  permutation_upper _ _ _ [258,68,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16681

theorem m22761_40 : Upper (D 8) (R 8) [258,68,129,144,40] 13 :=
  permutation_upper _ _ _ [258,68,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16689

theorem m22761_65 : Upper (D 8) (R 8) [258,68,129,144,65] 13 :=
  permutation_upper _ _ _ [258,68,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16692

theorem m22761_72 : Upper (D 8) (R 8) [258,68,129,144,72] 13 :=
  permutation_upper _ _ _ [258,68,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16695

theorem m22761_96 : Upper (D 8) (R 8) [258,68,129,144,96] 13 :=
  permutation_upper _ _ _ [258,68,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16698

def r22761 : Route 9 := (fun mask => (mask,id))

def c22761 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u22761 : Upper (D 8) (R 8) [258,68,129,144] 13 := by
  apply FastRouting.sound _ _ [258,68,129,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r22761 c22761
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22761_9
  · exact m22761_33
  · exact m22761_40
  · exact m22761_65
  · exact m22761_72
  · exact m22761_96

theorem m22762_9 : Upper (D 8) (R 8) [258,68,129,160,9] 13 :=
  permutation_upper _ _ _ [258,68,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16676

theorem m22762_33 : Upper (D 8) (R 8) [258,68,129,160,33] 13 :=
  permutation_upper _ _ _ [258,68,129,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16682

theorem m22762_40 : Upper (D 8) (R 8) [258,68,129,160,40] 13 :=
  permutation_upper _ _ _ [258,68,129,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16690

theorem m22762_65 : Upper (D 8) (R 8) [258,68,129,160,65] 13 :=
  permutation_upper _ _ _ [258,68,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16693

theorem m22762_72 : Upper (D 8) (R 8) [258,68,129,160,72] 13 :=
  permutation_upper _ _ _ [258,68,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16696

theorem m22762_96 : Upper (D 8) (R 8) [258,68,129,160,96] 13 :=
  permutation_upper _ _ _ [258,68,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16699

def r22762 : Route 9 := (fun mask => (mask,id))

def c22762 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u22762 : Upper (D 8) (R 8) [258,68,129,160] 13 := by
  apply FastRouting.sound _ _ [258,68,129,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r22762 c22762
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22762_9
  · exact m22762_33
  · exact m22762_40
  · exact m22762_65
  · exact m22762_72
  · exact m22762_96

theorem m22763_9 : Upper (D 8) (R 8) [258,68,129,192,9] 13 :=
  permutation_upper _ _ _ [258,68,129,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16677

theorem m22763_33 : Upper (D 8) (R 8) [258,68,129,192,33] 13 :=
  permutation_upper _ _ _ [258,68,129,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16683

theorem m22763_40 : Upper (D 8) (R 8) [258,68,129,192,40] 13 :=
  permutation_upper _ _ _ [258,68,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16691

def r22763 : Route 9 := (fun mask => (mask,id))

def c22763 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22763 : Upper (D 8) (R 8) [258,68,129,192] 13 := by
  apply FastRouting.sound _ _ [258,68,129,192] 13 (by decide) (choices 2) [9,33,40] r22763 c22763
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m22763_9
  · exact m22763_33
  · exact m22763_40

def r22764 : Route 9 := (fun mask => (mask,id))

def c22764 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22764 : Upper (D 8) (R 8) [258,68,136,17] 13 := by
  apply FastRouting.sound _ _ [258,68,136,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22764 c22764
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16700
  · exact u16701
  · exact u16702
  · exact u16703
  · exact u16704
  · exact u16705

def r22765 : Route 9 := (fun mask => (mask,id))

def c22765 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22765 : Upper (D 8) (R 8) [258,68,136,33] 13 := by
  apply FastRouting.sound _ _ [258,68,136,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22765 c22765
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16706
  · exact u16707
  · exact u16708
  · exact u16709
  · exact u16710
  · exact u16711

def r22766 : Route 9 := (fun mask => (mask,id))

def c22766 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22766 : Upper (D 8) (R 8) [258,68,136,48] 13 := by
  apply FastRouting.sound _ _ [258,68,136,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22766 c22766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16712
  · exact u16713
  · exact u16714
  · exact u16715
  · exact u16716
  · exact u16717

def b22767 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 140 73 177 177 241 177 433), lower := (rows 259 70 140 73 16 32 64 128 256), losses := [] }

theorem u22767 : Upper (D 8) (R 8) [258,68,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22768 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 140 88 177 161 225 161 417), lower := (rows 259 70 140 88 16 32 64 128 256), losses := [] }

theorem u22768 : Upper (D 8) (R 8) [258,68,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22769 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 140 104 177 177 241 177 433), lower := (rows 259 70 140 104 16 32 64 128 256), losses := [] }

theorem u22769 : Upper (D 8) (R 8) [258,68,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22770 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 140 137 113 113 113 241 369), lower := (rows 259 70 140 137 16 32 64 128 256), losses := [] }

theorem u22770 : Upper (D 8) (R 8) [258,68,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22771 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 140 152 113 97 97 225 353), lower := (rows 259 70 140 152 16 32 64 128 256), losses := [] }

theorem u22771 : Upper (D 8) (R 8) [258,68,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22772 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 140 168 113 113 113 241 369), lower := (rows 259 70 140 168 16 32 64 128 256), losses := [] }

theorem u22772 : Upper (D 8) (R 8) [258,68,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22773 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 140 200 49 49 113 177 305), lower := (rows 259 70 140 200 16 32 64 128 256), losses := [] }

theorem u22773 : Upper (D 8) (R 8) [258,68,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22774 : Route 9 := (fun mask => (mask,id))

def c22774 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22774 : Upper (D 8) (R 8) [258,68,160,17] 13 := by
  apply FastRouting.sound _ _ [258,68,160,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22774 c22774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16718
  · exact u16719
  · exact u16720
  · exact u16721
  · exact u16722
  · exact u16723
  · exact u16724
  · exact u16725
  · exact u16726
  · exact u16727

theorem m22775_9 : Upper (D 8) (R 8) [258,68,160,33,9] 13 :=
  permutation_upper _ _ _ [258,68,160,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16719

def r22775 : Route 9 := (fun mask => (mask,id))

def c22775 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22775 : Upper (D 8) (R 8) [258,68,160,33] 13 := by
  apply FastRouting.sound _ _ [258,68,160,33] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22775 c22775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22775_9
  · exact u16728
  · exact u16729
  · exact u16730
  · exact u16731
  · exact u16732
  · exact u16733
  · exact u16734
  · exact u16735
  · exact u16736

theorem m22776_9 : Upper (D 8) (R 8) [258,68,160,48,9] 13 :=
  permutation_upper _ _ _ [258,68,160,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16720

theorem m22776_33 : Upper (D 8) (R 8) [258,68,160,48,33] 13 :=
  permutation_upper _ _ _ [258,68,160,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16729

def r22776 : Route 9 := (fun mask => (mask,id))

def c22776 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22776 : Upper (D 8) (R 8) [258,68,160,48] 13 := by
  apply FastRouting.sound _ _ [258,68,160,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22776 c22776
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22776_9
  · exact m22776_33
  · exact u16737
  · exact u16738
  · exact u16739
  · exact u16740
  · exact u16741
  · exact u16742
  · exact u16743
  · exact u16744

def b22777 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 164 73 185 185 249 185 441), lower := (rows 259 70 164 73 16 32 64 128 256), losses := [] }

theorem u22777 : Upper (D 8) (R 8) [258,68,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22778_9 : Upper (D 8) (R 8) [258,68,160,80,9] 13 :=
  permutation_upper _ _ _ [258,68,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16722

theorem m22778_33 : Upper (D 8) (R 8) [258,68,160,80,33] 13 :=
  permutation_upper _ _ _ [258,68,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16731

theorem m22778_40 : Upper (D 8) (R 8) [258,68,160,80,40] 13 :=
  permutation_upper _ _ _ [258,68,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16739

def r22778 : Route 9 := (fun mask => (mask,id))

def c22778 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22778 : Upper (D 8) (R 8) [258,68,160,80] 13 := by
  apply FastRouting.sound _ _ [258,68,160,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22778 c22778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22778_9
  · exact m22778_33
  · exact m22778_40
  · exact u16746
  · exact u16747
  · exact u16748

theorem m22779_9 : Upper (D 8) (R 8) [258,68,160,96,9] 13 :=
  permutation_upper _ _ _ [258,68,160,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16723

theorem m22779_33 : Upper (D 8) (R 8) [258,68,160,96,33] 13 :=
  permutation_upper _ _ _ [258,68,160,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16732

theorem m22779_40 : Upper (D 8) (R 8) [258,68,160,96,40] 13 :=
  permutation_upper _ _ _ [258,68,160,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16740

def r22779 : Route 9 := (fun mask => (mask,id))

def c22779 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22779 : Upper (D 8) (R 8) [258,68,160,96] 13 := by
  apply FastRouting.sound _ _ [258,68,160,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22779 c22779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22779_9
  · exact m22779_33
  · exact m22779_40
  · exact u16749
  · exact u16750
  · exact u16751

def b22780 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 259 70 164 137 121 121 121 249 377), lower := (rows 259 70 164 137 16 32 64 128 256), losses := [] }

theorem u22780 : Upper (D 8) (R 8) [258,68,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22781_9 : Upper (D 8) (R 8) [258,68,160,144,9] 13 :=
  permutation_upper _ _ _ [258,68,160,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16725

theorem m22781_33 : Upper (D 8) (R 8) [258,68,160,144,33] 13 :=
  permutation_upper _ _ _ [258,68,160,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16734

theorem m22781_40 : Upper (D 8) (R 8) [258,68,160,144,40] 13 :=
  permutation_upper _ _ _ [258,68,160,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16742

theorem m22781_65 : Upper (D 8) (R 8) [258,68,160,144,65] 13 :=
  permutation_upper _ _ _ [258,68,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16745

theorem m22781_72 : Upper (D 8) (R 8) [258,68,160,144,72] 13 :=
  permutation_upper _ _ _ [258,68,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16747

theorem m22781_96 : Upper (D 8) (R 8) [258,68,160,144,96] 13 :=
  permutation_upper _ _ _ [258,68,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16750

def r22781 : Route 9 := (fun mask => (mask,id))

def c22781 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u22781 : Upper (D 8) (R 8) [258,68,160,144] 13 := by
  apply FastRouting.sound _ _ [258,68,160,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r22781 c22781
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22781_9
  · exact m22781_33
  · exact m22781_40
  · exact m22781_65
  · exact m22781_72
  · exact m22781_96

def b22782 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 164 168 121 121 121 249 377), lower := (rows 259 70 164 168 16 32 64 128 256), losses := [] }

theorem u22782 : Upper (D 8) (R 8) [258,68,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22783_9 : Upper (D 8) (R 8) [258,68,160,192,9] 13 :=
  permutation_upper _ _ _ [258,68,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16727

theorem m22783_33 : Upper (D 8) (R 8) [258,68,160,192,33] 13 :=
  permutation_upper _ _ _ [258,68,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16736

theorem m22783_40 : Upper (D 8) (R 8) [258,68,160,192,40] 13 :=
  permutation_upper _ _ _ [258,68,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16744

def r22783 : Route 9 := (fun mask => (mask,id))

def c22783 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22783 : Upper (D 8) (R 8) [258,68,160,192] 13 := by
  apply FastRouting.sound _ _ [258,68,160,192] 13 (by decide) (choices 2) [9,33,40] r22783 c22783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m22783_9
  · exact m22783_33
  · exact m22783_40

def b22784 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 13 240 240 240 240 496), lower := (rows 259 98 13 13 16 32 64 128 256), losses := [] }

theorem u22784 : Upper (D 8) (R 8) [258,96,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22785 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 25 244 228 228 228 484), lower := (rows 259 98 13 25 16 32 64 128 256), losses := [] }

theorem u22785 : Upper (D 8) (R 8) [258,96,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22786 : Route 9 := (fun mask => (mask,id))

def c22786 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22786 : Upper (D 8) (R 8) [258,96,9,20] 13 := by
  apply FastRouting.sound _ _ [258,96,9,20] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22786 c22786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16759
  · exact u16760
  · exact u16761
  · exact u16762
  · exact u16763
  · exact u16764

def b22787 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 244 244 244 244 500), lower := (rows 259 98 13 41 16 32 64 128 256), losses := [] }

theorem u22787 : Upper (D 8) (R 8) [258,96,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22788 : Route 9 := (fun mask => (mask,id))

def c22788 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22788 : Upper (D 8) (R 8) [258,96,9,36] 13 := by
  apply FastRouting.sound _ _ [258,96,9,36] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22788 c22788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16770
  · exact u16771
  · exact u16772
  · exact u16773
  · exact u16774
  · exact u16775

theorem m22789_5 : Upper (D 8) (R 8) [258,96,9,48,5] 13 :=
  permutation_upper _ _ _ [258,96,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16754

def r22789 : Route 9 := (fun mask => (mask,id))

def c22789 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22789 : Upper (D 8) (R 8) [258,96,9,48] 13 := by
  apply FastRouting.sound _ _ [258,96,9,48] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22789 c22789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22789_5
  · exact u16776
  · exact u16777
  · exact u16778
  · exact u16779
  · exact u16780
  · exact u16781
  · exact u16782
  · exact u16783
  · exact u16784

def b22790 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 73 180 180 244 180 436), lower := (rows 259 98 13 73 16 32 64 128 256), losses := [] }

theorem u22790 : Upper (D 8) (R 8) [258,96,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22791 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 76 177 177 241 177 433), lower := (rows 259 98 13 76 16 32 64 128 256), losses := [] }

theorem u22791 : Upper (D 8) (R 8) [258,96,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22792 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 88 181 165 229 165 421), lower := (rows 259 98 13 88 16 32 64 128 256), losses := [] }

theorem u22792 : Upper (D 8) (R 8) [258,96,9,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22793 : PairBound 9 := { available := 181, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 181 181 245 181 437), lower := (rows 259 98 13 104 16 32 64 128 256), losses := [] }

theorem u22793 : Upper (D 8) (R 8) [258,96,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22794 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 244 244 244 244 500), lower := (rows 259 98 13 137 16 32 64 128 256), losses := [] }

theorem u22794 : Upper (D 8) (R 8) [258,96,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22795 : Route 9 := (fun mask => (mask,id))

def c22795 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22795 : Upper (D 8) (R 8) [258,96,9,132] 13 := by
  apply FastRouting.sound _ _ [258,96,9,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22795 c22795
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16806
  · exact u16807
  · exact u16808
  · exact u16809
  · exact u16810
  · exact u16811

theorem m22796_5 : Upper (D 8) (R 8) [258,96,9,144,5] 13 :=
  permutation_upper _ _ _ [258,96,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16756

def r22796 : Route 9 := (fun mask => (mask,id))

def c22796 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22796 : Upper (D 8) (R 8) [258,96,9,144] 13 := by
  apply FastRouting.sound _ _ [258,96,9,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22796 c22796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22796_5
  · exact u16812
  · exact u16813
  · exact u16814
  · exact u16815
  · exact u16816
  · exact u16817
  · exact u16818
  · exact u16819
  · exact u16820

theorem m22797_5 : Upper (D 8) (R 8) [258,96,9,160,5] 13 :=
  permutation_upper _ _ _ [258,96,9,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16757

def r22797 : Route 9 := (fun mask => (mask,id))

def c22797 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22797 : Upper (D 8) (R 8) [258,96,9,160] 13 := by
  apply FastRouting.sound _ _ [258,96,9,160] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22797 c22797
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22797_5
  · exact u16821
  · exact u16822
  · exact u16823
  · exact u16824
  · exact u16825
  · exact u16826
  · exact u16827
  · exact u16828
  · exact u16829

def b22798 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 200 181 181 245 181 437), lower := (rows 259 98 13 200 16 32 64 128 256), losses := [] }

theorem u22798 : Upper (D 8) (R 8) [258,96,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22799_12 : Upper (D 8) (R 8) [258,96,17,33,12] 13 :=
  permutation_upper _ _ _ [258,96,9,20,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16759

theorem m22799_36 : Upper (D 8) (R 8) [258,96,17,33,36] 13 :=
  permutation_upper _ _ _ [258,96,9,36,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16770

theorem m22799_40 : Upper (D 8) (R 8) [258,96,17,33,40] 13 :=
  permutation_upper _ _ _ [258,96,9,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16776

theorem m22799_68 : Upper (D 8) (R 8) [258,96,17,33,68] 13 :=
  permutation_upper _ _ _ [258,96,9,68,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16788

theorem m22799_72 : Upper (D 8) (R 8) [258,96,17,33,72] 13 :=
  permutation_upper _ _ _ [258,96,9,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16791

theorem m22799_96 : Upper (D 8) (R 8) [258,96,17,33,96] 13 :=
  permutation_upper _ _ _ [258,96,9,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16796

theorem m22799_132 : Upper (D 8) (R 8) [258,96,17,33,132] 13 :=
  permutation_upper _ _ _ [258,96,9,132,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16806

theorem m22799_136 : Upper (D 8) (R 8) [258,96,17,33,136] 13 :=
  permutation_upper _ _ _ [258,96,9,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16812

theorem m22799_160 : Upper (D 8) (R 8) [258,96,17,33,160] 13 :=
  permutation_upper _ _ _ [258,96,9,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16821

theorem m22799_192 : Upper (D 8) (R 8) [258,96,17,33,192] 13 :=
  permutation_upper _ _ _ [258,96,9,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16830

def r22799 : Route 9 := (fun mask => (mask,id))

def c22799 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22799 : Upper (D 8) (R 8) [258,96,17,33] 13 := by
  apply FastRouting.sound _ _ [258,96,17,33] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r22799 c22799
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22799_12
  · exact m22799_36
  · exact m22799_40
  · exact m22799_68
  · exact m22799_72
  · exact m22799_96
  · exact m22799_132
  · exact m22799_136
  · exact m22799_160
  · exact m22799_192

#print axioms u22799
end Delivery.IrregularNine14.P08
