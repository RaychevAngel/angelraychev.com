import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0602
import IrregularNine14P07C0604
import IrregularNine14P07C0605
import IrregularNine14P07C0606
import IrregularNine14P07C0607
import IrregularNine14P07C0608
import IrregularNine14P07C0609
import IrregularNine14P07C0610
import IrregularNine14P07C0611

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b42720 : PairBound 9 := { available := 87, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 322 140 168 87 119 87 215 343), lower := (rows 35 322 140 168 16 32 64 128 256), losses := [] }

theorem u42720 : Upper (D 7) (R 7) [34,320,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42721 : PairBound 9 := { available := 55, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 322 140 200 55 55 119 183 311), lower := (rows 35 322 140 200 16 32 64 128 256), losses := [] }

theorem u42721 : Upper (D 7) (R 7) [34,320,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42722_3 : Upper (D 7) (R 7) [34,320,144,160,3] 13 :=
  permutation_upper _ _ _ [34,320,3,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36130

theorem m42722_5 : Upper (D 7) (R 7) [34,320,144,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36240

theorem m42722_6 : Upper (D 7) (R 7) [34,320,144,160,6] 13 :=
  permutation_upper _ _ _ [34,320,10,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36317

theorem m42722_9 : Upper (D 7) (R 7) [34,320,144,160,9] 13 :=
  permutation_upper _ _ _ [34,320,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36261

theorem m42722_10 : Upper (D 7) (R 7) [34,320,144,160,10] 13 :=
  permutation_upper _ _ _ [34,320,10,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36331

theorem m42722_12 : Upper (D 7) (R 7) [34,320,144,160,12] 13 :=
  permutation_upper _ _ _ [34,320,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36375

theorem m42722_65 : Upper (D 7) (R 7) [34,320,144,160,65] 13 :=
  permutation_upper _ _ _ [34,320,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36450

theorem m42722_66 : Upper (D 7) (R 7) [34,320,144,160,66] 13 :=
  permutation_upper _ _ _ [34,320,66,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36455

theorem m42722_68 : Upper (D 7) (R 7) [34,320,144,160,68] 13 :=
  permutation_upper _ _ _ [34,320,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36465

theorem m42722_72 : Upper (D 7) (R 7) [34,320,144,160,72] 13 :=
  permutation_upper _ _ _ [34,320,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36472

def r42722 : Route 9 := (fun mask => (mask,id))

def c42722 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42722 : Upper (D 7) (R 7) [34,320,144,160] 13 := by
  apply FastRouting.sound _ _ [34,320,144,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42722 c42722
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42722_3
  · exact m42722_5
  · exact m42722_6
  · exact m42722_9
  · exact m42722_10
  · exact m42722_12
  · exact m42722_65
  · exact m42722_66
  · exact m42722_68
  · exact m42722_72

theorem m42723_3 : Upper (D 7) (R 7) [34,320,144,192,3] 13 :=
  permutation_upper _ _ _ [34,320,3,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36131

theorem m42723_5 : Upper (D 7) (R 7) [34,320,144,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36241

theorem m42723_6 : Upper (D 7) (R 7) [34,320,144,192,6] 13 :=
  permutation_upper _ _ _ [34,320,10,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36318

theorem m42723_9 : Upper (D 7) (R 7) [34,320,144,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36269

theorem m42723_10 : Upper (D 7) (R 7) [34,320,144,192,10] 13 :=
  permutation_upper _ _ _ [34,320,10,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36336

theorem m42723_12 : Upper (D 7) (R 7) [34,320,144,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36376

theorem m42723_33 : Upper (D 7) (R 7) [34,320,144,192,33] 13 :=
  permutation_upper _ _ _ [34,320,33,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36393

theorem m42723_34 : Upper (D 7) (R 7) [34,320,144,192,34] 13 :=
  permutation_upper _ _ _ [34,320,34,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36404

theorem m42723_36 : Upper (D 7) (R 7) [34,320,144,192,36] 13 :=
  permutation_upper _ _ _ [34,320,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36431

theorem m42723_40 : Upper (D 7) (R 7) [34,320,144,192,40] 13 :=
  permutation_upper _ _ _ [34,320,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36441

def r42723 : Route 9 := (fun mask => (mask,id))

def c42723 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42723 : Upper (D 7) (R 7) [34,320,144,192] 13 := by
  apply FastRouting.sound _ _ [34,320,144,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r42723 c42723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42723_3
  · exact m42723_5
  · exact m42723_6
  · exact m42723_9
  · exact m42723_10
  · exact m42723_12
  · exact m42723_33
  · exact m42723_34
  · exact m42723_36
  · exact m42723_40

theorem m42724_3 : Upper (D 7) (R 7) [34,320,160,192,3] 13 :=
  permutation_upper _ _ _ [34,320,3,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36132

theorem m42724_5 : Upper (D 7) (R 7) [34,320,160,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36262

theorem m42724_6 : Upper (D 7) (R 7) [34,320,160,192,6] 13 :=
  permutation_upper _ _ _ [34,320,10,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36332

theorem m42724_9 : Upper (D 7) (R 7) [34,320,160,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36270

theorem m42724_10 : Upper (D 7) (R 7) [34,320,160,192,10] 13 :=
  permutation_upper _ _ _ [34,320,10,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36337

theorem m42724_12 : Upper (D 7) (R 7) [34,320,160,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36377

def r42724 : Route 9 := (fun mask => (mask,id))

def c42724 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42724 : Upper (D 7) (R 7) [34,320,160,192] 13 := by
  apply FastRouting.sound _ _ [34,320,160,192] 13 (by decide) (choices 2) [3,5,6,9,10,12] r42724 c42724
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42724_3
  · exact m42724_5
  · exact m42724_6
  · exact m42724_9
  · exact m42724_10
  · exact m42724_12

def b42725 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 25 466 482 450 450 450), lower := (rows 37 42 7 25 16 32 64 128 256), losses := [] }

theorem u42725 : Upper (D 7) (R 7) [36,40,3,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42726 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 26 465 481 449 449 449), lower := (rows 37 42 7 26 16 32 64 128 256), losses := [] }

theorem u42726 : Upper (D 7) (R 7) [36,40,3,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42727 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 73 466 498 466 466 466), lower := (rows 37 42 7 73 16 32 64 128 256), losses := [] }

theorem u42727 : Upper (D 7) (R 7) [36,40,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42728 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 74 465 497 465 465 465), lower := (rows 37 42 7 74 16 32 64 128 256), losses := [] }

theorem u42728 : Upper (D 7) (R 7) [36,40,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42729 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 88 467 483 451 451 451), lower := (rows 37 42 7 88 16 32 64 128 256), losses := [] }

theorem u42729 : Upper (D 7) (R 7) [36,40,3,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42730 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 200 467 499 467 467 467), lower := (rows 37 42 7 200 16 32 64 128 256), losses := [] }

theorem u42730 : Upper (D 7) (R 7) [36,40,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42731 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 265 210 242 210 210 466), lower := (rows 37 42 7 265 16 32 64 128 256), losses := [] }

theorem u42731 : Upper (D 7) (R 7) [36,40,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42732 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 266 209 241 209 209 465), lower := (rows 37 42 7 266 16 32 64 128 256), losses := [] }

theorem u42732 : Upper (D 7) (R 7) [36,40,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42733 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 280 211 227 195 195 451), lower := (rows 37 42 7 280 16 32 64 128 256), losses := [] }

theorem u42733 : Upper (D 7) (R 7) [36,40,3,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42734 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 7 328 211 243 211 211 467), lower := (rows 37 42 7 328 16 32 64 128 256), losses := [] }

theorem u42734 : Upper (D 7) (R 7) [36,40,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42735 : Route 9 := (fun mask => (mask,id))

def c42735 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42735 : Upper (D 7) (R 7) [36,40,17,65] 13 := by
  apply FastRouting.sound _ _ [36,40,17,65] 13 (by decide) (choices 2) [66,130,192,258,320,384] r42735 c42735
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36481
  · exact u36482
  · exact u36483
  · exact u36484
  · exact u36485
  · exact u36486

def r42736 : Route 9 := (fun mask => (mask,id))

def c42736 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42736 : Upper (D 7) (R 7) [36,40,17,66] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42736 c42736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36487
  · exact u36488
  · exact u36489
  · exact u36490
  · exact u36491
  · exact u36492
  · exact u36493
  · exact u36494
  · exact u36495
  · exact u36496

def r42737 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42737 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42737 : Upper (D 7) (R 7) [36,40,17,192] 13 := by
  apply FastRouting.sound _ _ [36,40,17,192] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r42737 c42737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36497
  · exact u36498
  · exact u36499
  · exact u36500
  · exact u36501
  · exact u36502
  · exact u36503

def r42738 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42738 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42738 : Upper (D 7) (R 7) [36,40,17,257] 13 := by
  apply FastRouting.sound _ _ [36,40,17,257] 13 (by decide) (choices 2) [66,192] r42738 c42738
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u36504
  · exact u36505

def r42739 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42739 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42739 : Upper (D 7) (R 7) [36,40,17,258] 13 := by
  apply FastRouting.sound _ _ [36,40,17,258] 13 (by decide) (choices 2) [3,65,66,192] r42739 c42739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u36506
  · exact u36507
  · exact u36508
  · exact u36509

def r42740 : Route 9 := (fun mask => (mask,id))

def c42740 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42740 : Upper (D 7) (R 7) [36,40,17,320] 13 := by
  apply FastRouting.sound _ _ [36,40,17,320] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42740 c42740
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36510
  · exact u36511
  · exact u36512
  · exact u36513
  · exact u36514
  · exact u36515

def r42741 : Route 9 := (fun mask => (mask,id))

def c42741 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42741 : Upper (D 7) (R 7) [36,40,18,65] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42741 c42741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36516
  · exact u36517
  · exact u36518
  · exact u36519
  · exact u36520
  · exact u36521
  · exact u36522
  · exact u36523
  · exact u36524
  · exact u36525

def r42742 : Route 9 := (fun mask => (mask,id))

def c42742 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42742 : Upper (D 7) (R 7) [36,40,18,66] 13 := by
  apply FastRouting.sound _ _ [36,40,18,66] 13 (by decide) (choices 2) [65,129,192,257,320,384] r42742 c42742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36526
  · exact u36527
  · exact u36528
  · exact u36529
  · exact u36530
  · exact u36531

def r42743 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42743 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42743 : Upper (D 7) (R 7) [36,40,18,192] 13 := by
  apply FastRouting.sound _ _ [36,40,18,192] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r42743 c42743
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36532
  · exact u36533
  · exact u36534
  · exact u36535
  · exact u36536
  · exact u36537
  · exact u36538

def r42744 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42744 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42744 : Upper (D 7) (R 7) [36,40,18,257] 13 := by
  apply FastRouting.sound _ _ [36,40,18,257] 13 (by decide) (choices 2) [3,65,66,192] r42744 c42744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u36539
  · exact u36540
  · exact u36541
  · exact u36542

def r42745 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42745 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42745 : Upper (D 7) (R 7) [36,40,18,258] 13 := by
  apply FastRouting.sound _ _ [36,40,18,258] 13 (by decide) (choices 2) [65,192] r42745 c42745
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u36543
  · exact u36544

def r42746 : Route 9 := (fun mask => (mask,id))

def c42746 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42746 : Upper (D 7) (R 7) [36,40,18,320] 13 := by
  apply FastRouting.sound _ _ [36,40,18,320] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42746 c42746
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36545
  · exact u36546
  · exact u36547
  · exact u36548
  · exact u36549
  · exact u36550

def b42747 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 37 42 69 73 402 434 466 402 402), lower := (rows 37 42 69 73 16 32 64 128 256), losses := [] }

theorem u42747 : Upper (D 7) (R 7) [36,40,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42748 : PairBound 9 := { available := 403, camps := [], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 42 69 74 403 435 467 403 403), lower := (rows 37 42 69 74 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 3 4 12 16 32 64 128 256), good := (rows 46 42 78 74 16 32 64 128 256) },{ target := 1, region := (rows 3 0 12 8 16 32 64 128 256), good := (rows 37 45 69 77 16 32 64 128 256) }] }

theorem u42748 : Upper (D 7) (R 7) [36,40,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42749 : Route 9 := (fun mask => (mask,id))

def c42749 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42749 : Upper (D 7) (R 7) [36,40,65,80] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42749 c42749
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36551
  · exact u36552
  · exact u36553
  · exact u36554
  · exact u36555
  · exact u36556

def r42750 : Route 9 := (fun mask => (mask,id))

def c42750 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42750 : Upper (D 7) (R 7) [36,40,65,129] 13 := by
  apply FastRouting.sound _ _ [36,40,65,129] 13 (by decide) (choices 2) [66,130,192,258,320,384] r42750 c42750
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36557
  · exact u36558
  · exact u36559
  · exact u36560
  · exact u36561
  · exact u36562

theorem m42751_129 : Upper (D 7) (R 7) [36,40,65,130,129] 13 :=
  permutation_upper _ _ _ [36,40,65,130,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36565

theorem m42751_130 : Upper (D 7) (R 7) [36,40,65,130,130] 13 :=
  permutation_upper _ _ _ [36,40,65,130,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36564

theorem m42751_258 : Upper (D 7) (R 7) [36,40,65,130,258] 13 :=
  permutation_upper _ _ _ [36,40,65,130,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36567

theorem m42751_384 : Upper (D 7) (R 7) [36,40,65,130,384] 13 :=
  permutation_upper _ _ _ [36,40,65,130,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36568

def r42751 : Route 9 := (fun mask => (mask,id))

def c42751 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42751 : Upper (D 7) (R 7) [36,40,65,130] 13 := by
  apply FastRouting.sound _ _ [36,40,65,130] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42751 c42751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36563
  · exact u36564
  · exact u36565
  · exact m42751_129
  · exact m42751_130
  · exact u36566
  · exact u36567
  · exact m42751_258
  · exact u36568
  · exact m42751_384

def r42752 : Route 9 := (fun mask => (mask,id))

def c42752 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42752 : Upper (D 7) (R 7) [36,40,65,144] 13 := by
  apply FastRouting.sound _ _ [36,40,65,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42752 c42752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36569
  · exact u36570
  · exact u36571
  · exact u36572
  · exact u36573
  · exact u36574
  · exact u36575
  · exact u36576
  · exact u36577
  · exact u36578

def r42753 : Route 9 := (fun mask => (mask,id))

def c42753 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42753 : Upper (D 7) (R 7) [36,40,65,192] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42753 c42753
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36579
  · exact u36580
  · exact u36581
  · exact u36582
  · exact u36583
  · exact u36584

def r42754 : Route 9 := (fun mask => (mask,id))

def c42754 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42754 : Upper (D 7) (R 7) [36,40,65,257] 13 := by
  apply FastRouting.sound _ _ [36,40,65,257] 13 (by decide) (choices 2) [66,130,192] r42754 c42754
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36585
  · exact u36586
  · exact u36587

def r42755 : Route 9 := (fun mask => (mask,id))

def c42755 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42755 : Upper (D 7) (R 7) [36,40,65,258] 13 := by
  apply FastRouting.sound _ _ [36,40,65,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42755 c42755
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36588
  · exact u36589
  · exact u36590
  · exact u36591
  · exact u36592
  · exact u36593

def r42756 : Route 9 := (fun mask => (mask,id))

def c42756 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42756 : Upper (D 7) (R 7) [36,40,65,272] 13 := by
  apply FastRouting.sound _ _ [36,40,65,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42756 c42756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36594
  · exact u36595
  · exact u36596
  · exact u36597
  · exact u36598
  · exact u36599

def r42757 : Route 9 := (fun mask => (mask,id))

def c42757 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42757 : Upper (D 7) (R 7) [36,40,65,320] 13 := by
  apply FastRouting.sound _ _ [36,40,65,320] 13 (by decide) (choices 2) [3,129,130] r42757 c42757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36600
  · exact u36601
  · exact u36602

def r42758 : Route 9 := (fun mask => (mask,id))

def c42758 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42758 : Upper (D 7) (R 7) [36,40,65,384] 13 := by
  apply FastRouting.sound _ _ [36,40,65,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42758 c42758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36603
  · exact u36604
  · exact u36605
  · exact u36606
  · exact u36607
  · exact u36608

def b42759 : PairBound 9 := { available := 403, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 3, region := 434, targets := 64 }], pairs := [(0,6),(0,7),(1,6),(4,6)], upper := (rows 37 42 70 73 403 435 467 403 403), lower := (rows 37 42 70 73 16 32 64 128 256), losses := [{ target := 7, region := (rows 3 3 12 12 16 32 64 0 256), good := (rows 47 47 79 79 16 32 64 0 256) }] }

theorem u42759 : Upper (D 7) (R 7) [36,40,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42760 : Route 9 := (fun mask => (mask,id))

def c42760 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42760 : Upper (D 7) (R 7) [36,40,66,80] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42760 c42760
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36609
  · exact u36610
  · exact u36611
  · exact u36612
  · exact u36613
  · exact u36614

theorem m42761_129 : Upper (D 7) (R 7) [36,40,66,129,129] 13 :=
  permutation_upper _ _ _ [36,40,66,129,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36617

theorem m42761_130 : Upper (D 7) (R 7) [36,40,66,129,130] 13 :=
  permutation_upper _ _ _ [36,40,66,129,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36616

theorem m42761_258 : Upper (D 7) (R 7) [36,40,66,129,258] 13 :=
  permutation_upper _ _ _ [36,40,66,129,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36619

theorem m42761_384 : Upper (D 7) (R 7) [36,40,66,129,384] 13 :=
  permutation_upper _ _ _ [36,40,66,129,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u36620

def r42761 : Route 9 := (fun mask => (mask,id))

def c42761 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42761 : Upper (D 7) (R 7) [36,40,66,129] 13 := by
  apply FastRouting.sound _ _ [36,40,66,129] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42761 c42761
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36615
  · exact u36616
  · exact u36617
  · exact m42761_129
  · exact m42761_130
  · exact u36618
  · exact u36619
  · exact m42761_258
  · exact u36620
  · exact m42761_384

def r42762 : Route 9 := (fun mask => (mask,id))

def c42762 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42762 : Upper (D 7) (R 7) [36,40,66,144] 13 := by
  apply FastRouting.sound _ _ [36,40,66,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42762 c42762
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36621
  · exact u36622
  · exact u36623
  · exact u36624
  · exact u36625
  · exact u36626
  · exact u36627
  · exact u36628
  · exact u36629
  · exact u36630

def r42763 : Route 9 := (fun mask => (mask,id))

def c42763 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42763 : Upper (D 7) (R 7) [36,40,66,192] 13 := by
  apply FastRouting.sound _ _ [36,40,66,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42763 c42763
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36631
  · exact u36632
  · exact u36633
  · exact u36634
  · exact u36635
  · exact u36636

def r42764 : Route 9 := (fun mask => (mask,id))

def c42764 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42764 : Upper (D 7) (R 7) [36,40,66,257] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42764 c42764
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36637
  · exact u36638
  · exact u36639
  · exact u36640
  · exact u36641
  · exact u36642

def r42765 : Route 9 := (fun mask => (mask,id))

def c42765 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42765 : Upper (D 7) (R 7) [36,40,66,258] 13 := by
  apply FastRouting.sound _ _ [36,40,66,258] 13 (by decide) (choices 2) [65,129,192] r42765 c42765
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36643
  · exact u36644
  · exact u36645

def r42766 : Route 9 := (fun mask => (mask,id))

def c42766 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42766 : Upper (D 7) (R 7) [36,40,66,272] 13 := by
  apply FastRouting.sound _ _ [36,40,66,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42766 c42766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36646
  · exact u36647
  · exact u36648
  · exact u36649
  · exact u36650
  · exact u36651

def r42767 : Route 9 := (fun mask => (mask,id))

def c42767 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42767 : Upper (D 7) (R 7) [36,40,66,320] 13 := by
  apply FastRouting.sound _ _ [36,40,66,320] 13 (by decide) (choices 2) [3,129,130] r42767 c42767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36652
  · exact u36653
  · exact u36654

def r42768 : Route 9 := (fun mask => (mask,id))

def c42768 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42768 : Upper (D 7) (R 7) [36,40,66,384] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42768 c42768
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36655
  · exact u36656
  · exact u36657
  · exact u36658
  · exact u36659
  · exact u36660

def r42769 : Route 9 := (fun mask => (mask,id))

def c42769 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42769 : Upper (D 7) (R 7) [36,40,80,192] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42769 c42769
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36661
  · exact u36662
  · exact u36663
  · exact u36664
  · exact u36665
  · exact u36666

def r42770 : Route 9 := (fun mask => (mask,id))

def c42770 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42770 : Upper (D 7) (R 7) [36,40,80,257] 13 := by
  apply FastRouting.sound _ _ [36,40,80,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42770 c42770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36667
  · exact u36668
  · exact u36669
  · exact u36670
  · exact u36671
  · exact u36672

def r42771 : Route 9 := (fun mask => (mask,id))

def c42771 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42771 : Upper (D 7) (R 7) [36,40,80,258] 13 := by
  apply FastRouting.sound _ _ [36,40,80,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42771 c42771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36673
  · exact u36674
  · exact u36675
  · exact u36676
  · exact u36677
  · exact u36678

def r42772 : Route 9 := (fun mask => (mask,id))

def c42772 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42772 : Upper (D 7) (R 7) [36,40,80,320] 13 := by
  apply FastRouting.sound _ _ [36,40,80,320] 13 (by decide) (choices 2) [3,129,130] r42772 c42772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36679
  · exact u36680
  · exact u36681

def r42773 : Route 9 := (fun mask => (mask,id))

def c42773 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42773 : Upper (D 7) (R 7) [36,40,80,384] 13 := by
  apply FastRouting.sound _ _ [36,40,80,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42773 c42773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36682
  · exact u36683
  · exact u36684
  · exact u36685
  · exact u36686
  · exact u36687

def b42774 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 37 42 196 200 275 307 339 403 275), lower := (rows 37 42 196 200 16 32 64 128 256), losses := [] }

theorem u42774 : Upper (D 7) (R 7) [36,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42775 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42775 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42775 : Upper (D 7) (R 7) [36,40,192,257] 13 := by
  apply FastRouting.sound _ _ [36,40,192,257] 13 (by decide) (choices 2) [3,65,66,192] r42775 c42775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u36688
  · exact u36689
  · exact u36690
  · exact u36691

def r42776 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42776 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42776 : Upper (D 7) (R 7) [36,40,192,258] 13 := by
  apply FastRouting.sound _ _ [36,40,192,258] 13 (by decide) (choices 2) [3,65,66,192] r42776 c42776
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u36692
  · exact u36693
  · exact u36694
  · exact u36695

def r42777 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42777 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42777 : Upper (D 7) (R 7) [36,40,192,272] 13 := by
  apply FastRouting.sound _ _ [36,40,192,272] 13 (by decide) (choices 2) [3,65,66,192] r42777 c42777
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u36696
  · exact u36697
  · exact u36698
  · exact u36699

def r42778 : Route 9 := (fun mask => (mask,id))

def c42778 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42778 : Upper (D 7) (R 7) [36,40,192,320] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320] 13 (by decide) (choices 2) [3,129,130] r42778 c42778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36700
  · exact u36701
  · exact u36702

def b42779 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 74 7 11 496 496 496 496 496), lower := (rows 37 74 7 11 16 32 64 128 256), losses := [] }

theorem u42779 : Upper (D 7) (R 7) [36,72,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u42779
end Delivery.IrregularNine14.P07
