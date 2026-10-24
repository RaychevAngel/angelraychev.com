import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0003
import IrregularNine14P04C0004
import IrregularNine14P04C0005
import IrregularNine14P04C0006
import IrregularNine14P04C0007
import IrregularNine14P04C0008
import IrregularNine14P04C0009
import IrregularNine14P04C0010
import IrregularNine14P04C0011

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m720_5 : Upper (D 4) (R 4) [18,36,66,384,5] 13 :=
  permutation_upper _ _ _ [6,9,40,68,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u305

theorem m720_9 : Upper (D 4) (R 4) [18,36,66,384,9] 13 :=
  permutation_upper _ _ _ [6,9,48,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u328

theorem m720_12 : Upper (D 4) (R 4) [18,36,66,384,12] 13 :=
  permutation_upper _ _ _ [6,24,40,68,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u426

def r720 : Route 9 := (fun mask => (mask,id))

def c720 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u720 : Upper (D 4) (R 4) [18,36,66,384] 13 := by
  apply FastRouting.sound _ _ [18,36,66,384] 13 (by decide) (choices 2) [5,9,12] r720 c720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m720_5
  · exact m720_9
  · exact m720_12

theorem m721_3 : Upper (D 4) (R 4) [18,36,72,129,3] 13 :=
  permutation_upper _ _ _ [6,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u233

theorem m721_5 : Upper (D 4) (R 4) [18,36,72,129,5] 13 :=
  permutation_upper _ _ _ [6,9,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u306

theorem m721_6 : Upper (D 4) (R 4) [18,36,72,129,6] 13 :=
  permutation_upper _ _ _ [6,12,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u366

theorem m721_9 : Upper (D 4) (R 4) [18,36,72,129,9] 13 :=
  permutation_upper _ _ _ [6,9,34,80,132] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u297

theorem m721_10 : Upper (D 4) (R 4) [18,36,72,129,10] 13 :=
  permutation_upper _ _ _ [6,12,48,65,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u373

theorem m721_12 : Upper (D 4) (R 4) [18,36,72,129,12] 13 :=
  permutation_upper _ _ _ [6,24,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u427

theorem m721_257 : Upper (D 4) (R 4) [18,36,72,129,257] 13 :=
  permutation_upper _ _ _ [6,33,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u475

theorem m721_258 : Upper (D 4) (R 4) [18,36,72,129,258] 13 :=
  permutation_upper _ _ _ [6,36,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u498

theorem m721_260 : Upper (D 4) (R 4) [18,36,72,129,260] 13 :=
  permutation_upper _ _ _ [6,40,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u506

theorem m721_264 : Upper (D 4) (R 4) [18,36,72,129,264] 13 :=
  permutation_upper _ _ _ [6,40,80,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 8 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u511

def r721 : Route 9 := (fun mask => (mask,id))

def c721 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u721 : Upper (D 4) (R 4) [18,36,72,129] 13 := by
  apply FastRouting.sound _ _ [18,36,72,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r721 c721
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m721_3
  · exact m721_5
  · exact m721_6
  · exact m721_9
  · exact m721_10
  · exact m721_12
  · exact m721_257
  · exact m721_258
  · exact m721_260
  · exact m721_264

theorem m722_5 : Upper (D 4) (R 4) [18,36,72,130,5] 13 :=
  permutation_upper _ _ _ [6,9,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u308

theorem m722_9 : Upper (D 4) (R 4) [18,36,72,130,9] 13 :=
  permutation_upper _ _ _ [6,9,40,80,132] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u308

theorem m722_12 : Upper (D 4) (R 4) [18,36,72,130,12] 13 :=
  permutation_upper _ _ _ [6,24,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u428

theorem m722_257 : Upper (D 4) (R 4) [18,36,72,130,257] 13 :=
  permutation_upper _ _ _ [6,33,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u477

theorem m722_260 : Upper (D 4) (R 4) [18,36,72,130,260] 13 :=
  permutation_upper _ _ _ [6,40,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u507

theorem m722_264 : Upper (D 4) (R 4) [18,36,72,130,264] 13 :=
  permutation_upper _ _ _ [6,40,80,132,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 8 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u515

def r722 : Route 9 := (fun mask => (mask,id))

def c722 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u722 : Upper (D 4) (R 4) [18,36,72,130] 13 := by
  apply FastRouting.sound _ _ [18,36,72,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r722 c722
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m722_5
  · exact m722_9
  · exact m722_12
  · exact m722_257
  · exact m722_260
  · exact m722_264

theorem m723_3 : Upper (D 4) (R 4) [18,36,72,132,3] 13 :=
  permutation_upper _ _ _ [6,5,40,80,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u234

theorem m723_9 : Upper (D 4) (R 4) [18,36,72,132,9] 13 :=
  permutation_upper _ _ _ [6,9,48,80,132] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u318

theorem m723_10 : Upper (D 4) (R 4) [18,36,72,132,10] 13 :=
  permutation_upper _ _ _ [6,12,48,80,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u381

theorem m723_257 : Upper (D 4) (R 4) [18,36,72,132,257] 13 :=
  permutation_upper _ _ _ [6,33,72,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u478

theorem m723_258 : Upper (D 4) (R 4) [18,36,72,132,258] 13 :=
  permutation_upper _ _ _ [6,36,72,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u500

theorem m723_264 : Upper (D 4) (R 4) [18,36,72,132,264] 13 :=
  permutation_upper _ _ _ [6,40,80,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u516

def r723 : Route 9 := (fun mask => (mask,id))

def c723 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u723 : Upper (D 4) (R 4) [18,36,72,132] 13 := by
  apply FastRouting.sound _ _ [18,36,72,132] 13 (by decide) (choices 2) [3,9,10,257,258,264] r723 c723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m723_3
  · exact m723_9
  · exact m723_10
  · exact m723_257
  · exact m723_258
  · exact m723_264

theorem m724_3 : Upper (D 4) (R 4) [18,36,72,384,3] 13 :=
  permutation_upper _ _ _ [6,5,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u235

theorem m724_5 : Upper (D 4) (R 4) [18,36,72,384,5] 13 :=
  permutation_upper _ _ _ [6,9,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u309

theorem m724_6 : Upper (D 4) (R 4) [18,36,72,384,6] 13 :=
  permutation_upper _ _ _ [6,12,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u367

theorem m724_9 : Upper (D 4) (R 4) [18,36,72,384,9] 13 :=
  permutation_upper _ _ _ [6,9,48,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u329

theorem m724_10 : Upper (D 4) (R 4) [18,36,72,384,10] 13 :=
  permutation_upper _ _ _ [6,12,48,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u386

theorem m724_12 : Upper (D 4) (R 4) [18,36,72,384,12] 13 :=
  permutation_upper _ _ _ [6,24,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u429

def r724 : Route 9 := (fun mask => (mask,id))

def c724 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u724 : Upper (D 4) (R 4) [18,36,72,384] 13 := by
  apply FastRouting.sound _ _ [18,36,72,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r724 c724
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m724_3
  · exact m724_5
  · exact m724_6
  · exact m724_9
  · exact m724_10
  · exact m724_12

theorem m725_3 : Upper (D 4) (R 4) [18,36,192,257,3] 13 :=
  permutation_upper _ _ _ [6,5,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u237

theorem m725_5 : Upper (D 4) (R 4) [18,36,192,257,5] 13 :=
  permutation_upper _ _ _ [6,9,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u310

theorem m725_6 : Upper (D 4) (R 4) [18,36,192,257,6] 13 :=
  permutation_upper _ _ _ [6,12,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u368

theorem m725_9 : Upper (D 4) (R 4) [18,36,192,257,9] 13 :=
  permutation_upper _ _ _ [6,9,34,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u299

theorem m725_10 : Upper (D 4) (R 4) [18,36,192,257,10] 13 :=
  permutation_upper _ _ _ [6,12,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u374

theorem m725_12 : Upper (D 4) (R 4) [18,36,192,257,12] 13 :=
  permutation_upper _ _ _ [6,24,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u430

def r725 : Route 9 := (fun mask => (mask,id))

def c725 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u725 : Upper (D 4) (R 4) [18,36,192,257] 13 := by
  apply FastRouting.sound _ _ [18,36,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12] r725 c725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m725_3
  · exact m725_5
  · exact m725_6
  · exact m725_9
  · exact m725_10
  · exact m725_12

theorem m726_5 : Upper (D 4) (R 4) [18,36,192,258,5] 13 :=
  permutation_upper _ _ _ [6,9,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u312

theorem m726_9 : Upper (D 4) (R 4) [18,36,192,258,9] 13 :=
  permutation_upper _ _ _ [6,9,40,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u309

theorem m726_12 : Upper (D 4) (R 4) [18,36,192,258,12] 13 :=
  permutation_upper _ _ _ [6,24,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u432

def r726 : Route 9 := (fun mask => (mask,id))

def c726 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u726 : Upper (D 4) (R 4) [18,36,192,258] 13 := by
  apply FastRouting.sound _ _ [18,36,192,258] 13 (by decide) (choices 2) [5,9,12] r726 c726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m726_5
  · exact m726_9
  · exact m726_12

theorem m727_3 : Upper (D 4) (R 4) [18,36,192,260,3] 13 :=
  permutation_upper _ _ _ [6,5,40,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u238

theorem m727_9 : Upper (D 4) (R 4) [18,36,192,260,9] 13 :=
  permutation_upper _ _ _ [6,9,48,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u319

theorem m727_10 : Upper (D 4) (R 4) [18,36,192,260,10] 13 :=
  permutation_upper _ _ _ [6,12,48,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u382

def r727 : Route 9 := (fun mask => (mask,id))

def c727 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u727 : Upper (D 4) (R 4) [18,36,192,260] 13 := by
  apply FastRouting.sound _ _ [18,36,192,260] 13 (by decide) (choices 2) [3,9,10] r727 c727
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m727_3
  · exact m727_9
  · exact m727_10

def b728 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 460, targets := 16 }], pairs := [(2,4)], upper := (rows 19 50 69 140 287 303 335 399 271), lower := (rows 19 50 69 140 16 32 64 128 256), losses := [] }

theorem u728 : Upper (D 4) (R 4) [18,48,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b728
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 460, targets := 16 }], pairs := [(2,4)], upper := (rows 19 50 69 392 31 47 79 143 271), lower := (rows 19 50 69 392 16 32 64 128 256), losses := [] }

theorem u729 : Upper (D 4) (R 4) [18,48,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b729
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 460, targets := 16 }], pairs := [(2,4)], upper := (rows 19 50 76 140 287 303 335 399 271), lower := (rows 19 50 76 140 16 32 64 128 256), losses := [] }

theorem u730 : Upper (D 4) (R 4) [18,48,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b730
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b731 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 460, targets := 16 }], pairs := [(2,4)], upper := (rows 19 50 76 392 31 47 79 143 271), lower := (rows 19 50 76 392 16 32 64 128 256), losses := [] }

theorem u731 : Upper (D 4) (R 4) [18,48,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b731
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m732_5 : Upper (D 4) (R 4) [18,96,129,258,5] 13 :=
  permutation_upper _ _ _ [6,9,34,192,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u303

theorem m732_9 : Upper (D 4) (R 4) [18,96,129,258,9] 13 :=
  permutation_upper _ _ _ [6,9,40,192,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u311

theorem m732_12 : Upper (D 4) (R 4) [18,96,129,258,12] 13 :=
  permutation_upper _ _ _ [6,24,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u435

def r732 : Route 9 := (fun mask => (mask,id))

def c732 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u732 : Upper (D 4) (R 4) [18,96,129,258] 13 := by
  apply FastRouting.sound _ _ [18,96,129,258] 13 (by decide) (choices 2) [5,9,12] r732 c732
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m732_5
  · exact m732_9
  · exact m732_12

theorem m733_3 : Upper (D 4) (R 4) [18,96,129,260,3] 13 :=
  permutation_upper _ _ _ [6,5,96,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u241

theorem m733_5 : Upper (D 4) (R 4) [18,96,129,260,5] 13 :=
  permutation_upper _ _ _ [6,9,34,192,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u302

theorem m733_6 : Upper (D 4) (R 4) [18,96,129,260,6] 13 :=
  permutation_upper _ _ _ [6,12,96,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u391

theorem m733_9 : Upper (D 4) (R 4) [18,96,129,260,9] 13 :=
  permutation_upper _ _ _ [6,9,48,192,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u327

theorem m733_10 : Upper (D 4) (R 4) [18,96,129,260,10] 13 :=
  permutation_upper _ _ _ [6,12,96,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u396

theorem m733_12 : Upper (D 4) (R 4) [18,96,129,260,12] 13 :=
  permutation_upper _ _ _ [6,24,96,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u436

def r733 : Route 9 := (fun mask => (mask,id))

def c733 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u733 : Upper (D 4) (R 4) [18,96,129,260] 13 := by
  apply FastRouting.sound _ _ [18,96,129,260] 13 (by decide) (choices 2) [3,5,6,9,10,12] r733 c733
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m733_3
  · exact m733_5
  · exact m733_6
  · exact m733_9
  · exact m733_10
  · exact m733_12

theorem m734_5 : Upper (D 4) (R 4) [18,96,130,260,5] 13 :=
  permutation_upper _ _ _ [6,9,40,192,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u312

theorem m734_9 : Upper (D 4) (R 4) [18,96,130,260,9] 13 :=
  permutation_upper _ _ _ [6,9,48,192,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u329

theorem m734_12 : Upper (D 4) (R 4) [18,96,130,260,12] 13 :=
  permutation_upper _ _ _ [6,24,96,132,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u439

def r734 : Route 9 := (fun mask => (mask,id))

def c734 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u734 : Upper (D 4) (R 4) [18,96,130,260] 13 := by
  apply FastRouting.sound _ _ [18,96,130,260] 13 (by decide) (choices 2) [5,9,12] r734 c734
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m734_5
  · exact m734_9
  · exact m734_12

theorem m735_3 : Upper (D 4) (R 4) [18,96,136,260,3] 13 :=
  permutation_upper _ _ _ [6,5,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u242

theorem m735_5 : Upper (D 4) (R 4) [18,96,136,260,5] 13 :=
  permutation_upper _ _ _ [6,9,48,192,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u328

theorem m735_6 : Upper (D 4) (R 4) [18,96,136,260,6] 13 :=
  permutation_upper _ _ _ [6,12,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u398

theorem m735_9 : Upper (D 4) (R 4) [18,96,136,260,9] 13 :=
  permutation_upper _ _ _ [6,9,48,192,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u328

theorem m735_10 : Upper (D 4) (R 4) [18,96,136,260,10] 13 :=
  permutation_upper _ _ _ [6,12,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u398

theorem m735_12 : Upper (D 4) (R 4) [18,96,136,260,12] 13 :=
  permutation_upper _ _ _ [6,24,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u440

def r735 : Route 9 := (fun mask => (mask,id))

def c735 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u735 : Upper (D 4) (R 4) [18,96,136,260] 13 := by
  apply FastRouting.sound _ _ [18,96,136,260] 13 (by decide) (choices 2) [3,5,6,9,10,12] r735 c735
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m735_3
  · exact m735_5
  · exact m735_6
  · exact m735_9
  · exact m735_10
  · exact m735_12

theorem m736_12 : Upper (D 4) (R 4) [34,65,129,258,12] 13 :=
  permutation_upper _ _ _ [6,40,80,144,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u516

def r736 : Route 9 := (fun mask => (mask,id))

def c736 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u736 : Upper (D 4) (R 4) [34,65,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258] 13 (by decide) (choices 2) [12] r736 c736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact m736_12

theorem m737_6 : Upper (D 4) (R 4) [34,65,129,260,6] 13 :=
  permutation_upper _ _ _ [6,40,72,130,260] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u505

theorem m737_10 : Upper (D 4) (R 4) [34,65,129,260,10] 13 :=
  permutation_upper _ _ _ [6,40,80,130,264] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 8 | 7 => 5 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u513

theorem m737_12 : Upper (D 4) (R 4) [34,65,129,260,12] 13 :=
  permutation_upper _ _ _ [6,36,72,144,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u500

def r737 : Route 9 := (fun mask => (mask,id))

def c737 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u737 : Upper (D 4) (R 4) [34,65,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260] 13 (by decide) (choices 2) [6,10,12] r737 c737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m737_6
  · exact m737_10
  · exact m737_12

theorem m738_6 : Upper (D 4) (R 4) [34,65,129,272,6] 13 :=
  permutation_upper _ _ _ [6,40,72,130,257] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u504

theorem m738_10 : Upper (D 4) (R 4) [34,65,129,272,10] 13 :=
  permutation_upper _ _ _ [6,33,72,132,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 6 | 7 => 5 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u473

theorem m738_12 : Upper (D 4) (R 4) [34,65,129,272,12] 13 :=
  permutation_upper _ _ _ [6,33,72,144,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u478

def r738 : Route 9 := (fun mask => (mask,id))

def c738 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u738 : Upper (D 4) (R 4) [34,65,129,272] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272] 13 (by decide) (choices 2) [6,10,12] r738 c738
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m738_6
  · exact m738_10
  · exact m738_12

theorem m739_3 : Upper (D 4) (R 4) [34,65,136,260,3] 13 :=
  permutation_upper _ _ _ [6,36,66,144,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u490

theorem m739_5 : Upper (D 4) (R 4) [34,65,136,260,5] 13 :=
  permutation_upper _ _ _ [6,40,80,130,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u512

theorem m739_6 : Upper (D 4) (R 4) [34,65,136,260,6] 13 :=
  permutation_upper _ _ _ [6,40,80,130,260] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u512

theorem m739_9 : Upper (D 4) (R 4) [34,65,136,260,9] 13 :=
  permutation_upper _ _ _ [6,40,80,130,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u512

theorem m739_10 : Upper (D 4) (R 4) [34,65,136,260,10] 13 :=
  permutation_upper _ _ _ [6,40,80,130,260] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 8 | 7 => 5 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u512

theorem m739_12 : Upper (D 4) (R 4) [34,65,136,260,12] 13 :=
  permutation_upper _ _ _ [6,36,66,144,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u490

def r739 : Route 9 := (fun mask => (mask,id))

def c739 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u739 : Upper (D 4) (R 4) [34,65,136,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260] 13 (by decide) (choices 2) [3,5,6,9,10,12] r739 c739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m739_3
  · exact m739_5
  · exact m739_6
  · exact m739_9
  · exact m739_10
  · exact m739_12

theorem m740_3 : Upper (D 4) (R 4) [34,65,136,272,3] 13 :=
  permutation_upper _ _ _ [6,36,66,129,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u489

theorem m740_5 : Upper (D 4) (R 4) [34,65,136,272,5] 13 :=
  permutation_upper _ _ _ [6,40,80,129,260] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 7 | 6 => 5 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 8 | 7 => 5 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u510

theorem m740_6 : Upper (D 4) (R 4) [34,65,136,272,6] 13 :=
  permutation_upper _ _ _ [6,40,80,129,260] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 5 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u510

theorem m740_9 : Upper (D 4) (R 4) [34,65,136,272,9] 13 :=
  permutation_upper _ _ _ [6,33,72,132,258] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u472

theorem m740_10 : Upper (D 4) (R 4) [34,65,136,272,10] 13 :=
  permutation_upper _ _ _ [6,33,72,132,258] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 6 | 7 => 5 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u472

theorem m740_12 : Upper (D 4) (R 4) [34,65,136,272,12] 13 :=
  permutation_upper _ _ _ [6,33,66,144,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u451

def r740 : Route 9 := (fun mask => (mask,id))

def c740 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u740 : Upper (D 4) (R 4) [34,65,136,272] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272] 13 (by decide) (choices 2) [3,5,6,9,10,12] r740 c740
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m740_3
  · exact m740_5
  · exact m740_6
  · exact m740_9
  · exact m740_10
  · exact m740_12

theorem m741_6 : Upper (D 4) (R 4) [34,68,129,257,6] 13 :=
  permutation_upper _ _ _ [6,36,72,130,264] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u497

theorem m741_10 : Upper (D 4) (R 4) [34,68,129,257,10] 13 :=
  permutation_upper _ _ _ [6,40,80,132,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 6 | 7 => 5 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u515

theorem m741_12 : Upper (D 4) (R 4) [34,68,129,257,12] 13 :=
  permutation_upper _ _ _ [6,40,72,144,258] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u507

def r741 : Route 9 := (fun mask => (mask,id))

def c741 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u741 : Upper (D 4) (R 4) [34,68,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257] 13 (by decide) (choices 2) [6,10,12] r741 c741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m741_6
  · exact m741_10
  · exact m741_12

theorem m742_3 : Upper (D 4) (R 4) [34,68,129,272,3] 13 :=
  permutation_upper _ _ _ [6,36,72,130,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u496

theorem m742_5 : Upper (D 4) (R 4) [34,68,129,272,5] 13 :=
  permutation_upper _ _ _ [6,36,72,130,257] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u496

theorem m742_6 : Upper (D 4) (R 4) [34,68,129,272,6] 13 :=
  permutation_upper _ _ _ [6,36,72,130,257] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u496

theorem m742_9 : Upper (D 4) (R 4) [34,68,129,272,9] 13 :=
  permutation_upper _ _ _ [6,33,72,144,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u477

theorem m742_10 : Upper (D 4) (R 4) [34,68,129,272,10] 13 :=
  permutation_upper _ _ _ [6,33,72,144,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u477

theorem m742_12 : Upper (D 4) (R 4) [34,68,129,272,12] 13 :=
  permutation_upper _ _ _ [6,33,72,144,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u477

def r742 : Route 9 := (fun mask => (mask,id))

def c742 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u742 : Upper (D 4) (R 4) [34,68,129,272] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272] 13 (by decide) (choices 2) [3,5,6,9,10,12] r742 c742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m742_3
  · exact m742_5
  · exact m742_6
  · exact m742_9
  · exact m742_10
  · exact m742_12

theorem m743_3 : Upper (D 4) (R 4) [34,68,136,257,3] 13 :=
  permutation_upper _ _ _ [6,36,72,144,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u499

theorem m743_5 : Upper (D 4) (R 4) [34,68,136,257,5] 13 :=
  permutation_upper _ _ _ [6,40,80,132,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u514

theorem m743_6 : Upper (D 4) (R 4) [34,68,136,257,6] 13 :=
  permutation_upper _ _ _ [6,36,72,144,258] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u499

theorem m743_9 : Upper (D 4) (R 4) [34,68,136,257,9] 13 :=
  permutation_upper _ _ _ [6,36,72,144,258] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u499

theorem m743_10 : Upper (D 4) (R 4) [34,68,136,257,10] 13 :=
  permutation_upper _ _ _ [6,40,80,132,258] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 8 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 5 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u514

theorem m743_12 : Upper (D 4) (R 4) [34,68,136,257,12] 13 :=
  permutation_upper _ _ _ [6,36,72,144,258] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u499

def r743 : Route 9 := (fun mask => (mask,id))

def c743 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u743 : Upper (D 4) (R 4) [34,68,136,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257] 13 (by decide) (choices 2) [3,5,6,9,10,12] r743 c743
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m743_3
  · exact m743_5
  · exact m743_6
  · exact m743_9
  · exact m743_10
  · exact m743_12

theorem m744_3 : Upper (D 4) (R 4) [34,68,136,272,3] 13 :=
  permutation_upper _ _ _ [6,36,72,144,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u498

theorem m744_5 : Upper (D 4) (R 4) [34,68,136,272,5] 13 :=
  permutation_upper _ _ _ [6,40,80,129,258] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 7 | 6 => 5 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 8 | 7 => 5 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u509

theorem m744_6 : Upper (D 4) (R 4) [34,68,136,272,6] 13 :=
  permutation_upper _ _ _ [6,36,72,129,258] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u494

theorem m744_9 : Upper (D 4) (R 4) [34,68,136,272,9] 13 :=
  permutation_upper _ _ _ [6,33,72,144,258] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u476

theorem m744_10 : Upper (D 4) (R 4) [34,68,136,272,10] 13 :=
  permutation_upper _ _ _ [6,33,72,130,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u468

theorem m744_12 : Upper (D 4) (R 4) [34,68,136,272,12] 13 :=
  permutation_upper _ _ _ [6,33,66,132,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 8 | 6 => 7 | 7 => 6 | _ => 5) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 8 | 6 => 7 | 7 => 6 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u450

def r744 : Route 9 := (fun mask => (mask,id))

def c744 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u744 : Upper (D 4) (R 4) [34,68,136,272] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272] 13 (by decide) (choices 2) [3,5,6,9,10,12] r744 c744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m744_3
  · exact m744_5
  · exact m744_6
  · exact m744_9
  · exact m744_10
  · exact m744_12

def b745 : PairBound 9 := { available := 506, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 7 13 506 506 506 506 506 506), lower := (rows 7 7 13 8 16 32 64 128 256), losses := [] }

theorem u745 : Upper (D 4) (R 4) [6,5,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b745
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 507, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 28 507 507 507 507 507 507), lower := (rows 7 7 28 8 16 32 64 128 256), losses := [] }

theorem u746 : Upper (D 4) (R 4) [6,5,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b746
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b747 : PairBound 9 := { available := 474, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 37 474 474 506 474 474 474), lower := (rows 7 7 37 8 16 32 64 128 256), losses := [] }

theorem u747 : Upper (D 4) (R 4) [6,5,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b747
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 475, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 475 475 507 475 475 475), lower := (rows 7 7 44 8 16 32 64 128 256), losses := [] }

theorem u748 : Upper (D 4) (R 4) [6,5,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b748
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 411, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 100 411 411 443 475 411 411), lower := (rows 7 7 100 8 16 32 64 128 256), losses := [] }

theorem u749 : Upper (D 4) (R 4) [6,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b749
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 502, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 13 510 502 502 502 502 502), lower := (rows 7 11 13 8 16 32 64 128 256), losses := [] }

theorem u750 : Upper (D 4) (R 4) [6,9,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b750
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b751 : PairBound 9 := { available := 501, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 14 509 501 501 501 501 501), lower := (rows 7 11 14 8 16 32 64 128 256), losses := [] }

theorem u751 : Upper (D 4) (R 4) [6,9,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b751
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 510, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 510 510 510 510 510 510), lower := (rows 7 11 21 8 16 32 64 128 256), losses := [] }

theorem u752 : Upper (D 4) (R 4) [6,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b752
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 509, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 509 509 509 509 509 509), lower := (rows 7 11 22 8 16 32 64 128 256), losses := [] }

theorem u753 : Upper (D 4) (R 4) [6,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b753
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 503, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 511 503 503 503 503 503), lower := (rows 7 11 28 8 16 32 64 128 256), losses := [] }

theorem u754 : Upper (D 4) (R 4) [6,9,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b754
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 478, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 478 478 510 478 478 478), lower := (rows 7 11 37 8 16 32 64 128 256), losses := [] }

theorem u755 : Upper (D 4) (R 4) [6,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b755
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 477, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 477 477 509 477 477 477), lower := (rows 7 11 38 8 16 32 64 128 256), losses := [] }

theorem u756 : Upper (D 4) (R 4) [6,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b756
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 471, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 479 471 503 471 471 471), lower := (rows 7 11 44 8 16 32 64 128 256), losses := [] }

theorem u757 : Upper (D 4) (R 4) [6,9,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b757
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m758_3 : Upper (D 4) (R 4) [6,9,48,3] 13 :=
  permutation_upper _ _ _ [6,5,9,48] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u521

theorem m758_5 : Upper (D 4) (R 4) [6,9,48,5] 13 :=
  permutation_upper _ _ _ [6,9,10,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u535

theorem m758_6 : Upper (D 4) (R 4) [6,9,48,6] 13 :=
  permutation_upper _ _ _ [6,9,9,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u533

theorem m758_17 : Upper (D 4) (R 4) [6,9,48,17] 13 :=
  permutation_upper _ _ _ [6,9,18,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u539

theorem m758_18 : Upper (D 4) (R 4) [6,9,48,18] 13 :=
  permutation_upper _ _ _ [6,9,17,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u537

theorem m758_20 : Upper (D 4) (R 4) [6,9,48,20] 13 :=
  permutation_upper _ _ _ [6,9,24,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u542

theorem m758_65 : Upper (D 4) (R 4) [6,9,48,65] 13 :=
  permutation_upper _ _ _ [6,9,34,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u548

theorem m758_66 : Upper (D 4) (R 4) [6,9,48,66] 13 :=
  permutation_upper _ _ _ [6,9,33,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u545

theorem m758_68 : Upper (D 4) (R 4) [6,9,48,68] 13 :=
  permutation_upper _ _ _ [6,9,40,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u551

def r758 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c758 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u758 : Upper (D 4) (R 4) [6,9,48] 13 := by
  apply FastRouting.sound _ _ [6,9,48] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,192] r758 c758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m758_3
  · exact m758_5
  · exact m758_6
  · exact m758_17
  · exact m758_18
  · exact m758_20
  · exact m758_65
  · exact m758_66
  · exact m758_68
  · exact u553
  · exact u554

theorem m759_3 : Upper (D 4) (R 4) [6,9,96,3] 13 :=
  permutation_upper _ _ _ [6,5,9,96] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u522

theorem m759_5 : Upper (D 4) (R 4) [6,9,96,5] 13 :=
  permutation_upper _ _ _ [6,9,10,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u536

theorem m759_6 : Upper (D 4) (R 4) [6,9,96,6] 13 :=
  permutation_upper _ _ _ [6,9,9,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u534

theorem m759_17 : Upper (D 4) (R 4) [6,9,96,17] 13 :=
  permutation_upper _ _ _ [6,9,18,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u540

theorem m759_18 : Upper (D 4) (R 4) [6,9,96,18] 13 :=
  permutation_upper _ _ _ [6,9,17,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u538

theorem m759_20 : Upper (D 4) (R 4) [6,9,96,20] 13 :=
  permutation_upper _ _ _ [6,9,24,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u543

theorem m759_129 : Upper (D 4) (R 4) [6,9,96,129] 13 :=
  permutation_upper _ _ _ [6,9,34,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u549

theorem m759_130 : Upper (D 4) (R 4) [6,9,96,130] 13 :=
  permutation_upper _ _ _ [6,9,33,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u546

theorem m759_132 : Upper (D 4) (R 4) [6,9,96,132] 13 :=
  permutation_upper _ _ _ [6,9,40,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u552

theorem m759_144 : Upper (D 4) (R 4) [6,9,96,144] 13 :=
  permutation_upper _ _ _ [6,9,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u554

def r759 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c759 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u759 : Upper (D 4) (R 4) [6,9,96] 13 := by
  apply FastRouting.sound _ _ [6,9,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r759 c759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m759_3
  · exact m759_5
  · exact m759_6
  · exact m759_17
  · exact m759_18
  · exact m759_20
  · exact m759_129
  · exact m759_130
  · exact m759_132
  · exact m759_144
  · exact u555

def b760 : PairBound 9 := { available := 499, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 28 507 499 499 499 499 499), lower := (rows 7 14 28 8 16 32 64 128 256), losses := [] }

theorem u760 : Upper (D 4) (R 4) [6,12,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b760
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 475, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 475 475 507 475 475 475), lower := (rows 7 14 37 8 16 32 64 128 256), losses := [] }

theorem u761 : Upper (D 4) (R 4) [6,12,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b761
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 44 475 467 499 467 467 467), lower := (rows 7 14 44 8 16 32 64 128 256), losses := [] }

theorem u762 : Upper (D 4) (R 4) [6,12,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b762
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 475, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 475 475 507 475 475 475), lower := (rows 7 14 52 8 16 32 64 128 256), losses := [] }

theorem u763 : Upper (D 4) (R 4) [6,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b763
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 411 411 443 475 411 411), lower := (rows 7 14 100 8 16 32 64 128 256), losses := [] }

theorem u764 : Upper (D 4) (R 4) [6,12,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b764
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 487, camps := [{ cop := 0, region := 496, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 28 495 503 487 487 487 487), lower := (rows 7 26 28 8 16 32 64 128 256), losses := [] }

theorem u765 : Upper (D 4) (R 4) [6,24,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b765
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m766_3 : Upper (D 4) (R 4) [6,24,33,3] 13 :=
  permutation_upper _ _ _ [6,12,17,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u557

theorem m766_5 : Upper (D 4) (R 4) [6,24,33,5] 13 :=
  permutation_upper _ _ _ [6,12,34,17] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u565

theorem m766_6 : Upper (D 4) (R 4) [6,24,33,6] 13 :=
  permutation_upper _ _ _ [6,17,40,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u586

def r766 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c766 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u766 : Upper (D 4) (R 4) [6,24,33] 13 := by
  apply FastRouting.sound _ _ [6,24,33] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,192] r766 c766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m766_3
  · exact m766_5
  · exact m766_6
  · exact u610
  · exact u611
  · exact u612
  · exact u613
  · exact u614
  · exact u615
  · exact u616
  · exact u617

def b767 : PairBound 9 := { available := 477, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 38 477 477 509 477 477 477), lower := (rows 7 26 38 8 16 32 64 128 256), losses := [] }

theorem u767 : Upper (D 4) (R 4) [6,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b767
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 471, camps := [{ cop := 0, region := 464, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 479 471 503 471 471 471), lower := (rows 7 26 44 8 16 32 64 128 256), losses := [] }

theorem u768 : Upper (D 4) (R 4) [6,24,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b768
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m769_3 : Upper (D 4) (R 4) [6,24,96,3] 13 :=
  permutation_upper _ _ _ [6,12,17,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u558

theorem m769_5 : Upper (D 4) (R 4) [6,24,96,5] 13 :=
  permutation_upper _ _ _ [6,12,96,17] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u572

theorem m769_6 : Upper (D 4) (R 4) [6,24,96,6] 13 :=
  permutation_upper _ _ _ [6,17,96,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u593

def r769 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c769 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u769 : Upper (D 4) (R 4) [6,24,96] 13 := by
  apply FastRouting.sound _ _ [6,24,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r769 c769
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m769_3
  · exact m769_5
  · exact m769_6
  · exact u625
  · exact u626
  · exact u627
  · exact u628
  · exact u629
  · exact u630
  · exact u631
  · exact u632

def b770 : PairBound 9 := { available := 414, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 414 414 446 478 414 414), lower := (rows 7 35 69 8 16 32 64 128 256), losses := [] }

theorem u770 : Upper (D 4) (R 4) [6,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b770
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 413 413 445 477 413 413), lower := (rows 7 35 70 8 16 32 64 128 256), losses := [] }

theorem u771 : Upper (D 4) (R 4) [6,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b771
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m772_3 : Upper (D 4) (R 4) [6,33,72,3] 13 :=
  permutation_upper _ _ _ [6,12,34,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u566

theorem m772_5 : Upper (D 4) (R 4) [6,33,72,5] 13 :=
  permutation_upper _ _ _ [6,12,33,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u562

def r772 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c772 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u772 : Upper (D 4) (R 4) [6,33,72] 13 := by
  apply FastRouting.sound _ _ [6,33,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r772 c772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m772_3
  · exact m772_5
  · exact u638
  · exact u639
  · exact u640
  · exact u641
  · exact u642
  · exact u643
  · exact u644
  · exact u645
  · exact u646

theorem m773_3 : Upper (D 4) (R 4) [6,33,192,3] 13 :=
  permutation_upper _ _ _ [6,12,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u567

theorem m773_5 : Upper (D 4) (R 4) [6,33,192,5] 13 :=
  permutation_upper _ _ _ [6,12,96,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u574

def r773 : Route 9 := (fun mask => (mask,id))

def c773 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u773 : Upper (D 4) (R 4) [6,33,192] 13 := by
  apply FastRouting.sound _ _ [6,33,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r773 c773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m773_3
  · exact m773_5
  · exact u651
  · exact u652
  · exact u653
  · exact u654
  · exact u655
  · exact u656
  · exact u657
  · exact u658

def b774 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 38 70 409 409 441 473 409 409), lower := (rows 7 38 70 8 16 32 64 128 256), losses := [] }

theorem u774 : Upper (D 4) (R 4) [6,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b774
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b775 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 411 411 443 475 411 411), lower := (rows 7 38 76 8 16 32 64 128 256), losses := [] }

theorem u775 : Upper (D 4) (R 4) [6,36,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b775
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 196 283 283 315 347 411 283), lower := (rows 7 38 196 8 16 32 64 128 256), losses := [] }

theorem u776 : Upper (D 4) (R 4) [6,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b776
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 400, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 415 407 439 471 407 407), lower := (rows 7 42 76 8 16 32 64 128 256), losses := [] }

theorem u777 : Upper (D 4) (R 4) [6,40,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b777
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m778_3 : Upper (D 4) (R 4) [6,40,80,3] 13 :=
  permutation_upper _ _ _ [6,12,33,80] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u563

theorem m778_5 : Upper (D 4) (R 4) [6,40,80,5] 13 :=
  permutation_upper _ _ _ [6,12,48,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u570

theorem m778_6 : Upper (D 4) (R 4) [6,40,80,6] 13 :=
  permutation_upper _ _ _ [6,33,80,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u647

def r778 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c778 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u778 : Upper (D 4) (R 4) [6,40,80] 13 := by
  apply FastRouting.sound _ _ [6,40,80] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r778 c778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m778_3
  · exact m778_5
  · exact m778_6
  · exact u674
  · exact u675
  · exact u676
  · exact u677
  · exact u678
  · exact u679
  · exact u680
  · exact u681

theorem m779_3 : Upper (D 4) (R 4) [6,40,192,3] 13 :=
  permutation_upper _ _ _ [6,12,33,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u564

theorem m779_5 : Upper (D 4) (R 4) [6,40,192,5] 13 :=
  permutation_upper _ _ _ [6,12,96,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u573

theorem m779_6 : Upper (D 4) (R 4) [6,40,192,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u651

def r779 : Route 9 := (fun mask => (mask,id))

def c779 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u779 : Upper (D 4) (R 4) [6,40,192] 13 := by
  apply FastRouting.sound _ _ [6,40,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r779 c779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m779_3
  · exact m779_5
  · exact m779_6
  · exact u682
  · exact u683
  · exact u684
  · exact u685
  · exact u686
  · exact u687
  · exact u688

#print axioms u779
end Delivery.IrregularNine14.P04
