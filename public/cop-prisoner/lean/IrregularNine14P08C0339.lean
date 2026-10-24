import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0187
import IrregularNine14P08C0188
import IrregularNine14P08C0189
import IrregularNine14P08C0190
import IrregularNine14P08C0191

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m20340_9 : Upper (D 8) (R 8) [66,132,33,272,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11269

theorem m20340_33 : Upper (D 8) (R 8) [66,132,33,272,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11279

theorem m20340_40 : Upper (D 8) (R 8) [66,132,33,272,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11292

theorem m20340_65 : Upper (D 8) (R 8) [66,132,33,272,65] 13 :=
  permutation_upper _ _ _ [66,132,33,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11298

theorem m20340_72 : Upper (D 8) (R 8) [66,132,33,272,72] 13 :=
  permutation_upper _ _ _ [66,132,33,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11305

theorem m20340_96 : Upper (D 8) (R 8) [66,132,33,272,96] 13 :=
  permutation_upper _ _ _ [66,132,33,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11312

theorem m20340_129 : Upper (D 8) (R 8) [66,132,33,272,129] 13 :=
  permutation_upper _ _ _ [66,132,33,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11315

theorem m20340_136 : Upper (D 8) (R 8) [66,132,33,272,136] 13 :=
  permutation_upper _ _ _ [66,132,33,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11319

theorem m20340_160 : Upper (D 8) (R 8) [66,132,33,272,160] 13 :=
  permutation_upper _ _ _ [66,132,33,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11323

theorem m20340_192 : Upper (D 8) (R 8) [66,132,33,272,192] 13 :=
  permutation_upper _ _ _ [66,132,33,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11327

def r20340 : Route 9 := (fun mask => (mask,id))

def c20340 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20340 : Upper (D 8) (R 8) [66,132,33,272] 13 := by
  apply FastRouting.sound _ _ [66,132,33,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20340 c20340
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20340_9
  · exact m20340_33
  · exact m20340_40
  · exact m20340_65
  · exact m20340_72
  · exact m20340_96
  · exact m20340_129
  · exact m20340_136
  · exact m20340_160
  · exact m20340_192

theorem m20341_9 : Upper (D 8) (R 8) [66,132,33,288,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11270

theorem m20341_33 : Upper (D 8) (R 8) [66,132,33,288,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11280

theorem m20341_40 : Upper (D 8) (R 8) [66,132,33,288,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11293

theorem m20341_65 : Upper (D 8) (R 8) [66,132,33,288,65] 13 :=
  permutation_upper _ _ _ [66,132,33,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11299

theorem m20341_72 : Upper (D 8) (R 8) [66,132,33,288,72] 13 :=
  permutation_upper _ _ _ [66,132,33,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11306

theorem m20341_96 : Upper (D 8) (R 8) [66,132,33,288,96] 13 :=
  permutation_upper _ _ _ [66,132,33,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11313

theorem m20341_129 : Upper (D 8) (R 8) [66,132,33,288,129] 13 :=
  permutation_upper _ _ _ [66,132,33,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11316

theorem m20341_136 : Upper (D 8) (R 8) [66,132,33,288,136] 13 :=
  permutation_upper _ _ _ [66,132,33,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11320

theorem m20341_160 : Upper (D 8) (R 8) [66,132,33,288,160] 13 :=
  permutation_upper _ _ _ [66,132,33,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11324

theorem m20341_192 : Upper (D 8) (R 8) [66,132,33,288,192] 13 :=
  permutation_upper _ _ _ [66,132,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11328

def r20341 : Route 9 := (fun mask => (mask,id))

def c20341 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20341 : Upper (D 8) (R 8) [66,132,33,288] 13 := by
  apply FastRouting.sound _ _ [66,132,33,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20341 c20341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20341_9
  · exact m20341_33
  · exact m20341_40
  · exact m20341_65
  · exact m20341_72
  · exact m20341_96
  · exact m20341_129
  · exact m20341_136
  · exact m20341_160
  · exact m20341_192

theorem m20342_9 : Upper (D 8) (R 8) [66,132,33,320,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11271

theorem m20342_33 : Upper (D 8) (R 8) [66,132,33,320,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11281

theorem m20342_40 : Upper (D 8) (R 8) [66,132,33,320,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11294

theorem m20342_129 : Upper (D 8) (R 8) [66,132,33,320,129] 13 :=
  permutation_upper _ _ _ [66,132,33,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11317

theorem m20342_136 : Upper (D 8) (R 8) [66,132,33,320,136] 13 :=
  permutation_upper _ _ _ [66,132,33,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11321

theorem m20342_160 : Upper (D 8) (R 8) [66,132,33,320,160] 13 :=
  permutation_upper _ _ _ [66,132,33,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11325

def r20342 : Route 9 := (fun mask => (mask,id))

def c20342 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20342 : Upper (D 8) (R 8) [66,132,33,320] 13 := by
  apply FastRouting.sound _ _ [66,132,33,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20342 c20342
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20342_9
  · exact m20342_33
  · exact m20342_40
  · exact m20342_129
  · exact m20342_136
  · exact m20342_160

theorem m20343_9 : Upper (D 8) (R 8) [66,132,33,384,9] 13 :=
  permutation_upper _ _ _ [66,132,33,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11272

theorem m20343_33 : Upper (D 8) (R 8) [66,132,33,384,33] 13 :=
  permutation_upper _ _ _ [66,132,33,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11282

theorem m20343_40 : Upper (D 8) (R 8) [66,132,33,384,40] 13 :=
  permutation_upper _ _ _ [66,132,33,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11295

theorem m20343_65 : Upper (D 8) (R 8) [66,132,33,384,65] 13 :=
  permutation_upper _ _ _ [66,132,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11300

theorem m20343_72 : Upper (D 8) (R 8) [66,132,33,384,72] 13 :=
  permutation_upper _ _ _ [66,132,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11307

theorem m20343_96 : Upper (D 8) (R 8) [66,132,33,384,96] 13 :=
  permutation_upper _ _ _ [66,132,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11314

def r20343 : Route 9 := (fun mask => (mask,id))

def c20343 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20343 : Upper (D 8) (R 8) [66,132,33,384] 13 := by
  apply FastRouting.sound _ _ [66,132,33,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20343 c20343
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20343_9
  · exact m20343_33
  · exact m20343_40
  · exact m20343_65
  · exact m20343_72
  · exact m20343_96

def r20344 : Route 9 := (fun mask => (mask,id))

def c20344 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20344 : Upper (D 8) (R 8) [66,132,40,17] 13 := by
  apply FastRouting.sound _ _ [66,132,40,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20344 c20344
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11329
  · exact u11330
  · exact u11331
  · exact u11332
  · exact u11333
  · exact u11334
  · exact u11335
  · exact u11336
  · exact u11337
  · exact u11338

def b20345 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 134 44 41 497 497 497 497 497), lower := (rows 67 134 44 41 16 32 64 128 256), losses := [] }

theorem u20345 : Upper (D 8) (R 8) [66,132,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20346 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 134 44 56 497 481 481 481 481), lower := (rows 67 134 44 56 16 32 64 128 256), losses := [] }

theorem u20346 : Upper (D 8) (R 8) [66,132,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20347 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 44 73 433 433 497 433 433), lower := (rows 67 134 44 73 16 32 64 128 256), losses := [] }

theorem u20347 : Upper (D 8) (R 8) [66,132,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20348 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 44 88 433 417 481 417 417), lower := (rows 67 134 44 88 16 32 64 128 256), losses := [] }

theorem u20348 : Upper (D 8) (R 8) [66,132,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20349 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 134 44 104 433 433 497 433 433), lower := (rows 67 134 44 104 16 32 64 128 256), losses := [] }

theorem u20349 : Upper (D 8) (R 8) [66,132,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20350 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 44 137 369 369 369 497 369), lower := (rows 67 134 44 137 16 32 64 128 256), losses := [] }

theorem u20350 : Upper (D 8) (R 8) [66,132,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20351 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 44 152 369 353 353 481 353), lower := (rows 67 134 44 152 16 32 64 128 256), losses := [] }

theorem u20351 : Upper (D 8) (R 8) [66,132,40,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20352 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 44 168 369 369 369 497 369), lower := (rows 67 134 44 168 16 32 64 128 256), losses := [] }

theorem u20352 : Upper (D 8) (R 8) [66,132,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20353 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 44 200 305 305 369 433 305), lower := (rows 67 134 44 200 16 32 64 128 256), losses := [] }

theorem u20353 : Upper (D 8) (R 8) [66,132,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20354 : Route 9 := (fun mask => (mask,id))

def c20354 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20354 : Upper (D 8) (R 8) [66,132,40,257] 13 := by
  apply FastRouting.sound _ _ [66,132,40,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20354 c20354
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11339
  · exact u11340
  · exact u11341
  · exact u11342
  · exact u11343
  · exact u11344

def r20355 : Route 9 := (fun mask => (mask,id))

def c20355 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20355 : Upper (D 8) (R 8) [66,132,40,272] 13 := by
  apply FastRouting.sound _ _ [66,132,40,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20355 c20355
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11345
  · exact u11346
  · exact u11347
  · exact u11348
  · exact u11349
  · exact u11350

def b20356 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 134 44 296 241 241 241 241 497), lower := (rows 67 134 44 296 16 32 64 128 256), losses := [] }

theorem u20356 : Upper (D 8) (R 8) [66,132,40,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20357 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 44 328 177 177 241 177 433), lower := (rows 67 134 44 328 16 32 64 128 256), losses := [] }

theorem u20357 : Upper (D 8) (R 8) [66,132,40,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20358 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 44 392 113 113 113 241 369), lower := (rows 67 134 44 392 16 32 64 128 256), losses := [] }

theorem u20358 : Upper (D 8) (R 8) [66,132,40,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20359 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 261 25 248 232 232 232 488), lower := (rows 67 134 261 25 16 32 64 128 256), losses := [] }

theorem u20359 : Upper (D 8) (R 8) [66,132,257,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20360 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 261 41 248 248 248 248 504), lower := (rows 67 134 261 41 16 32 64 128 256), losses := [] }

theorem u20360 : Upper (D 8) (R 8) [66,132,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20361_9 : Upper (D 8) (R 8) [66,132,257,48,9] 13 :=
  permutation_upper _ _ _ [66,132,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11351

theorem m20361_33 : Upper (D 8) (R 8) [66,132,257,48,33] 13 :=
  permutation_upper _ _ _ [66,132,257,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11357

def r20361 : Route 9 := (fun mask => (mask,id))

def c20361 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20361 : Upper (D 8) (R 8) [66,132,257,48] 13 := by
  apply FastRouting.sound _ _ [66,132,257,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20361 c20361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20361_9
  · exact m20361_33
  · exact u11363
  · exact u11364
  · exact u11365
  · exact u11366
  · exact u11367
  · exact u11368
  · exact u11369
  · exact u11370

def b20362 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 261 73 184 184 248 184 440), lower := (rows 67 134 261 73 16 32 64 128 256), losses := [] }

theorem u20362 : Upper (D 8) (R 8) [66,132,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20363_9 : Upper (D 8) (R 8) [66,132,257,80,9] 13 :=
  permutation_upper _ _ _ [66,132,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11352

theorem m20363_33 : Upper (D 8) (R 8) [66,132,257,80,33] 13 :=
  permutation_upper _ _ _ [66,132,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11358

theorem m20363_40 : Upper (D 8) (R 8) [66,132,257,80,40] 13 :=
  permutation_upper _ _ _ [66,132,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11365

def r20363 : Route 9 := (fun mask => (mask,id))

def c20363 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20363 : Upper (D 8) (R 8) [66,132,257,80] 13 := by
  apply FastRouting.sound _ _ [66,132,257,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20363 c20363
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20363_9
  · exact m20363_33
  · exact m20363_40
  · exact u11373
  · exact u11374
  · exact u11375

theorem m20364_9 : Upper (D 8) (R 8) [66,132,257,96,9] 13 :=
  permutation_upper _ _ _ [66,132,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11353

theorem m20364_33 : Upper (D 8) (R 8) [66,132,257,96,33] 13 :=
  permutation_upper _ _ _ [66,132,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11359

theorem m20364_40 : Upper (D 8) (R 8) [66,132,257,96,40] 13 :=
  permutation_upper _ _ _ [66,132,257,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11366

def r20364 : Route 9 := (fun mask => (mask,id))

def c20364 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20364 : Upper (D 8) (R 8) [66,132,257,96] 13 := by
  apply FastRouting.sound _ _ [66,132,257,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20364 c20364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20364_9
  · exact m20364_33
  · exact m20364_40
  · exact u11376
  · exact u11377
  · exact u11378

def b20365 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 261 137 120 120 120 248 376), lower := (rows 67 134 261 137 16 32 64 128 256), losses := [] }

theorem u20365 : Upper (D 8) (R 8) [66,132,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20366_9 : Upper (D 8) (R 8) [66,132,257,144,9] 13 :=
  permutation_upper _ _ _ [66,132,257,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11354

theorem m20366_33 : Upper (D 8) (R 8) [66,132,257,144,33] 13 :=
  permutation_upper _ _ _ [66,132,257,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11360

theorem m20366_40 : Upper (D 8) (R 8) [66,132,257,144,40] 13 :=
  permutation_upper _ _ _ [66,132,257,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11368

theorem m20366_65 : Upper (D 8) (R 8) [66,132,257,144,65] 13 :=
  permutation_upper _ _ _ [66,132,257,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11371

theorem m20366_72 : Upper (D 8) (R 8) [66,132,257,144,72] 13 :=
  permutation_upper _ _ _ [66,132,257,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11374

theorem m20366_96 : Upper (D 8) (R 8) [66,132,257,144,96] 13 :=
  permutation_upper _ _ _ [66,132,257,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11377

def r20366 : Route 9 := (fun mask => (mask,id))

def c20366 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20366 : Upper (D 8) (R 8) [66,132,257,144] 13 := by
  apply FastRouting.sound _ _ [66,132,257,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20366 c20366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20366_9
  · exact m20366_33
  · exact m20366_40
  · exact m20366_65
  · exact m20366_72
  · exact m20366_96

theorem m20367_9 : Upper (D 8) (R 8) [66,132,257,160,9] 13 :=
  permutation_upper _ _ _ [66,132,257,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11355

theorem m20367_33 : Upper (D 8) (R 8) [66,132,257,160,33] 13 :=
  permutation_upper _ _ _ [66,132,257,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11361

theorem m20367_40 : Upper (D 8) (R 8) [66,132,257,160,40] 13 :=
  permutation_upper _ _ _ [66,132,257,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11369

theorem m20367_65 : Upper (D 8) (R 8) [66,132,257,160,65] 13 :=
  permutation_upper _ _ _ [66,132,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11372

theorem m20367_72 : Upper (D 8) (R 8) [66,132,257,160,72] 13 :=
  permutation_upper _ _ _ [66,132,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11375

theorem m20367_96 : Upper (D 8) (R 8) [66,132,257,160,96] 13 :=
  permutation_upper _ _ _ [66,132,257,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11378

def r20367 : Route 9 := (fun mask => (mask,id))

def c20367 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20367 : Upper (D 8) (R 8) [66,132,257,160] 13 := by
  apply FastRouting.sound _ _ [66,132,257,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20367 c20367
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20367_9
  · exact m20367_33
  · exact m20367_40
  · exact m20367_65
  · exact m20367_72
  · exact m20367_96

theorem m20368_9 : Upper (D 8) (R 8) [66,132,257,192,9] 13 :=
  permutation_upper _ _ _ [66,132,257,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11356

theorem m20368_33 : Upper (D 8) (R 8) [66,132,257,192,33] 13 :=
  permutation_upper _ _ _ [66,132,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11362

theorem m20368_40 : Upper (D 8) (R 8) [66,132,257,192,40] 13 :=
  permutation_upper _ _ _ [66,132,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11370

def r20368 : Route 9 := (fun mask => (mask,id))

def c20368 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20368 : Upper (D 8) (R 8) [66,132,257,192] 13 := by
  apply FastRouting.sound _ _ [66,132,257,192] 13 (by decide) (choices 2) [9,33,40] r20368 c20368
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m20368_9
  · exact m20368_33
  · exact m20368_40

def r20369 : Route 9 := (fun mask => (mask,id))

def c20369 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20369 : Upper (D 8) (R 8) [66,132,264,17] 13 := by
  apply FastRouting.sound _ _ [66,132,264,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20369 c20369
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11379
  · exact u11380
  · exact u11381
  · exact u11382
  · exact u11383
  · exact u11384

def r20370 : Route 9 := (fun mask => (mask,id))

def c20370 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20370 : Upper (D 8) (R 8) [66,132,264,33] 13 := by
  apply FastRouting.sound _ _ [66,132,264,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20370 c20370
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11385
  · exact u11386
  · exact u11387
  · exact u11388
  · exact u11389
  · exact u11390

def r20371 : Route 9 := (fun mask => (mask,id))

def c20371 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20371 : Upper (D 8) (R 8) [66,132,264,48] 13 := by
  apply FastRouting.sound _ _ [66,132,264,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20371 c20371
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11391
  · exact u11392
  · exact u11393
  · exact u11394
  · exact u11395
  · exact u11396

def b20372 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 73 177 177 241 177 433), lower := (rows 67 134 268 73 16 32 64 128 256), losses := [] }

theorem u20372 : Upper (D 8) (R 8) [66,132,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20373 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 268 88 177 161 225 161 417), lower := (rows 67 134 268 88 16 32 64 128 256), losses := [] }

theorem u20373 : Upper (D 8) (R 8) [66,132,264,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20374 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 268 104 177 177 241 177 433), lower := (rows 67 134 268 104 16 32 64 128 256), losses := [] }

theorem u20374 : Upper (D 8) (R 8) [66,132,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20375 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 268 137 113 113 113 241 369), lower := (rows 67 134 268 137 16 32 64 128 256), losses := [] }

theorem u20375 : Upper (D 8) (R 8) [66,132,264,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20376 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 268 152 113 97 97 225 353), lower := (rows 67 134 268 152 16 32 64 128 256), losses := [] }

theorem u20376 : Upper (D 8) (R 8) [66,132,264,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20377 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 268 168 113 113 113 241 369), lower := (rows 67 134 268 168 16 32 64 128 256), losses := [] }

theorem u20377 : Upper (D 8) (R 8) [66,132,264,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20378 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 268 200 49 49 113 177 305), lower := (rows 67 134 268 200 16 32 64 128 256), losses := [] }

theorem u20378 : Upper (D 8) (R 8) [66,132,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20379 : Route 9 := (fun mask => (mask,id))

def c20379 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20379 : Upper (D 8) (R 8) [66,132,288,17] 13 := by
  apply FastRouting.sound _ _ [66,132,288,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20379 c20379
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11397
  · exact u11398
  · exact u11399
  · exact u11400
  · exact u11401
  · exact u11402
  · exact u11403
  · exact u11404
  · exact u11405
  · exact u11406

theorem m20380_9 : Upper (D 8) (R 8) [66,132,288,33,9] 13 :=
  permutation_upper _ _ _ [66,132,288,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11398

def r20380 : Route 9 := (fun mask => (mask,id))

def c20380 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20380 : Upper (D 8) (R 8) [66,132,288,33] 13 := by
  apply FastRouting.sound _ _ [66,132,288,33] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20380 c20380
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20380_9
  · exact u11407
  · exact u11408
  · exact u11409
  · exact u11410
  · exact u11411
  · exact u11412
  · exact u11413
  · exact u11414
  · exact u11415

theorem m20381_9 : Upper (D 8) (R 8) [66,132,288,48,9] 13 :=
  permutation_upper _ _ _ [66,132,288,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11399

theorem m20381_33 : Upper (D 8) (R 8) [66,132,288,48,33] 13 :=
  permutation_upper _ _ _ [66,132,288,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11408

def r20381 : Route 9 := (fun mask => (mask,id))

def c20381 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20381 : Upper (D 8) (R 8) [66,132,288,48] 13 := by
  apply FastRouting.sound _ _ [66,132,288,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20381 c20381
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20381_9
  · exact m20381_33
  · exact u11416
  · exact u11417
  · exact u11418
  · exact u11419
  · exact u11420
  · exact u11421
  · exact u11422
  · exact u11423

def b20382 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 73 185 185 249 185 441), lower := (rows 67 134 292 73 16 32 64 128 256), losses := [] }

theorem u20382 : Upper (D 8) (R 8) [66,132,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20383_9 : Upper (D 8) (R 8) [66,132,288,80,9] 13 :=
  permutation_upper _ _ _ [66,132,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11401

theorem m20383_33 : Upper (D 8) (R 8) [66,132,288,80,33] 13 :=
  permutation_upper _ _ _ [66,132,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11410

theorem m20383_40 : Upper (D 8) (R 8) [66,132,288,80,40] 13 :=
  permutation_upper _ _ _ [66,132,288,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11418

def r20383 : Route 9 := (fun mask => (mask,id))

def c20383 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20383 : Upper (D 8) (R 8) [66,132,288,80] 13 := by
  apply FastRouting.sound _ _ [66,132,288,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20383 c20383
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20383_9
  · exact m20383_33
  · exact m20383_40
  · exact u11426
  · exact u11427
  · exact u11428

theorem m20384_9 : Upper (D 8) (R 8) [66,132,288,96,9] 13 :=
  permutation_upper _ _ _ [66,132,288,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11402

theorem m20384_33 : Upper (D 8) (R 8) [66,132,288,96,33] 13 :=
  permutation_upper _ _ _ [66,132,288,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11411

theorem m20384_40 : Upper (D 8) (R 8) [66,132,288,96,40] 13 :=
  permutation_upper _ _ _ [66,132,288,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11419

def r20384 : Route 9 := (fun mask => (mask,id))

def c20384 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20384 : Upper (D 8) (R 8) [66,132,288,96] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20384 c20384
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20384_9
  · exact m20384_33
  · exact m20384_40
  · exact u11429
  · exact u11430
  · exact u11431

def b20385 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 137 121 121 121 249 377), lower := (rows 67 134 292 137 16 32 64 128 256), losses := [] }

theorem u20385 : Upper (D 8) (R 8) [66,132,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20386_9 : Upper (D 8) (R 8) [66,132,288,144,9] 13 :=
  permutation_upper _ _ _ [66,132,288,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11404

theorem m20386_33 : Upper (D 8) (R 8) [66,132,288,144,33] 13 :=
  permutation_upper _ _ _ [66,132,288,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11413

theorem m20386_40 : Upper (D 8) (R 8) [66,132,288,144,40] 13 :=
  permutation_upper _ _ _ [66,132,288,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11421

theorem m20386_65 : Upper (D 8) (R 8) [66,132,288,144,65] 13 :=
  permutation_upper _ _ _ [66,132,288,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11424

theorem m20386_72 : Upper (D 8) (R 8) [66,132,288,144,72] 13 :=
  permutation_upper _ _ _ [66,132,288,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11427

theorem m20386_96 : Upper (D 8) (R 8) [66,132,288,144,96] 13 :=
  permutation_upper _ _ _ [66,132,288,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11430

def r20386 : Route 9 := (fun mask => (mask,id))

def c20386 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20386 : Upper (D 8) (R 8) [66,132,288,144] 13 := by
  apply FastRouting.sound _ _ [66,132,288,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20386 c20386
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20386_9
  · exact m20386_33
  · exact m20386_40
  · exact m20386_65
  · exact m20386_72
  · exact m20386_96

theorem m20387_9 : Upper (D 8) (R 8) [66,132,288,160,9] 13 :=
  permutation_upper _ _ _ [66,132,288,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11405

theorem m20387_33 : Upper (D 8) (R 8) [66,132,288,160,33] 13 :=
  permutation_upper _ _ _ [66,132,288,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11414

theorem m20387_40 : Upper (D 8) (R 8) [66,132,288,160,40] 13 :=
  permutation_upper _ _ _ [66,132,288,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11422

theorem m20387_65 : Upper (D 8) (R 8) [66,132,288,160,65] 13 :=
  permutation_upper _ _ _ [66,132,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11425

theorem m20387_72 : Upper (D 8) (R 8) [66,132,288,160,72] 13 :=
  permutation_upper _ _ _ [66,132,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11428

theorem m20387_96 : Upper (D 8) (R 8) [66,132,288,160,96] 13 :=
  permutation_upper _ _ _ [66,132,288,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11431

def r20387 : Route 9 := (fun mask => (mask,id))

def c20387 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20387 : Upper (D 8) (R 8) [66,132,288,160] 13 := by
  apply FastRouting.sound _ _ [66,132,288,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20387 c20387
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20387_9
  · exact m20387_33
  · exact m20387_40
  · exact m20387_65
  · exact m20387_72
  · exact m20387_96

theorem m20388_9 : Upper (D 8) (R 8) [66,132,288,192,9] 13 :=
  permutation_upper _ _ _ [66,132,288,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11406

theorem m20388_33 : Upper (D 8) (R 8) [66,132,288,192,33] 13 :=
  permutation_upper _ _ _ [66,132,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11415

theorem m20388_40 : Upper (D 8) (R 8) [66,132,288,192,40] 13 :=
  permutation_upper _ _ _ [66,132,288,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11423

def r20388 : Route 9 := (fun mask => (mask,id))

def c20388 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20388 : Upper (D 8) (R 8) [66,132,288,192] 13 := by
  apply FastRouting.sound _ _ [66,132,288,192] 13 (by decide) (choices 2) [9,33,40] r20388 c20388
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m20388_9
  · exact m20388_33
  · exact m20388_40

def b20389 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 13 496 496 496 496 496), lower := (rows 67 162 13 13 16 32 64 128 256), losses := [] }

theorem u20389 : Upper (D 8) (R 8) [66,160,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20390 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 25 500 484 484 484 484), lower := (rows 67 162 13 25 16 32 64 128 256), losses := [] }

theorem u20390 : Upper (D 8) (R 8) [66,160,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20391 : Route 9 := (fun mask => (mask,id))

def c20391 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20391 : Upper (D 8) (R 8) [66,160,9,20] 13 := by
  apply FastRouting.sound _ _ [66,160,9,20] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20391 c20391
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11446
  · exact u11447
  · exact u11448
  · exact u11449
  · exact u11450
  · exact u11451
  · exact u11452
  · exact u11453
  · exact u11454
  · exact u11455

def b20392 : PairBound 9 := { available := 500, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 500 500 500 500 500), lower := (rows 67 162 13 41 16 32 64 128 256), losses := [] }

theorem u20392 : Upper (D 8) (R 8) [66,160,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20393 : Route 9 := (fun mask => (mask,id))

def c20393 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20393 : Upper (D 8) (R 8) [66,160,9,36] 13 := by
  apply FastRouting.sound _ _ [66,160,9,36] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20393 c20393
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u11465
  · exact u11466
  · exact u11467
  · exact u11468
  · exact u11469
  · exact u11470
  · exact u11471
  · exact u11472
  · exact u11473
  · exact u11474

theorem m20394_5 : Upper (D 8) (R 8) [66,160,9,48,5] 13 :=
  permutation_upper _ _ _ [66,160,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11437

def r20394 : Route 9 := (fun mask => (mask,id))

def c20394 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20394 : Upper (D 8) (R 8) [66,160,9,48] 13 := by
  apply FastRouting.sound _ _ [66,160,9,48] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r20394 c20394
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20394_5
  · exact u11475
  · exact u11476
  · exact u11477
  · exact u11478
  · exact u11479
  · exact u11480
  · exact u11481
  · exact u11482
  · exact u11483
  · exact u11484
  · exact u11485
  · exact u11486
  · exact u11487
  · exact u11488

def b20395 : PairBound 9 := { available := 436, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 73 436 436 500 436 436), lower := (rows 67 162 13 73 16 32 64 128 256), losses := [] }

theorem u20395 : Upper (D 8) (R 8) [66,160,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20396 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 76 433 433 497 433 433), lower := (rows 67 162 13 76 16 32 64 128 256), losses := [] }

theorem u20396 : Upper (D 8) (R 8) [66,160,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20397 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 88 437 421 485 421 421), lower := (rows 67 162 13 88 16 32 64 128 256), losses := [] }

theorem u20397 : Upper (D 8) (R 8) [66,160,9,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20398 : PairBound 9 := { available := 437, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 104 437 437 501 437 437), lower := (rows 67 162 13 104 16 32 64 128 256), losses := [] }

theorem u20398 : Upper (D 8) (R 8) [66,160,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20399 : PairBound 9 := { available := 372, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 137 372 372 372 500 372), lower := (rows 67 162 13 137 16 32 64 128 256), losses := [] }

theorem u20399 : Upper (D 8) (R 8) [66,160,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u20399
end Delivery.IrregularNine14.P08
