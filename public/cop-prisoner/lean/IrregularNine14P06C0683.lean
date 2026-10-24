import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0488
import IrregularNine14P06C0489
import IrregularNine14P06C0490
import IrregularNine14P06C0491
import IrregularNine14P06C0492

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40980 : PairBound 9 := { available := 380, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 133 11 380 380 380 508 380), lower := (rows 7 98 133 11 16 32 64 128 256), losses := [] }

theorem u40980 : Upper (D 6) (R 6) [6,96,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40980
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40981 : PairBound 9 := { available := 378, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 13 378 378 378 506 378), lower := (rows 7 98 133 13 16 32 64 128 256), losses := [] }

theorem u40981 : Upper (D 6) (R 6) [6,96,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40981
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40982 : PairBound 9 := { available := 377, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 133 14 377 377 377 505 377), lower := (rows 7 98 133 14 16 32 64 128 256), losses := [] }

theorem u40982 : Upper (D 6) (R 6) [6,96,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40982
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40983_6 : Upper (D 6) (R 6) [6,96,129,17,6] 13 :=
  permutation_upper _ _ _ [6,96,129,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29299

def r40983 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40983 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40983 : Upper (D 6) (R 6) [6,96,129,17] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,96,258,260,264,288] r40983 c40983
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40983_6
  · exact u29305
  · exact u29306
  · exact u29307
  · exact u29308
  · exact u29309
  · exact u29310
  · exact u29311
  · exact u29312
  · exact u29313
  · exact u29314

theorem m40984_5 : Upper (D 6) (R 6) [6,96,129,18,5] 13 :=
  permutation_upper _ _ _ [6,96,129,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29294

theorem m40984_9 : Upper (D 6) (R 6) [6,96,129,18,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29305

def r40984 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40984 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40984 : Upper (D 6) (R 6) [6,96,129,18] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,96,257,260,264,288] r40984 c40984
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40984_5
  · exact m40984_9
  · exact u29315
  · exact u29316
  · exact u29317
  · exact u29318
  · exact u29319
  · exact u29320
  · exact u29321
  · exact u29322
  · exact u29323

theorem m40985_3 : Upper (D 6) (R 6) [6,96,129,20,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29288

theorem m40985_9 : Upper (D 6) (R 6) [6,96,129,20,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29306

theorem m40985_10 : Upper (D 6) (R 6) [6,96,129,20,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29315

def r40985 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40985 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40985 : Upper (D 6) (R 6) [6,96,129,20] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,257,258,264,288] r40985 c40985
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40985_3
  · exact m40985_9
  · exact m40985_10
  · exact u29324
  · exact u29325
  · exact u29326
  · exact u29327
  · exact u29328
  · exact u29329
  · exact u29330
  · exact u29331

theorem m40986_6 : Upper (D 6) (R 6) [6,96,129,33,6] 13 :=
  permutation_upper _ _ _ [6,96,129,6,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29300

theorem m40986_10 : Upper (D 6) (R 6) [6,96,129,33,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29316

theorem m40986_12 : Upper (D 6) (R 6) [6,96,129,33,12] 13 :=
  permutation_upper _ _ _ [6,96,129,20,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29324

def r40986 : Route 9 := (fun mask => (mask,id))

def c40986 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40986 : Upper (D 6) (R 6) [6,96,129,33] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r40986 c40986
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40986_6
  · exact m40986_10
  · exact m40986_12
  · exact u29332
  · exact u29333
  · exact u29334
  · exact u29335
  · exact u29336
  · exact u29337
  · exact u29338

def b40987 : PairBound 9 := { available := 349, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 133 42 349 381 349 477 349), lower := (rows 7 98 133 42 16 32 64 128 256), losses := [] }

theorem u40987 : Upper (D 6) (R 6) [6,96,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40987
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40988_3 : Upper (D 6) (R 6) [6,96,129,36,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29289

theorem m40988_9 : Upper (D 6) (R 6) [6,96,129,36,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29308

theorem m40988_10 : Upper (D 6) (R 6) [6,96,129,36,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29317

theorem m40988_65 : Upper (D 6) (R 6) [6,96,129,36,65] 13 :=
  permutation_upper _ _ _ [6,96,129,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29333

theorem m40988_66 : Upper (D 6) (R 6) [6,96,129,36,66] 13 :=
  permutation_upper _ _ _ [6,96,129,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29339

def r40988 : Route 9 := (fun mask => (mask,id))

def c40988 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40988 : Upper (D 6) (R 6) [6,96,129,36] 13 := by
  apply FastRouting.sound _ _ [6,96,129,36] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r40988 c40988
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40988_3
  · exact m40988_9
  · exact m40988_10
  · exact m40988_65
  · exact m40988_66
  · exact u29345
  · exact u29346
  · exact u29347
  · exact u29348
  · exact u29349

theorem m40989_3 : Upper (D 6) (R 6) [6,96,129,48,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29290

theorem m40989_5 : Upper (D 6) (R 6) [6,96,129,48,5] 13 :=
  permutation_upper _ _ _ [6,96,129,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29295

theorem m40989_6 : Upper (D 6) (R 6) [6,96,129,48,6] 13 :=
  permutation_upper _ _ _ [6,96,129,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29301

theorem m40989_9 : Upper (D 6) (R 6) [6,96,129,48,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29309

theorem m40989_10 : Upper (D 6) (R 6) [6,96,129,48,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29318

theorem m40989_12 : Upper (D 6) (R 6) [6,96,129,48,12] 13 :=
  permutation_upper _ _ _ [6,96,129,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29326

theorem m40989_65 : Upper (D 6) (R 6) [6,96,129,48,65] 13 :=
  permutation_upper _ _ _ [6,96,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29334

theorem m40989_66 : Upper (D 6) (R 6) [6,96,129,48,66] 13 :=
  permutation_upper _ _ _ [6,96,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29340

theorem m40989_68 : Upper (D 6) (R 6) [6,96,129,48,68] 13 :=
  permutation_upper _ _ _ [6,96,129,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29345

def r40989 : Route 9 := (fun mask => (mask,id))

def c40989 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40989 : Upper (D 6) (R 6) [6,96,129,48] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,257,258,260,264,320] r40989 c40989
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40989_3
  · exact m40989_5
  · exact m40989_6
  · exact m40989_9
  · exact m40989_10
  · exact m40989_12
  · exact m40989_65
  · exact m40989_66
  · exact m40989_68
  · exact u29350
  · exact u29351
  · exact u29352
  · exact u29353
  · exact u29354
  · exact u29355

def b40990 : PairBound 9 := { available := 287, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 98 133 104 287 319 351 415 287), lower := (rows 7 98 133 104 16 32 64 128 256), losses := [] }

theorem u40990 : Upper (D 6) (R 6) [6,96,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40990
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40991_6 : Upper (D 6) (R 6) [6,96,129,257,6] 13 :=
  permutation_upper _ _ _ [6,96,129,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29302

theorem m40991_10 : Upper (D 6) (R 6) [6,96,129,257,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29320

theorem m40991_12 : Upper (D 6) (R 6) [6,96,129,257,12] 13 :=
  permutation_upper _ _ _ [6,96,129,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29328

theorem m40991_34 : Upper (D 6) (R 6) [6,96,129,257,34] 13 :=
  permutation_upper _ _ _ [6,96,129,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29341

theorem m40991_36 : Upper (D 6) (R 6) [6,96,129,257,36] 13 :=
  permutation_upper _ _ _ [6,96,129,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29346

theorem m40991_40 : Upper (D 6) (R 6) [6,96,129,257,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29351

theorem m40991_96 : Upper (D 6) (R 6) [6,96,129,257,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29356

def r40991 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40991 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40991 : Upper (D 6) (R 6) [6,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,257] 13 (by decide) (choices 2) [6,10,12,34,36,40,96] r40991 c40991
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40991_6
  · exact m40991_10
  · exact m40991_12
  · exact m40991_34
  · exact m40991_36
  · exact m40991_40
  · exact m40991_96

theorem m40992_5 : Upper (D 6) (R 6) [6,96,129,258,5] 13 :=
  permutation_upper _ _ _ [6,96,129,5,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29296

theorem m40992_9 : Upper (D 6) (R 6) [6,96,129,258,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29311

theorem m40992_12 : Upper (D 6) (R 6) [6,96,129,258,12] 13 :=
  permutation_upper _ _ _ [6,96,129,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29329

theorem m40992_33 : Upper (D 6) (R 6) [6,96,129,258,33] 13 :=
  permutation_upper _ _ _ [6,96,129,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29335

theorem m40992_36 : Upper (D 6) (R 6) [6,96,129,258,36] 13 :=
  permutation_upper _ _ _ [6,96,129,36,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29347

theorem m40992_40 : Upper (D 6) (R 6) [6,96,129,258,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29352

theorem m40992_96 : Upper (D 6) (R 6) [6,96,129,258,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29357

def r40992 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40992 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40992 : Upper (D 6) (R 6) [6,96,129,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,96] r40992 c40992
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40992_5
  · exact m40992_9
  · exact m40992_12
  · exact m40992_33
  · exact m40992_36
  · exact m40992_40
  · exact m40992_96

theorem m40993_3 : Upper (D 6) (R 6) [6,96,129,260,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29291

theorem m40993_9 : Upper (D 6) (R 6) [6,96,129,260,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29312

theorem m40993_10 : Upper (D 6) (R 6) [6,96,129,260,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29321

theorem m40993_33 : Upper (D 6) (R 6) [6,96,129,260,33] 13 :=
  permutation_upper _ _ _ [6,96,129,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29336

theorem m40993_34 : Upper (D 6) (R 6) [6,96,129,260,34] 13 :=
  permutation_upper _ _ _ [6,96,129,34,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29342

theorem m40993_40 : Upper (D 6) (R 6) [6,96,129,260,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29353

theorem m40993_96 : Upper (D 6) (R 6) [6,96,129,260,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29358

def r40993 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40993 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40993 : Upper (D 6) (R 6) [6,96,129,260] 13 := by
  apply FastRouting.sound _ _ [6,96,129,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,96] r40993 c40993
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40993_3
  · exact m40993_9
  · exact m40993_10
  · exact m40993_33
  · exact m40993_34
  · exact m40993_40
  · exact m40993_96

theorem m40994_3 : Upper (D 6) (R 6) [6,96,129,272,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29292

theorem m40994_5 : Upper (D 6) (R 6) [6,96,129,272,5] 13 :=
  permutation_upper _ _ _ [6,96,129,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29297

theorem m40994_6 : Upper (D 6) (R 6) [6,96,129,272,6] 13 :=
  permutation_upper _ _ _ [6,96,129,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29303

theorem m40994_9 : Upper (D 6) (R 6) [6,96,129,272,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29313

theorem m40994_10 : Upper (D 6) (R 6) [6,96,129,272,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29322

theorem m40994_12 : Upper (D 6) (R 6) [6,96,129,272,12] 13 :=
  permutation_upper _ _ _ [6,96,129,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29330

theorem m40994_33 : Upper (D 6) (R 6) [6,96,129,272,33] 13 :=
  permutation_upper _ _ _ [6,96,129,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29337

theorem m40994_34 : Upper (D 6) (R 6) [6,96,129,272,34] 13 :=
  permutation_upper _ _ _ [6,96,129,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29343

theorem m40994_36 : Upper (D 6) (R 6) [6,96,129,272,36] 13 :=
  permutation_upper _ _ _ [6,96,129,36,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29348

theorem m40994_40 : Upper (D 6) (R 6) [6,96,129,272,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29354

theorem m40994_96 : Upper (D 6) (R 6) [6,96,129,272,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29359

def r40994 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40994 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40994 : Upper (D 6) (R 6) [6,96,129,272] 13 := by
  apply FastRouting.sound _ _ [6,96,129,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,96] r40994 c40994
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40994_3
  · exact m40994_5
  · exact m40994_6
  · exact m40994_9
  · exact m40994_10
  · exact m40994_12
  · exact m40994_33
  · exact m40994_34
  · exact m40994_36
  · exact m40994_40
  · exact m40994_96

theorem m40995_3 : Upper (D 6) (R 6) [6,96,129,288,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29293

theorem m40995_5 : Upper (D 6) (R 6) [6,96,129,288,5] 13 :=
  permutation_upper _ _ _ [6,96,129,5,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29298

theorem m40995_6 : Upper (D 6) (R 6) [6,96,129,288,6] 13 :=
  permutation_upper _ _ _ [6,96,129,6,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29304

theorem m40995_9 : Upper (D 6) (R 6) [6,96,129,288,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29314

theorem m40995_10 : Upper (D 6) (R 6) [6,96,129,288,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29323

theorem m40995_12 : Upper (D 6) (R 6) [6,96,129,288,12] 13 :=
  permutation_upper _ _ _ [6,96,129,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29331

theorem m40995_65 : Upper (D 6) (R 6) [6,96,129,288,65] 13 :=
  permutation_upper _ _ _ [6,96,129,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29338

theorem m40995_66 : Upper (D 6) (R 6) [6,96,129,288,66] 13 :=
  permutation_upper _ _ _ [6,96,129,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29344

theorem m40995_68 : Upper (D 6) (R 6) [6,96,129,288,68] 13 :=
  permutation_upper _ _ _ [6,96,129,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29349

theorem m40995_72 : Upper (D 6) (R 6) [6,96,129,288,72] 13 :=
  permutation_upper _ _ _ [6,96,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29355

def r40995 : Route 9 := (fun mask => (mask,id))

def c40995 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40995 : Upper (D 6) (R 6) [6,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,96,129,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r40995 c40995
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40995_3
  · exact m40995_5
  · exact m40995_6
  · exact m40995_9
  · exact m40995_10
  · exact m40995_12
  · exact m40995_65
  · exact m40995_66
  · exact m40995_68
  · exact m40995_72

def b40996 : PairBound 9 := { available := 373, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 140 11 373 373 373 501 373), lower := (rows 7 98 140 11 16 32 64 128 256), losses := [] }

theorem u40996 : Upper (D 6) (R 6) [6,96,136,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40996
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40997 : PairBound 9 := { available := 371, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 140 13 371 371 371 499 371), lower := (rows 7 98 140 13 16 32 64 128 256), losses := [] }

theorem u40997 : Upper (D 6) (R 6) [6,96,136,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40997
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40998 : PairBound 9 := { available := 369, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 0, region := 8, targets := 32 }], pairs := [(1,2),(3,5),(4,2)], upper := (rows 7 98 140 14 369 369 369 497 369), lower := (rows 7 98 140 14 16 32 64 128 256), losses := [] }

theorem u40998 : Upper (D 6) (R 6) [6,96,136,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40998
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40999 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40999 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40999 : Upper (D 6) (R 6) [6,96,136,17] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r40999 c40999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29360
  · exact u29361
  · exact u29362
  · exact u29363
  · exact u29364
  · exact u29365
  · exact u29366
  · exact u29367
  · exact u29368
  · exact u29369
  · exact u29370

def r41000 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41000 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41000 : Upper (D 6) (R 6) [6,96,136,18] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r41000 c41000
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29371
  · exact u29372
  · exact u29373
  · exact u29374
  · exact u29375
  · exact u29376
  · exact u29377

def r41001 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41001 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41001 : Upper (D 6) (R 6) [6,96,136,20] 13 := by
  apply FastRouting.sound _ _ [6,96,136,20] 13 (by decide) (choices 2) [3,33,34,96,257,258,288] r41001 c41001
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29378
  · exact u29379
  · exact u29380
  · exact u29381
  · exact u29382
  · exact u29383
  · exact u29384

def r41002 : Route 9 := (fun mask => (mask,id))

def c41002 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41002 : Upper (D 6) (R 6) [6,96,136,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41002 c41002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29385
  · exact u29386
  · exact u29387
  · exact u29388
  · exact u29389
  · exact u29390
  · exact u29391
  · exact u29392
  · exact u29393
  · exact u29394

def b41003 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 140 42 341 373 341 469 341), lower := (rows 7 98 140 42 16 32 64 128 256), losses := [] }

theorem u41003 : Upper (D 6) (R 6) [6,96,136,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41003
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41004 : PairBound 9 := { available := 339, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 7 98 140 44 339 371 339 467 339), lower := (rows 7 98 140 44 16 32 64 128 256), losses := [] }

theorem u41004 : Upper (D 6) (R 6) [6,96,136,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41004
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41005 : Route 9 := (fun mask => (mask,id))

def c41005 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41005 : Upper (D 6) (R 6) [6,96,136,48] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41005 c41005
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29395
  · exact u29396
  · exact u29397
  · exact u29398
  · exact u29399
  · exact u29400
  · exact u29401
  · exact u29402
  · exact u29403
  · exact u29404

def b41006 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 98 140 104 279 311 343 407 279), lower := (rows 7 98 140 104 16 32 64 128 256), losses := [] }

theorem u41006 : Upper (D 6) (R 6) [6,96,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41006
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41007 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41007 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41007 : Upper (D 6) (R 6) [6,96,136,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41007 c41007
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29405
  · exact u29406
  · exact u29407
  · exact u29408
  · exact u29409
  · exact u29410
  · exact u29411

def r41008 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41008 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41008 : Upper (D 6) (R 6) [6,96,136,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258] 13 (by decide) (choices 2) [5,33,36,96] r41008 c41008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29412
  · exact u29413
  · exact u29414
  · exact u29415

def r41009 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41009 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41009 : Upper (D 6) (R 6) [6,96,136,260] 13 := by
  apply FastRouting.sound _ _ [6,96,136,260] 13 (by decide) (choices 2) [3,33,34,96] r41009 c41009
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29416
  · exact u29417
  · exact u29418
  · exact u29419

def r41010 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41010 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41010 : Upper (D 6) (R 6) [6,96,136,272] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41010 c41010
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29420
  · exact u29421
  · exact u29422
  · exact u29423
  · exact u29424
  · exact u29425
  · exact u29426

def r41011 : Route 9 := (fun mask => (mask,id))

def c41011 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41011 : Upper (D 6) (R 6) [6,96,136,288] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41011 c41011
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29427
  · exact u29428
  · exact u29429
  · exact u29430
  · exact u29431
  · exact u29432

def b41012 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 164 11 349 381 349 477 349), lower := (rows 7 98 164 11 16 32 64 128 256), losses := [] }

theorem u41012 : Upper (D 6) (R 6) [6,96,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41012
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41013 : PairBound 9 := { available := 347, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 164 13 347 379 347 475 347), lower := (rows 7 98 164 13 16 32 64 128 256), losses := [] }

theorem u41013 : Upper (D 6) (R 6) [6,96,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41013
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41014 : PairBound 9 := { available := 345, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 98 164 14 345 377 345 473 345), lower := (rows 7 98 164 14 16 32 64 128 256), losses := [] }

theorem u41014 : Upper (D 6) (R 6) [6,96,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41014
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41015_3 : Upper (D 6) (R 6) [6,96,160,17,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29433

theorem m41015_5 : Upper (D 6) (R 6) [6,96,160,17,5] 13 :=
  permutation_upper _ _ _ [6,96,160,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29442

theorem m41015_6 : Upper (D 6) (R 6) [6,96,160,17,6] 13 :=
  permutation_upper _ _ _ [6,96,160,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29450

def r41015 : Route 9 := (fun mask => (mask,id))

def c41015 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41015 : Upper (D 6) (R 6) [6,96,160,17] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,257,258,260,264,320] r41015 c41015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41015_3
  · exact m41015_5
  · exact m41015_6
  · exact u29456
  · exact u29457
  · exact u29458
  · exact u29459
  · exact u29460
  · exact u29461
  · exact u29462
  · exact u29463
  · exact u29464
  · exact u29465
  · exact u29466
  · exact u29467

theorem m41016_5 : Upper (D 6) (R 6) [6,96,160,18,5] 13 :=
  permutation_upper _ _ _ [6,96,160,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29443

theorem m41016_9 : Upper (D 6) (R 6) [6,96,160,18,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29457

def r41016 : Route 9 := (fun mask => (mask,id))

def c41016 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41016 : Upper (D 6) (R 6) [6,96,160,18] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r41016 c41016
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41016_5
  · exact m41016_9
  · exact u29468
  · exact u29469
  · exact u29470
  · exact u29471
  · exact u29472
  · exact u29473
  · exact u29474
  · exact u29475

theorem m41017_3 : Upper (D 6) (R 6) [6,96,160,20,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29434

theorem m41017_9 : Upper (D 6) (R 6) [6,96,160,20,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29458

theorem m41017_10 : Upper (D 6) (R 6) [6,96,160,20,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29468

def r41017 : Route 9 := (fun mask => (mask,id))

def c41017 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41017 : Upper (D 6) (R 6) [6,96,160,20] 13 := by
  apply FastRouting.sound _ _ [6,96,160,20] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r41017 c41017
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41017_3
  · exact m41017_9
  · exact m41017_10
  · exact u29476
  · exact u29477
  · exact u29478
  · exact u29479
  · exact u29480
  · exact u29481
  · exact u29482

theorem m41018_3 : Upper (D 6) (R 6) [6,96,160,65,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29435

theorem m41018_5 : Upper (D 6) (R 6) [6,96,160,65,5] 13 :=
  permutation_upper _ _ _ [6,96,160,5,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29444

theorem m41018_6 : Upper (D 6) (R 6) [6,96,160,65,6] 13 :=
  permutation_upper _ _ _ [6,96,160,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29451

theorem m41018_9 : Upper (D 6) (R 6) [6,96,160,65,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29459

theorem m41018_10 : Upper (D 6) (R 6) [6,96,160,65,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29469

theorem m41018_12 : Upper (D 6) (R 6) [6,96,160,65,12] 13 :=
  permutation_upper _ _ _ [6,96,160,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29476

def r41018 : Route 9 := (fun mask => (mask,id))

def c41018 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41018 : Upper (D 6) (R 6) [6,96,160,65] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r41018 c41018
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41018_3
  · exact m41018_5
  · exact m41018_6
  · exact m41018_9
  · exact m41018_10
  · exact m41018_12
  · exact u29483
  · exact u29484
  · exact u29485
  · exact u29486

def b41019 : PairBound 9 := { available := 285, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 7 98 164 74 285 317 349 413 285), lower := (rows 7 98 164 74 16 32 64 128 256), losses := [] }

theorem u41019 : Upper (D 6) (R 6) [6,96,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41019
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41020_3 : Upper (D 6) (R 6) [6,96,160,68,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29436

theorem m41020_9 : Upper (D 6) (R 6) [6,96,160,68,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29461

theorem m41020_10 : Upper (D 6) (R 6) [6,96,160,68,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29470

def r41020 : Route 9 := (fun mask => (mask,id))

def c41020 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41020 : Upper (D 6) (R 6) [6,96,160,68] 13 := by
  apply FastRouting.sound _ _ [6,96,160,68] 13 (by decide) (choices 2) [3,9,10,257,258,264] r41020 c41020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41020_3
  · exact m41020_9
  · exact m41020_10
  · exact u29490
  · exact u29491
  · exact u29492

theorem m41021_3 : Upper (D 6) (R 6) [6,96,160,80,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29437

theorem m41021_5 : Upper (D 6) (R 6) [6,96,160,80,5] 13 :=
  permutation_upper _ _ _ [6,96,160,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29445

theorem m41021_6 : Upper (D 6) (R 6) [6,96,160,80,6] 13 :=
  permutation_upper _ _ _ [6,96,160,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29452

theorem m41021_9 : Upper (D 6) (R 6) [6,96,160,80,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29462

theorem m41021_10 : Upper (D 6) (R 6) [6,96,160,80,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29471

theorem m41021_12 : Upper (D 6) (R 6) [6,96,160,80,12] 13 :=
  permutation_upper _ _ _ [6,96,160,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29478

def r41021 : Route 9 := (fun mask => (mask,id))

def c41021 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41021 : Upper (D 6) (R 6) [6,96,160,80] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r41021 c41021
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41021_3
  · exact m41021_5
  · exact m41021_6
  · exact m41021_9
  · exact m41021_10
  · exact m41021_12
  · exact u29493
  · exact u29494
  · exact u29495
  · exact u29496

theorem m41022_3 : Upper (D 6) (R 6) [6,96,160,257,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29438

theorem m41022_5 : Upper (D 6) (R 6) [6,96,160,257,5] 13 :=
  permutation_upper _ _ _ [6,96,160,5,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29446

theorem m41022_6 : Upper (D 6) (R 6) [6,96,160,257,6] 13 :=
  permutation_upper _ _ _ [6,96,160,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29453

theorem m41022_9 : Upper (D 6) (R 6) [6,96,160,257,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29463

theorem m41022_10 : Upper (D 6) (R 6) [6,96,160,257,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29472

theorem m41022_12 : Upper (D 6) (R 6) [6,96,160,257,12] 13 :=
  permutation_upper _ _ _ [6,96,160,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29479

theorem m41022_65 : Upper (D 6) (R 6) [6,96,160,257,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29483

theorem m41022_66 : Upper (D 6) (R 6) [6,96,160,257,66] 13 :=
  permutation_upper _ _ _ [6,96,160,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29487

theorem m41022_68 : Upper (D 6) (R 6) [6,96,160,257,68] 13 :=
  permutation_upper _ _ _ [6,96,160,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29490

theorem m41022_72 : Upper (D 6) (R 6) [6,96,160,257,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29493

def r41022 : Route 9 := (fun mask => (mask,id))

def c41022 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41022 : Upper (D 6) (R 6) [6,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41022 c41022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41022_3
  · exact m41022_5
  · exact m41022_6
  · exact m41022_9
  · exact m41022_10
  · exact m41022_12
  · exact m41022_65
  · exact m41022_66
  · exact m41022_68
  · exact m41022_72

theorem m41023_5 : Upper (D 6) (R 6) [6,96,160,258,5] 13 :=
  permutation_upper _ _ _ [6,96,160,5,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29447

theorem m41023_9 : Upper (D 6) (R 6) [6,96,160,258,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29464

theorem m41023_12 : Upper (D 6) (R 6) [6,96,160,258,12] 13 :=
  permutation_upper _ _ _ [6,96,160,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29480

theorem m41023_65 : Upper (D 6) (R 6) [6,96,160,258,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29484

theorem m41023_68 : Upper (D 6) (R 6) [6,96,160,258,68] 13 :=
  permutation_upper _ _ _ [6,96,160,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29491

theorem m41023_72 : Upper (D 6) (R 6) [6,96,160,258,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29494

def r41023 : Route 9 := (fun mask => (mask,id))

def c41023 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41023 : Upper (D 6) (R 6) [6,96,160,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,258] 13 (by decide) (choices 2) [5,9,12,65,68,72] r41023 c41023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41023_5
  · exact m41023_9
  · exact m41023_12
  · exact m41023_65
  · exact m41023_68
  · exact m41023_72

theorem m41024_3 : Upper (D 6) (R 6) [6,96,160,260,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29439

theorem m41024_9 : Upper (D 6) (R 6) [6,96,160,260,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29465

theorem m41024_10 : Upper (D 6) (R 6) [6,96,160,260,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29473

theorem m41024_65 : Upper (D 6) (R 6) [6,96,160,260,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29485

theorem m41024_66 : Upper (D 6) (R 6) [6,96,160,260,66] 13 :=
  permutation_upper _ _ _ [6,96,160,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29488

theorem m41024_72 : Upper (D 6) (R 6) [6,96,160,260,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29495

def r41024 : Route 9 := (fun mask => (mask,id))

def c41024 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41024 : Upper (D 6) (R 6) [6,96,160,260] 13 := by
  apply FastRouting.sound _ _ [6,96,160,260] 13 (by decide) (choices 2) [3,9,10,65,66,72] r41024 c41024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41024_3
  · exact m41024_9
  · exact m41024_10
  · exact m41024_65
  · exact m41024_66
  · exact m41024_72

theorem m41025_3 : Upper (D 6) (R 6) [6,96,160,272,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29440

theorem m41025_5 : Upper (D 6) (R 6) [6,96,160,272,5] 13 :=
  permutation_upper _ _ _ [6,96,160,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29448

theorem m41025_6 : Upper (D 6) (R 6) [6,96,160,272,6] 13 :=
  permutation_upper _ _ _ [6,96,160,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29454

theorem m41025_9 : Upper (D 6) (R 6) [6,96,160,272,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29466

theorem m41025_10 : Upper (D 6) (R 6) [6,96,160,272,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29474

theorem m41025_12 : Upper (D 6) (R 6) [6,96,160,272,12] 13 :=
  permutation_upper _ _ _ [6,96,160,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29481

theorem m41025_65 : Upper (D 6) (R 6) [6,96,160,272,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29486

theorem m41025_66 : Upper (D 6) (R 6) [6,96,160,272,66] 13 :=
  permutation_upper _ _ _ [6,96,160,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29489

theorem m41025_68 : Upper (D 6) (R 6) [6,96,160,272,68] 13 :=
  permutation_upper _ _ _ [6,96,160,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29492

theorem m41025_72 : Upper (D 6) (R 6) [6,96,160,272,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29496

def r41025 : Route 9 := (fun mask => (mask,id))

def c41025 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41025 : Upper (D 6) (R 6) [6,96,160,272] 13 := by
  apply FastRouting.sound _ _ [6,96,160,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41025 c41025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41025_3
  · exact m41025_5
  · exact m41025_6
  · exact m41025_9
  · exact m41025_10
  · exact m41025_12
  · exact m41025_65
  · exact m41025_66
  · exact m41025_68
  · exact m41025_72

theorem m41026_3 : Upper (D 6) (R 6) [6,96,160,320,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29441

theorem m41026_5 : Upper (D 6) (R 6) [6,96,160,320,5] 13 :=
  permutation_upper _ _ _ [6,96,160,5,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29449

theorem m41026_6 : Upper (D 6) (R 6) [6,96,160,320,6] 13 :=
  permutation_upper _ _ _ [6,96,160,6,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29455

theorem m41026_9 : Upper (D 6) (R 6) [6,96,160,320,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29467

theorem m41026_10 : Upper (D 6) (R 6) [6,96,160,320,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29475

theorem m41026_12 : Upper (D 6) (R 6) [6,96,160,320,12] 13 :=
  permutation_upper _ _ _ [6,96,160,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29482

def r41026 : Route 9 := (fun mask => (mask,id))

def c41026 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41026 : Upper (D 6) (R 6) [6,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320] 13 (by decide) (choices 2) [3,5,6,9,10,12] r41026 c41026
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41026_3
  · exact m41026_5
  · exact m41026_6
  · exact m41026_9
  · exact m41026_10
  · exact m41026_12

def b41027 : PairBound 9 := { available := 125, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 388 11 125 125 125 253 381), lower := (rows 7 98 388 11 16 32 64 128 256), losses := [] }

theorem u41027 : Upper (D 6) (R 6) [6,96,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41027
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41028 : PairBound 9 := { available := 123, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 388 13 123 123 123 251 379), lower := (rows 7 98 388 13 16 32 64 128 256), losses := [] }

theorem u41028 : Upper (D 6) (R 6) [6,96,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41028
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41029 : PairBound 9 := { available := 121, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 388 14 121 121 121 249 377), lower := (rows 7 98 388 14 16 32 64 128 256), losses := [] }

theorem u41029 : Upper (D 6) (R 6) [6,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41029
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41030_3 : Upper (D 6) (R 6) [6,96,384,17,3] 13 :=
  permutation_upper _ _ _ [6,96,384,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29497

theorem m41030_5 : Upper (D 6) (R 6) [6,96,384,17,5] 13 :=
  permutation_upper _ _ _ [6,96,384,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29502

theorem m41030_6 : Upper (D 6) (R 6) [6,96,384,17,6] 13 :=
  permutation_upper _ _ _ [6,96,384,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29506

def r41030 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41030 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41030 : Upper (D 6) (R 6) [6,96,384,17] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,96] r41030 c41030
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41030_3
  · exact m41030_5
  · exact m41030_6
  · exact u29509
  · exact u29510
  · exact u29511
  · exact u29512
  · exact u29513
  · exact u29514
  · exact u29515
  · exact u29516

theorem m41031_5 : Upper (D 6) (R 6) [6,96,384,18,5] 13 :=
  permutation_upper _ _ _ [6,96,384,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29503

theorem m41031_9 : Upper (D 6) (R 6) [6,96,384,18,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29510

def r41031 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41031 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41031 : Upper (D 6) (R 6) [6,96,384,18] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,96] r41031 c41031
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41031_5
  · exact m41031_9
  · exact u29517
  · exact u29518
  · exact u29519
  · exact u29520
  · exact u29521

theorem m41032_3 : Upper (D 6) (R 6) [6,96,384,20,3] 13 :=
  permutation_upper _ _ _ [6,96,384,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29498

theorem m41032_9 : Upper (D 6) (R 6) [6,96,384,20,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29511

theorem m41032_10 : Upper (D 6) (R 6) [6,96,384,20,10] 13 :=
  permutation_upper _ _ _ [6,96,384,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29517

def r41032 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41032 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41032 : Upper (D 6) (R 6) [6,96,384,20] 13 := by
  apply FastRouting.sound _ _ [6,96,384,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,96] r41032 c41032
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41032_3
  · exact m41032_9
  · exact m41032_10
  · exact u29522
  · exact u29523
  · exact u29524
  · exact u29525

theorem m41033_3 : Upper (D 6) (R 6) [6,96,384,33,3] 13 :=
  permutation_upper _ _ _ [6,96,384,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29499

theorem m41033_5 : Upper (D 6) (R 6) [6,96,384,33,5] 13 :=
  permutation_upper _ _ _ [6,96,384,5,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29504

theorem m41033_6 : Upper (D 6) (R 6) [6,96,384,33,6] 13 :=
  permutation_upper _ _ _ [6,96,384,6,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29507

theorem m41033_9 : Upper (D 6) (R 6) [6,96,384,33,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29512

theorem m41033_10 : Upper (D 6) (R 6) [6,96,384,33,10] 13 :=
  permutation_upper _ _ _ [6,96,384,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29518

theorem m41033_12 : Upper (D 6) (R 6) [6,96,384,33,12] 13 :=
  permutation_upper _ _ _ [6,96,384,20,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29522

def r41033 : Route 9 := (fun mask => (mask,id))

def c41033 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41033 : Upper (D 6) (R 6) [6,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41033 c41033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41033_3
  · exact m41033_5
  · exact m41033_6
  · exact m41033_9
  · exact m41033_10
  · exact m41033_12
  · exact u29526
  · exact u29527
  · exact u29528
  · exact u29529

def b41034 : PairBound 9 := { available := 93, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 388 42 93 125 93 221 349), lower := (rows 7 98 388 42 16 32 64 128 256), losses := [] }

theorem u41034 : Upper (D 6) (R 6) [6,96,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41034
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41035_3 : Upper (D 6) (R 6) [6,96,384,36,3] 13 :=
  permutation_upper _ _ _ [6,96,384,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29500

theorem m41035_9 : Upper (D 6) (R 6) [6,96,384,36,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29514

theorem m41035_10 : Upper (D 6) (R 6) [6,96,384,36,10] 13 :=
  permutation_upper _ _ _ [6,96,384,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29519

theorem m41035_65 : Upper (D 6) (R 6) [6,96,384,36,65] 13 :=
  permutation_upper _ _ _ [6,96,384,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29528

theorem m41035_66 : Upper (D 6) (R 6) [6,96,384,36,66] 13 :=
  permutation_upper _ _ _ [6,96,384,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29530

def r41035 : Route 9 := (fun mask => (mask,id))

def c41035 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41035 : Upper (D 6) (R 6) [6,96,384,36] 13 := by
  apply FastRouting.sound _ _ [6,96,384,36] 13 (by decide) (choices 2) [3,9,10,65,66,72] r41035 c41035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41035_3
  · exact m41035_9
  · exact m41035_10
  · exact m41035_65
  · exact m41035_66
  · exact u29532

theorem m41036_3 : Upper (D 6) (R 6) [6,96,384,48,3] 13 :=
  permutation_upper _ _ _ [6,96,384,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29501

theorem m41036_5 : Upper (D 6) (R 6) [6,96,384,48,5] 13 :=
  permutation_upper _ _ _ [6,96,384,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29505

theorem m41036_6 : Upper (D 6) (R 6) [6,96,384,48,6] 13 :=
  permutation_upper _ _ _ [6,96,384,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29508

theorem m41036_9 : Upper (D 6) (R 6) [6,96,384,48,9] 13 :=
  permutation_upper _ _ _ [6,96,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29515

theorem m41036_10 : Upper (D 6) (R 6) [6,96,384,48,10] 13 :=
  permutation_upper _ _ _ [6,96,384,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29520

theorem m41036_12 : Upper (D 6) (R 6) [6,96,384,48,12] 13 :=
  permutation_upper _ _ _ [6,96,384,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29524

theorem m41036_65 : Upper (D 6) (R 6) [6,96,384,48,65] 13 :=
  permutation_upper _ _ _ [6,96,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29529

theorem m41036_66 : Upper (D 6) (R 6) [6,96,384,48,66] 13 :=
  permutation_upper _ _ _ [6,96,384,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29531

theorem m41036_68 : Upper (D 6) (R 6) [6,96,384,48,68] 13 :=
  permutation_upper _ _ _ [6,96,384,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u29532

def r41036 : Route 9 := (fun mask => (mask,id))

def c41036 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41036 : Upper (D 6) (R 6) [6,96,384,48] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r41036 c41036
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41036_3
  · exact m41036_5
  · exact m41036_6
  · exact m41036_9
  · exact m41036_10
  · exact m41036_12
  · exact m41036_65
  · exact m41036_66
  · exact m41036_68
  · exact u29533

def b41037 : PairBound 9 := { available := 31, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 98 388 104 31 63 95 159 287), lower := (rows 7 98 388 104 16 32 64 128 256), losses := [] }

theorem u41037 : Upper (D 6) (R 6) [6,96,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41037
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41038 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 261 14 120 120 120 248 376), lower := (rows 7 131 261 14 16 32 64 128 256), losses := [] }

theorem u41038 : Upper (D 6) (R 6) [6,129,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b41038
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41039 : Route 9 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41039 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41039 : Upper (D 6) (R 6) [6,129,257,18] 13 := by
  apply FastRouting.sound _ _ [6,129,257,18] 13 (by decide) (choices 2) [12,36,40,96] r41039 c41039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29536
  · exact u29537
  · exact u29538
  · exact u29539

#print axioms u41039
end Delivery.IrregularNine14.P06
