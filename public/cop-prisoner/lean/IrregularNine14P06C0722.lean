import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0654
import IrregularNine14P06C0655
import IrregularNine14P06C0656
import IrregularNine14P06C0657
import IrregularNine14P06C0658
import IrregularNine14P06C0659

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43320_3 : Upper (D 6) (R 6) [40,80,96,129,3] 13 :=
  permutation_upper _ _ _ [40,80,96,3,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39271

theorem m43320_5 : Upper (D 6) (R 6) [40,80,96,129,5] 13 :=
  permutation_upper _ _ _ [40,80,96,6,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39281

theorem m43320_6 : Upper (D 6) (R 6) [40,80,96,129,6] 13 :=
  permutation_upper _ _ _ [40,80,96,5,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39276

def r43320 : Route 9 := (fun mask => (mask,id))

def c43320 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43320 : Upper (D 6) (R 6) [40,80,96,129] 13 := by
  apply FastRouting.sound _ _ [40,80,96,129] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43320 c43320
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43320_3
  · exact m43320_5
  · exact m43320_6
  · exact u39284
  · exact u39285
  · exact u39286

theorem m43321_3 : Upper (D 6) (R 6) [40,80,96,130,3] 13 :=
  permutation_upper _ _ _ [40,80,96,3,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39270

theorem m43321_5 : Upper (D 6) (R 6) [40,80,96,130,5] 13 :=
  permutation_upper _ _ _ [40,80,96,6,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39280

theorem m43321_6 : Upper (D 6) (R 6) [40,80,96,130,6] 13 :=
  permutation_upper _ _ _ [40,80,96,5,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39275

theorem m43321_258 : Upper (D 6) (R 6) [40,80,96,130,258] 13 :=
  permutation_upper _ _ _ [40,80,96,129,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39284

def r43321 : Route 9 := (fun mask => (mask,id))

def c43321 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43321 : Upper (D 6) (R 6) [40,80,96,130] 13 := by
  apply FastRouting.sound _ _ [40,80,96,130] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43321 c43321
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43321_3
  · exact m43321_5
  · exact m43321_6
  · exact u39287
  · exact m43321_258
  · exact u39288

theorem m43322_3 : Upper (D 6) (R 6) [40,80,96,132,3] 13 :=
  permutation_upper _ _ _ [40,80,96,3,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39272

theorem m43322_5 : Upper (D 6) (R 6) [40,80,96,132,5] 13 :=
  permutation_upper _ _ _ [40,80,96,6,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39282

theorem m43322_6 : Upper (D 6) (R 6) [40,80,96,132,6] 13 :=
  permutation_upper _ _ _ [40,80,96,5,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39277

theorem m43322_257 : Upper (D 6) (R 6) [40,80,96,132,257] 13 :=
  permutation_upper _ _ _ [40,80,96,130,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39288

theorem m43322_258 : Upper (D 6) (R 6) [40,80,96,132,258] 13 :=
  permutation_upper _ _ _ [40,80,96,129,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39286

def r43322 : Route 9 := (fun mask => (mask,id))

def c43322 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43322 : Upper (D 6) (R 6) [40,80,96,132] 13 := by
  apply FastRouting.sound _ _ [40,80,96,132] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43322 c43322
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43322_3
  · exact m43322_5
  · exact m43322_6
  · exact m43322_257
  · exact m43322_258
  · exact u39289

theorem m43323_3 : Upper (D 6) (R 6) [40,80,96,384,3] 13 :=
  permutation_upper _ _ _ [40,80,96,3,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39273

theorem m43323_5 : Upper (D 6) (R 6) [40,80,96,384,5] 13 :=
  permutation_upper _ _ _ [40,80,96,6,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39283

theorem m43323_6 : Upper (D 6) (R 6) [40,80,96,384,6] 13 :=
  permutation_upper _ _ _ [40,80,96,5,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39278

def r43323 : Route 9 := (fun mask => (mask,id))

def c43323 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43323 : Upper (D 6) (R 6) [40,80,96,384] 13 := by
  apply FastRouting.sound _ _ [40,80,96,384] 13 (by decide) (choices 2) [3,5,6] r43323 c43323
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43323_3
  · exact m43323_5
  · exact m43323_6

def r43324 : Route 9 := (fun mask => (mask,id))

def c43324 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43324 : Upper (D 6) (R 6) [40,80,129,3] 13 := by
  apply FastRouting.sound _ _ [40,80,129,3] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r43324 c43324
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39290
  · exact u39291
  · exact u39292
  · exact u39293
  · exact u39294
  · exact u39295
  · exact u39296
  · exact u39297
  · exact u39298
  · exact u39299

def b43325 : PairBound 9 := { available := 358, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 41 82 133 13 374 358 358 486 358), lower := (rows 41 82 133 13 16 32 64 128 256), losses := [] }

theorem u43325 : Upper (D 6) (R 6) [40,80,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43326 : Route 9 := (fun mask => (mask,id))

def c43326 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43326 : Upper (D 6) (R 6) [40,80,129,6] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43326 c43326
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39300
  · exact u39301
  · exact u39302
  · exact u39303
  · exact u39304
  · exact u39305
  · exact u39306
  · exact u39307
  · exact u39308
  · exact u39309
  · exact u39310
  · exact u39311
  · exact u39312
  · exact u39313
  · exact u39314

def b43327 : PairBound 9 := { available := 326, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 41 342 358 326 454 326), lower := (rows 41 82 133 41 16 32 64 128 256), losses := [] }

theorem u43327 : Upper (D 6) (R 6) [40,80,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43328 : PairBound 9 := { available := 327, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 82 133 42 343 359 327 455 327), lower := (rows 41 82 133 42 16 32 64 128 256), losses := [] }

theorem u43328 : Upper (D 6) (R 6) [40,80,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43329 : PairBound 9 := { available := 327, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 82 133 44 343 359 327 455 327), lower := (rows 41 82 133 44 16 32 64 128 256), losses := [] }

theorem u43329 : Upper (D 6) (R 6) [40,80,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43330 : Route 9 := (fun mask => (mask,id))

def c43330 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43330 : Upper (D 6) (R 6) [40,80,129,65] 13 := by
  apply FastRouting.sound _ _ [40,80,129,65] 13 (by decide) (choices 2) [6,34,36,258,260,288] r43330 c43330
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39315
  · exact u39316
  · exact u39317
  · exact u39318
  · exact u39319
  · exact u39320

def b43331 : PairBound 9 := { available := 295, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 82 133 74 311 295 359 423 295), lower := (rows 41 82 133 74 16 32 64 128 256), losses := [] }

theorem u43331 : Upper (D 6) (R 6) [40,80,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43332 : Route 9 := (fun mask => (mask,id))

def c43332 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43332 : Upper (D 6) (R 6) [40,80,129,68] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r43332 c43332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39321
  · exact u39322
  · exact u39323
  · exact u39324
  · exact u39325
  · exact u39326
  · exact u39327
  · exact u39328
  · exact u39329
  · exact u39330

def b43333 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 82 133 104 279 295 327 391 263), lower := (rows 41 82 133 104 16 32 64 128 256), losses := [] }

theorem u43333 : Upper (D 6) (R 6) [40,80,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43334 : Route 9 := (fun mask => (mask,id))

def c43334 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43334 : Upper (D 6) (R 6) [40,80,129,257] 13 := by
  apply FastRouting.sound _ _ [40,80,129,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43334 c43334
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39331
  · exact u39332
  · exact u39333
  · exact u39334
  · exact u39335
  · exact u39336

def r43335 : Route 9 := (fun mask => (mask,id))

def c43335 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43335 : Upper (D 6) (R 6) [40,80,129,258] 13 := by
  apply FastRouting.sound _ _ [40,80,129,258] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43335 c43335
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39337
  · exact u39338
  · exact u39339
  · exact u39340
  · exact u39341
  · exact u39342
  · exact u39343
  · exact u39344
  · exact u39345
  · exact u39346

def r43336 : Route 9 := (fun mask => (mask,id))

def c43336 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43336 : Upper (D 6) (R 6) [40,80,129,260] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43336 c43336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39347
  · exact u39348
  · exact u39349
  · exact u39350
  · exact u39351
  · exact u39352
  · exact u39353
  · exact u39354
  · exact u39355
  · exact u39356

def b43337 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 214, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 82 133 296 87 103 71 199 327), lower := (rows 41 82 133 296 16 32 64 128 256), losses := [] }

theorem u43337 : Upper (D 6) (R 6) [40,80,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43338 : Route 9 := (fun mask => (mask,id))

def c43338 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43338 : Upper (D 6) (R 6) [40,80,129,320] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43338 c43338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39357
  · exact u39358
  · exact u39359
  · exact u39360
  · exact u39361
  · exact u39362

def r43339 : Route 9 := (fun mask => (mask,id))

def c43339 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43339 : Upper (D 6) (R 6) [40,80,160,3] 13 := by
  apply FastRouting.sound _ _ [40,80,160,3] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43339 c43339
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39363
  · exact u39364
  · exact u39365
  · exact u39366
  · exact u39367
  · exact u39368
  · exact u39369
  · exact u39370
  · exact u39371
  · exact u39372

def b43340 : PairBound 9 := { available := 327, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 164 13 343 359 327 455 327), lower := (rows 41 82 164 13 16 32 64 128 256), losses := [] }

theorem u43340 : Upper (D 6) (R 6) [40,80,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43341 : Route 9 := (fun mask => (mask,id))

def c43341 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43341 : Upper (D 6) (R 6) [40,80,160,6] 13 := by
  apply FastRouting.sound _ _ [40,80,160,6] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43341 c43341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39373
  · exact u39374
  · exact u39375
  · exact u39376
  · exact u39377
  · exact u39378
  · exact u39379
  · exact u39380
  · exact u39381
  · exact u39382

def r43342 : Route 9 := (fun mask => (mask,id))

def c43342 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43342 : Upper (D 6) (R 6) [40,80,160,65] 13 := by
  apply FastRouting.sound _ _ [40,80,160,65] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43342 c43342
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39383
  · exact u39384
  · exact u39385
  · exact u39386
  · exact u39387
  · exact u39388

def b43343 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 82 164 74 279 295 327 391 263), lower := (rows 41 82 164 74 16 32 64 128 256), losses := [] }

theorem u43343 : Upper (D 6) (R 6) [40,80,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43344 : Route 9 := (fun mask => (mask,id))

def c43344 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43344 : Upper (D 6) (R 6) [40,80,160,68] 13 := by
  apply FastRouting.sound _ _ [40,80,160,68] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43344 c43344
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39389
  · exact u39390
  · exact u39391
  · exact u39392
  · exact u39393
  · exact u39394

def r43345 : Route 9 := (fun mask => (mask,id))

def c43345 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43345 : Upper (D 6) (R 6) [40,80,160,257] 13 := by
  apply FastRouting.sound _ _ [40,80,160,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43345 c43345
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39395
  · exact u39396
  · exact u39397
  · exact u39398
  · exact u39399
  · exact u39400

def r43346 : Route 9 := (fun mask => (mask,id))

def c43346 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43346 : Upper (D 6) (R 6) [40,80,160,258] 13 := by
  apply FastRouting.sound _ _ [40,80,160,258] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43346 c43346
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39401
  · exact u39402
  · exact u39403
  · exact u39404
  · exact u39405
  · exact u39406

def r43347 : Route 9 := (fun mask => (mask,id))

def c43347 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43347 : Upper (D 6) (R 6) [40,80,160,260] 13 := by
  apply FastRouting.sound _ _ [40,80,160,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43347 c43347
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39407
  · exact u39408
  · exact u39409
  · exact u39410
  · exact u39411
  · exact u39412

def r43348 : Route 9 := (fun mask => (mask,id))

def c43348 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43348 : Upper (D 6) (R 6) [40,80,160,320] 13 := by
  apply FastRouting.sound _ _ [40,80,160,320] 13 (by decide) (choices 2) [3,5,6] r43348 c43348
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39413
  · exact u39414
  · exact u39415

def r43349 : Route 9 := (fun mask => (mask,id))

def c43349 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43349 : Upper (D 6) (R 6) [40,80,384,3] 13 := by
  apply FastRouting.sound _ _ [40,80,384,3] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43349 c43349
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39416
  · exact u39417
  · exact u39418
  · exact u39419
  · exact u39420
  · exact u39421
  · exact u39422
  · exact u39423
  · exact u39424
  · exact u39425

theorem m43350_3 : Upper (D 6) (R 6) [40,80,384,5,3] 13 :=
  permutation_upper _ _ _ [40,80,384,3,6] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39418

def r43350 : Route 9 := (fun mask => (mask,id))

def c43350 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43350 : Upper (D 6) (R 6) [40,80,384,5] 13 := by
  apply FastRouting.sound _ _ [40,80,384,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43350 c43350
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43350_3
  · exact u39426
  · exact u39427
  · exact u39428
  · exact u39429
  · exact u39430
  · exact u39431
  · exact u39432
  · exact u39433
  · exact u39434

theorem m43351_3 : Upper (D 6) (R 6) [40,80,384,6,3] 13 :=
  permutation_upper _ _ _ [40,80,384,3,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39417

theorem m43351_6 : Upper (D 6) (R 6) [40,80,384,6,6] 13 :=
  permutation_upper _ _ _ [40,80,384,5,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39426

def r43351 : Route 9 := (fun mask => (mask,id))

def c43351 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43351 : Upper (D 6) (R 6) [40,80,384,6] 13 := by
  apply FastRouting.sound _ _ [40,80,384,6] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43351 c43351
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43351_3
  · exact u39435
  · exact m43351_6
  · exact u39436
  · exact u39437
  · exact u39438
  · exact u39439
  · exact u39440
  · exact u39441
  · exact u39442

def b43352 : PairBound 9 := { available := 71, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 388 41 87 103 71 199 327), lower := (rows 41 82 388 41 16 32 64 128 256), losses := [] }

theorem u43352 : Upper (D 6) (R 6) [40,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43353 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 82 388 42 87 103 71 199 327), lower := (rows 41 82 388 42 16 32 64 128 256), losses := [] }

theorem u43353 : Upper (D 6) (R 6) [40,80,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43354 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 82 388 44 87 103 71 199 327), lower := (rows 41 82 388 44 16 32 64 128 256), losses := [] }

theorem u43354 : Upper (D 6) (R 6) [40,80,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43355_3 : Upper (D 6) (R 6) [40,80,384,65,3] 13 :=
  permutation_upper _ _ _ [40,80,384,3,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39420

theorem m43355_5 : Upper (D 6) (R 6) [40,80,384,65,5] 13 :=
  permutation_upper _ _ _ [40,80,384,6,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39437

theorem m43355_6 : Upper (D 6) (R 6) [40,80,384,65,6] 13 :=
  permutation_upper _ _ _ [40,80,384,5,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39429

def r43355 : Route 9 := (fun mask => (mask,id))

def c43355 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43355 : Upper (D 6) (R 6) [40,80,384,65] 13 := by
  apply FastRouting.sound _ _ [40,80,384,65] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43355 c43355
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43355_3
  · exact m43355_5
  · exact m43355_6
  · exact u39443
  · exact u39444
  · exact u39445

def b43356 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 82 388 74 55 39 103 167 295), lower := (rows 41 82 388 74 16 32 64 128 256), losses := [] }

theorem u43356 : Upper (D 6) (R 6) [40,80,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43357_3 : Upper (D 6) (R 6) [40,80,384,68,3] 13 :=
  permutation_upper _ _ _ [40,80,384,3,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39421

theorem m43357_5 : Upper (D 6) (R 6) [40,80,384,68,5] 13 :=
  permutation_upper _ _ _ [40,80,384,6,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39438

theorem m43357_6 : Upper (D 6) (R 6) [40,80,384,68,6] 13 :=
  permutation_upper _ _ _ [40,80,384,5,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39430

theorem m43357_33 : Upper (D 6) (R 6) [40,80,384,68,33] 13 :=
  permutation_upper _ _ _ [40,80,384,66,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39446

theorem m43357_34 : Upper (D 6) (R 6) [40,80,384,68,34] 13 :=
  permutation_upper _ _ _ [40,80,384,65,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39445

def r43357 : Route 9 := (fun mask => (mask,id))

def c43357 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43357 : Upper (D 6) (R 6) [40,80,384,68] 13 := by
  apply FastRouting.sound _ _ [40,80,384,68] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43357 c43357
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43357_3
  · exact m43357_5
  · exact m43357_6
  · exact m43357_33
  · exact m43357_34
  · exact u39447

def b43358 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 82 388 104 23 39 71 135 263), lower := (rows 41 82 388 104 16 32 64 128 256), losses := [] }

theorem u43358 : Upper (D 6) (R 6) [40,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43359 : PairBound 9 := { available := 342, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 133 11 342 374 342 470 342), lower := (rows 41 98 133 11 16 32 64 128 256), losses := [] }

theorem u43359 : Upper (D 6) (R 6) [40,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43360 : PairBound 9 := { available := 342, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 41 98 133 13 342 374 342 470 342), lower := (rows 41 98 133 13 16 32 64 128 256), losses := [] }

theorem u43360 : Upper (D 6) (R 6) [40,96,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43361 : Route 9 := (fun mask => (mask,id))

def c43361 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43361 : Upper (D 6) (R 6) [40,96,129,6] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43361 c43361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39448
  · exact u39449
  · exact u39450
  · exact u39451
  · exact u39452
  · exact u39453
  · exact u39454
  · exact u39455
  · exact u39456
  · exact u39457

def r43362 : Route 9 := (fun mask => (mask,id))

def c43362 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43362 : Upper (D 6) (R 6) [40,96,129,17] 13 := by
  apply FastRouting.sound _ _ [40,96,129,17] 13 (by decide) (choices 2) [6,66,68,258,260,320] r43362 c43362
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39458
  · exact u39459
  · exact u39460
  · exact u39461
  · exact u39462
  · exact u39463

def r43363 : Route 9 := (fun mask => (mask,id))

def c43363 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43363 : Upper (D 6) (R 6) [40,96,129,18] 13 := by
  apply FastRouting.sound _ _ [40,96,129,18] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43363 c43363
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39464
  · exact u39465
  · exact u39466
  · exact u39467
  · exact u39468
  · exact u39469
  · exact u39470
  · exact u39471
  · exact u39472
  · exact u39473

def r43364 : Route 9 := (fun mask => (mask,id))

def c43364 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43364 : Upper (D 6) (R 6) [40,96,129,20] 13 := by
  apply FastRouting.sound _ _ [40,96,129,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43364 c43364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39474
  · exact u39475
  · exact u39476
  · exact u39477
  · exact u39478
  · exact u39479
  · exact u39480
  · exact u39481
  · exact u39482
  · exact u39483

def b43365 : PairBound 9 := { available := 278, camps := [{ cop := 1, region := 9, targets := 2 },{ cop := 1, region := 9, targets := 4 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 98 133 73 278 310 342 406 278), lower := (rows 41 98 133 73 16 32 64 128 256), losses := [] }

theorem u43365 : Upper (D 6) (R 6) [40,96,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43366 : PairBound 9 := { available := 279, camps := [{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 41 98 133 74 279 311 343 407 279), lower := (rows 41 98 133 74 16 32 64 128 256), losses := [] }

theorem u43366 : Upper (D 6) (R 6) [40,96,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43367 : Route 9 := (fun mask => (mask,id))

def c43367 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43367 : Upper (D 6) (R 6) [40,96,129,68] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43367 c43367
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39484
  · exact u39485
  · exact u39486
  · exact u39487
  · exact u39488
  · exact u39489

def r43368 : Route 9 := (fun mask => (mask,id))

def c43368 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43368 : Upper (D 6) (R 6) [40,96,129,80] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43368 c43368
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39490
  · exact u39491
  · exact u39492
  · exact u39493
  · exact u39494
  · exact u39495

def r43369 : Route 9 := (fun mask => (mask,id))

def c43369 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43369 : Upper (D 6) (R 6) [40,96,129,257] 13 := by
  apply FastRouting.sound _ _ [40,96,129,257] 13 (by decide) (choices 2) [6,66,68] r43369 c43369
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39496
  · exact u39497
  · exact u39498

def r43370 : Route 9 := (fun mask => (mask,id))

def c43370 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43370 : Upper (D 6) (R 6) [40,96,129,258] 13 := by
  apply FastRouting.sound _ _ [40,96,129,258] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43370 c43370
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39499
  · exact u39500
  · exact u39501
  · exact u39502
  · exact u39503
  · exact u39504

def r43371 : Route 9 := (fun mask => (mask,id))

def c43371 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43371 : Upper (D 6) (R 6) [40,96,129,260] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43371 c43371
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39505
  · exact u39506
  · exact u39507
  · exact u39508
  · exact u39509
  · exact u39510

def r43372 : Route 9 := (fun mask => (mask,id))

def c43372 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43372 : Upper (D 6) (R 6) [40,96,129,272] 13 := by
  apply FastRouting.sound _ _ [40,96,129,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43372 c43372
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39511
  · exact u39512
  · exact u39513
  · exact u39514
  · exact u39515
  · exact u39516

def r43373 : Route 9 := (fun mask => (mask,id))

def c43373 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43373 : Upper (D 6) (R 6) [40,96,129,320] 13 := by
  apply FastRouting.sound _ _ [40,96,129,320] 13 (by decide) (choices 2) [3,5,6] r43373 c43373
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39517
  · exact u39518
  · exact u39519

def b43374 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 134 11 341 373 341 469 341), lower := (rows 41 98 134 11 16 32 64 128 256), losses := [] }

theorem u43374 : Upper (D 6) (R 6) [40,96,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43375 : Route 9 := (fun mask => (mask,id))

def c43375 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43375 : Upper (D 6) (R 6) [40,96,130,5] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43375 c43375
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39520
  · exact u39521
  · exact u39522
  · exact u39523
  · exact u39524
  · exact u39525
  · exact u39526
  · exact u39527
  · exact u39528
  · exact u39529

def b43376 : PairBound 9 := { available := 341, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 98 134 14 341 373 341 469 341), lower := (rows 41 98 134 14 16 32 64 128 256), losses := [] }

theorem u43376 : Upper (D 6) (R 6) [40,96,130,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43377 : Route 9 := (fun mask => (mask,id))

def c43377 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43377 : Upper (D 6) (R 6) [40,96,130,17] 13 := by
  apply FastRouting.sound _ _ [40,96,130,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43377 c43377
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39530
  · exact u39531
  · exact u39532
  · exact u39533
  · exact u39534
  · exact u39535
  · exact u39536
  · exact u39537
  · exact u39538
  · exact u39539

def r43378 : Route 9 := (fun mask => (mask,id))

def c43378 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43378 : Upper (D 6) (R 6) [40,96,130,18] 13 := by
  apply FastRouting.sound _ _ [40,96,130,18] 13 (by decide) (choices 2) [5,65,68,257,260,320] r43378 c43378
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39540
  · exact u39541
  · exact u39542
  · exact u39543
  · exact u39544
  · exact u39545

def r43379 : Route 9 := (fun mask => (mask,id))

def c43379 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43379 : Upper (D 6) (R 6) [40,96,130,20] 13 := by
  apply FastRouting.sound _ _ [40,96,130,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43379 c43379
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39546
  · exact u39547
  · exact u39548
  · exact u39549
  · exact u39550
  · exact u39551
  · exact u39552
  · exact u39553
  · exact u39554
  · exact u39555

#print axioms u43379
end Delivery.IrregularNine14.P06
