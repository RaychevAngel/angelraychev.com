import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0537
import IrregularNine14P07C0538
import IrregularNine14P07C0539
import IrregularNine14P07C0540

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m41580_3 : Upper (D 7) (R 7) [6,288,192,17,3] 13 :=
  permutation_upper _ _ _ [6,288,192,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32276

def r41580 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41580 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41580 : Upper (D 7) (R 7) [6,288,192,17] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r41580 c41580
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41580_3
  · exact u32282
  · exact u32283
  · exact u32284
  · exact u32285
  · exact u32286
  · exact u32287
  · exact u32288
  · exact u32289
  · exact u32290
  · exact u32291

theorem m41581_9 : Upper (D 7) (R 7) [6,288,192,18,9] 13 :=
  permutation_upper _ _ _ [6,288,192,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32283

def r41581 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41581 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41581 : Upper (D 7) (R 7) [6,288,192,18] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r41581 c41581
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41581_9
  · exact u32292
  · exact u32293
  · exact u32294
  · exact u32295
  · exact u32296
  · exact u32297

theorem m41582_3 : Upper (D 7) (R 7) [6,288,192,33,3] 13 :=
  permutation_upper _ _ _ [6,288,192,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32277

theorem m41582_9 : Upper (D 7) (R 7) [6,288,192,33,9] 13 :=
  permutation_upper _ _ _ [6,288,192,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32284

theorem m41582_10 : Upper (D 7) (R 7) [6,288,192,33,10] 13 :=
  permutation_upper _ _ _ [6,288,192,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32292

def r41582 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41582 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41582 : Upper (D 7) (R 7) [6,288,192,33] 13 := by
  apply FastRouting.sound _ _ [6,288,192,33] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r41582 c41582
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41582_3
  · exact m41582_9
  · exact m41582_10
  · exact u32298
  · exact u32299
  · exact u32300
  · exact u32301

def b41583 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 196 42 217 249 217 217 473), lower := (rows 7 290 196 42 16 32 64 128 256), losses := [] }

theorem u41583 : Upper (D 7) (R 7) [6,288,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41584_3 : Upper (D 7) (R 7) [6,288,192,48,3] 13 :=
  permutation_upper _ _ _ [6,288,192,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32278

theorem m41584_9 : Upper (D 7) (R 7) [6,288,192,48,9] 13 :=
  permutation_upper _ _ _ [6,288,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32286

theorem m41584_10 : Upper (D 7) (R 7) [6,288,192,48,10] 13 :=
  permutation_upper _ _ _ [6,288,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32293

def r41584 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41584 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41584 : Upper (D 7) (R 7) [6,288,192,48] 13 := by
  apply FastRouting.sound _ _ [6,288,192,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r41584 c41584
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41584_3
  · exact m41584_9
  · exact m41584_10
  · exact u32304
  · exact u32305
  · exact u32306
  · exact u32307

theorem m41585_3 : Upper (D 7) (R 7) [6,288,192,65,3] 13 :=
  permutation_upper _ _ _ [6,288,192,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32279

theorem m41585_9 : Upper (D 7) (R 7) [6,288,192,65,9] 13 :=
  permutation_upper _ _ _ [6,288,192,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32287

theorem m41585_10 : Upper (D 7) (R 7) [6,288,192,65,10] 13 :=
  permutation_upper _ _ _ [6,288,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32294

theorem m41585_33 : Upper (D 7) (R 7) [6,288,192,65,33] 13 :=
  permutation_upper _ _ _ [6,288,192,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32298

theorem m41585_34 : Upper (D 7) (R 7) [6,288,192,65,34] 13 :=
  permutation_upper _ _ _ [6,288,192,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32302

theorem m41585_40 : Upper (D 7) (R 7) [6,288,192,65,40] 13 :=
  permutation_upper _ _ _ [6,288,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32304

def r41585 : Route 9 := (fun mask => (mask,id))

def c41585 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41585 : Upper (D 7) (R 7) [6,288,192,65] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r41585 c41585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41585_3
  · exact m41585_9
  · exact m41585_10
  · exact m41585_33
  · exact m41585_34
  · exact m41585_40
  · exact u32308
  · exact u32309
  · exact u32310
  · exact u32311

theorem m41586_9 : Upper (D 7) (R 7) [6,288,192,66,9] 13 :=
  permutation_upper _ _ _ [6,288,192,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32288

theorem m41586_33 : Upper (D 7) (R 7) [6,288,192,66,33] 13 :=
  permutation_upper _ _ _ [6,288,192,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32299

theorem m41586_40 : Upper (D 7) (R 7) [6,288,192,66,40] 13 :=
  permutation_upper _ _ _ [6,288,192,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32305

theorem m41586_129 : Upper (D 7) (R 7) [6,288,192,66,129] 13 :=
  permutation_upper _ _ _ [6,288,192,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32309

def r41586 : Route 9 := (fun mask => (mask,id))

def c41586 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41586 : Upper (D 7) (R 7) [6,288,192,66] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r41586 c41586
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41586_9
  · exact m41586_33
  · exact m41586_40
  · exact m41586_129
  · exact u32312
  · exact u32313

theorem m41587_3 : Upper (D 7) (R 7) [6,288,192,80,3] 13 :=
  permutation_upper _ _ _ [6,288,192,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32280

theorem m41587_9 : Upper (D 7) (R 7) [6,288,192,80,9] 13 :=
  permutation_upper _ _ _ [6,288,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32289

theorem m41587_10 : Upper (D 7) (R 7) [6,288,192,80,10] 13 :=
  permutation_upper _ _ _ [6,288,192,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32295

theorem m41587_33 : Upper (D 7) (R 7) [6,288,192,80,33] 13 :=
  permutation_upper _ _ _ [6,288,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32300

theorem m41587_34 : Upper (D 7) (R 7) [6,288,192,80,34] 13 :=
  permutation_upper _ _ _ [6,288,192,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32303

theorem m41587_40 : Upper (D 7) (R 7) [6,288,192,80,40] 13 :=
  permutation_upper _ _ _ [6,288,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32306

theorem m41587_129 : Upper (D 7) (R 7) [6,288,192,80,129] 13 :=
  permutation_upper _ _ _ [6,288,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32310

theorem m41587_130 : Upper (D 7) (R 7) [6,288,192,80,130] 13 :=
  permutation_upper _ _ _ [6,288,192,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32312

def r41587 : Route 9 := (fun mask => (mask,id))

def c41587 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41587 : Upper (D 7) (R 7) [6,288,192,80] 13 := by
  apply FastRouting.sound _ _ [6,288,192,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r41587 c41587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41587_3
  · exact m41587_9
  · exact m41587_10
  · exact m41587_33
  · exact m41587_34
  · exact m41587_40
  · exact m41587_129
  · exact m41587_130
  · exact u32314
  · exact u32315

theorem m41588_3 : Upper (D 7) (R 7) [6,288,192,96,3] 13 :=
  permutation_upper _ _ _ [6,288,192,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32281

theorem m41588_9 : Upper (D 7) (R 7) [6,288,192,96,9] 13 :=
  permutation_upper _ _ _ [6,288,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32290

theorem m41588_10 : Upper (D 7) (R 7) [6,288,192,96,10] 13 :=
  permutation_upper _ _ _ [6,288,192,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32296

theorem m41588_129 : Upper (D 7) (R 7) [6,288,192,96,129] 13 :=
  permutation_upper _ _ _ [6,288,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32311

theorem m41588_130 : Upper (D 7) (R 7) [6,288,192,96,130] 13 :=
  permutation_upper _ _ _ [6,288,192,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32313

theorem m41588_136 : Upper (D 7) (R 7) [6,288,192,96,136] 13 :=
  permutation_upper _ _ _ [6,288,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32315

def r41588 : Route 9 := (fun mask => (mask,id))

def c41588 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41588 : Upper (D 7) (R 7) [6,288,192,96] 13 := by
  apply FastRouting.sound _ _ [6,288,192,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r41588 c41588
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41588_3
  · exact m41588_9
  · exact m41588_10
  · exact m41588_129
  · exact m41588_130
  · exact m41588_136

def b41589 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 7 290 196 200 59 59 123 187 315), lower := (rows 7 290 196 200 16 32 64 128 256), losses := [] }

theorem u41589 : Upper (D 7) (R 7) [6,288,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41590 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 35 7 26 496 480 480 480 480), lower := (rows 13 35 7 26 16 32 64 128 256), losses := [] }

theorem u41590 : Upper (D 7) (R 7) [12,33,3,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41591 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 13 35 7 56 466 482 450 450 450), lower := (rows 13 35 7 56 16 32 64 128 256), losses := [] }

theorem u41591 : Upper (D 7) (R 7) [12,33,3,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41592 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 35 7 74 496 496 496 496 496), lower := (rows 13 35 7 74 16 32 64 128 256), losses := [] }

theorem u41592 : Upper (D 7) (R 7) [12,33,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41593 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 13 35 7 88 498 482 482 482 482), lower := (rows 13 35 7 88 16 32 64 128 256), losses := [] }

theorem u41593 : Upper (D 7) (R 7) [12,33,3,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41594 : PairBound 9 := { available := 466, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 13 35 7 104 466 498 466 466 466), lower := (rows 13 35 7 104 16 32 64 128 256), losses := [] }

theorem u41594 : Upper (D 7) (R 7) [12,33,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41595 : PairBound 9 := { available := 498, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 13 35 7 200 498 498 498 498 498), lower := (rows 13 35 7 200 16 32 64 128 256), losses := [] }

theorem u41595 : Upper (D 7) (R 7) [12,33,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41596 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 35 7 266 240 240 240 240 496), lower := (rows 13 35 7 266 16 32 64 128 256), losses := [] }

theorem u41596 : Upper (D 7) (R 7) [12,33,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41597 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 13 35 7 280 242 226 226 226 482), lower := (rows 13 35 7 280 16 32 64 128 256), losses := [] }

theorem u41597 : Upper (D 7) (R 7) [12,33,3,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41598 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 13 35 7 296 210 242 210 210 466), lower := (rows 13 35 7 296 16 32 64 128 256), losses := [] }

theorem u41598 : Upper (D 7) (R 7) [12,33,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41599 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 13 35 7 328 242 242 242 242 498), lower := (rows 13 35 7 328 16 32 64 128 256), losses := [] }

theorem u41599 : Upper (D 7) (R 7) [12,33,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41600 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 1, region := 8, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 35 21 42 466 482 450 450 450), lower := (rows 13 35 21 42 16 32 64 128 256), losses := [] }

theorem u41600 : Upper (D 7) (R 7) [12,33,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41601 : Route 9 := (fun mask => (mask,id))

def c41601 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41601 : Upper (D 7) (R 7) [12,33,17,66] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41601 c41601
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32316
  · exact u32317
  · exact u32318
  · exact u32319
  · exact u32320
  · exact u32321
  · exact u32322
  · exact u32323
  · exact u32324
  · exact u32325

def b41602 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 468, targets := 32 }], pairs := [(2,5),(3,0),(4,0),(4,5)], upper := (rows 13 35 21 104 466 482 450 450 450), lower := (rows 13 35 21 104 16 32 64 128 256), losses := [] }

theorem u41602 : Upper (D 7) (R 7) [12,33,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41603 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41603 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41603 : Upper (D 7) (R 7) [12,33,17,192] 13 := by
  apply FastRouting.sound _ _ [12,33,17,192] 13 (by decide) (choices 2) [34,66,96,192,258,288,320] r41603 c41603
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32326
  · exact u32327
  · exact u32328
  · exact u32329
  · exact u32330
  · exact u32331
  · exact u32332

def r41604 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41604 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41604 : Upper (D 7) (R 7) [12,33,17,258] 13 := by
  apply FastRouting.sound _ _ [12,33,17,258] 13 (by decide) (choices 2) [34,66,96,192] r41604 c41604
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32333
  · exact u32334
  · exact u32335
  · exact u32336

def b41605 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5),(3,0),(4,0),(4,5)], upper := (rows 13 35 21 296 210 226 194 194 450), lower := (rows 13 35 21 296 16 32 64 128 256), losses := [] }

theorem u41605 : Upper (D 7) (R 7) [12,33,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41606 : Route 9 := (fun mask => (mask,id))

def c41606 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41606 : Upper (D 7) (R 7) [12,33,17,320] 13 := by
  apply FastRouting.sound _ _ [12,33,17,320] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41606 c41606
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32337
  · exact u32338
  · exact u32339
  · exact u32340
  · exact u32341
  · exact u32342

def b41607 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 468, targets := 32 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 13 35 22 41 466 482 450 450 450), lower := (rows 13 35 22 41 16 32 64 128 256), losses := [] }

theorem u41607 : Upper (D 7) (R 7) [12,33,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41608 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 13 35 22 42 465 481 449 449 449), lower := (rows 13 35 22 42 16 32 64 128 256), losses := [] }

theorem u41608 : Upper (D 7) (R 7) [12,33,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41609 : Route 9 := (fun mask => (mask,id))

def c41609 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41609 : Upper (D 7) (R 7) [12,33,18,65] 13 := by
  apply FastRouting.sound _ _ [12,33,18,65] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41609 c41609
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32343
  · exact u32344
  · exact u32345
  · exact u32346
  · exact u32347
  · exact u32348
  · exact u32349
  · exact u32350
  · exact u32351
  · exact u32352

def r41610 : Route 9 := (fun mask => (mask,id))

def c41610 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41610 : Upper (D 7) (R 7) [12,33,18,66] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41610 c41610
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32353
  · exact u32354
  · exact u32355
  · exact u32356
  · exact u32357
  · exact u32358
  · exact u32359
  · exact u32360
  · exact u32361
  · exact u32362

def r41611 : Route 9 := (fun mask => (mask,id))

def c41611 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41611 : Upper (D 7) (R 7) [12,33,18,96] 13 := by
  apply FastRouting.sound _ _ [12,33,18,96] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41611 c41611
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32363
  · exact u32364
  · exact u32365
  · exact u32366
  · exact u32367
  · exact u32368
  · exact u32369
  · exact u32370
  · exact u32371
  · exact u32372

def r41612 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41612 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41612 : Upper (D 7) (R 7) [12,33,18,192] 13 := by
  apply FastRouting.sound _ _ [12,33,18,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r41612 c41612
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32373
  · exact u32374
  · exact u32375
  · exact u32376
  · exact u32377
  · exact u32378
  · exact u32379
  · exact u32380
  · exact u32381
  · exact u32382
  · exact u32383

def r41613 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41613 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41613 : Upper (D 7) (R 7) [12,33,18,257] 13 := by
  apply FastRouting.sound _ _ [12,33,18,257] 13 (by decide) (choices 2) [34,66,96,192] r41613 c41613
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32384
  · exact u32385
  · exact u32386
  · exact u32387

def r41614 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41614 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41614 : Upper (D 7) (R 7) [12,33,18,258] 13 := by
  apply FastRouting.sound _ _ [12,33,18,258] 13 (by decide) (choices 2) [33,65,96,192] r41614 c41614
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32388
  · exact u32389
  · exact u32390
  · exact u32391

def r41615 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41615 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41615 : Upper (D 7) (R 7) [12,33,18,288] 13 := by
  apply FastRouting.sound _ _ [12,33,18,288] 13 (by decide) (choices 2) [3,65,66,192] r41615 c41615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32392
  · exact u32393
  · exact u32394
  · exact u32395

def r41616 : Route 9 := (fun mask => (mask,id))

def c41616 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41616 : Upper (D 7) (R 7) [12,33,18,320] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41616 c41616
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32396
  · exact u32397
  · exact u32398
  · exact u32399
  · exact u32400
  · exact u32401
  · exact u32402
  · exact u32403
  · exact u32404
  · exact u32405

def b41617 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 37 74 466 498 466 466 466), lower := (rows 13 35 37 74 16 32 64 128 256), losses := [] }

theorem u41617 : Upper (D 7) (R 7) [12,33,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41618 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 37 88 466 482 450 450 450), lower := (rows 13 35 37 88 16 32 64 128 256), losses := [] }

theorem u41618 : Upper (D 7) (R 7) [12,33,33,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41619 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 37 200 466 498 466 466 466), lower := (rows 13 35 37 200 16 32 64 128 256), losses := [] }

theorem u41619 : Upper (D 7) (R 7) [12,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41620 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 37 266 210 242 210 210 466), lower := (rows 13 35 37 266 16 32 64 128 256), losses := [] }

theorem u41620 : Upper (D 7) (R 7) [12,33,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41621 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 37 280 210 226 194 194 450), lower := (rows 13 35 37 280 16 32 64 128 256), losses := [] }

theorem u41621 : Upper (D 7) (R 7) [12,33,33,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41622 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 37 328 210 242 210 210 466), lower := (rows 13 35 37 328 16 32 64 128 256), losses := [] }

theorem u41622 : Upper (D 7) (R 7) [12,33,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41623 : PairBound 9 := { available := 466, camps := [{ cop := 2, region := 473, targets := 32 },{ cop := 1, region := 4, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 35 38 73 466 498 466 466 466), lower := (rows 13 35 38 73 16 32 64 128 256), losses := [] }

theorem u41623 : Upper (D 7) (R 7) [12,33,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41624 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 35 38 74 465 497 465 465 465), lower := (rows 13 35 38 74 16 32 64 128 256), losses := [] }

theorem u41624 : Upper (D 7) (R 7) [12,33,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41625 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 35 38 88 467 483 451 451 451), lower := (rows 13 35 38 88 16 32 64 128 256), losses := [] }

theorem u41625 : Upper (D 7) (R 7) [12,33,34,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41626 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 35 38 200 467 499 467 467 467), lower := (rows 13 35 38 200 16 32 64 128 256), losses := [] }

theorem u41626 : Upper (D 7) (R 7) [12,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41627 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 473, targets := 32 },{ cop := 1, region := 4, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 35 38 265 210 242 210 210 466), lower := (rows 13 35 38 265 16 32 64 128 256), losses := [] }

theorem u41627 : Upper (D 7) (R 7) [12,33,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41628 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 35 38 266 209 241 209 209 465), lower := (rows 13 35 38 266 16 32 64 128 256), losses := [] }

theorem u41628 : Upper (D 7) (R 7) [12,33,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41629 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 35 38 280 211 227 195 195 451), lower := (rows 13 35 38 280 16 32 64 128 256), losses := [] }

theorem u41629 : Upper (D 7) (R 7) [12,33,34,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41630 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 35 38 328 211 243 211 211 467), lower := (rows 13 35 38 328 16 32 64 128 256), losses := [] }

theorem u41630 : Upper (D 7) (R 7) [12,33,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41631 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 52 73 466 482 450 450 450), lower := (rows 13 35 52 73 16 32 64 128 256), losses := [] }

theorem u41631 : Upper (D 7) (R 7) [12,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41632 : Route 9 := (fun mask => (mask,id))

def c41632 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41632 : Upper (D 7) (R 7) [12,33,48,66] 13 := by
  apply FastRouting.sound _ _ [12,33,48,66] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41632 c41632
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32406
  · exact u32407
  · exact u32408
  · exact u32409
  · exact u32410
  · exact u32411
  · exact u32412
  · exact u32413
  · exact u32414
  · exact u32415

def r41633 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41633 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41633 : Upper (D 7) (R 7) [12,33,48,192] 13 := by
  apply FastRouting.sound _ _ [12,33,48,192] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r41633 c41633
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32416
  · exact u32417
  · exact u32418
  · exact u32419
  · exact u32420
  · exact u32421
  · exact u32422

def b41634 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 52 265 210 226 194 194 450), lower := (rows 13 35 52 265 16 32 64 128 256), losses := [] }

theorem u41634 : Upper (D 7) (R 7) [12,33,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41635 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41635 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41635 : Upper (D 7) (R 7) [12,33,48,258] 13 := by
  apply FastRouting.sound _ _ [12,33,48,258] 13 (by decide) (choices 2) [3,65,66,192] r41635 c41635
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32423
  · exact u32424
  · exact u32425
  · exact u32426

def r41636 : Route 9 := (fun mask => (mask,id))

def c41636 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41636 : Upper (D 7) (R 7) [12,33,48,320] 13 := by
  apply FastRouting.sound _ _ [12,33,48,320] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41636 c41636
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32427
  · exact u32428
  · exact u32429
  · exact u32430
  · exact u32431
  · exact u32432

def b41637 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 35 69 74 434 434 498 434 434), lower := (rows 13 35 69 74 16 32 64 128 256), losses := [] }

theorem u41637 : Upper (D 7) (R 7) [12,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41638 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 35 69 88 434 418 482 418 418), lower := (rows 13 35 69 88 16 32 64 128 256), losses := [] }

theorem u41638 : Upper (D 7) (R 7) [12,33,65,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41639 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 5, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 35 69 104 402 434 466 402 402), lower := (rows 13 35 69 104 16 32 64 128 256), losses := [] }

theorem u41639 : Upper (D 7) (R 7) [12,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u41639
end Delivery.IrregularNine14.P07
