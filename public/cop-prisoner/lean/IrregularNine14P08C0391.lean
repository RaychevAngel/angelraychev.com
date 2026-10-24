import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0297
import IrregularNine14P08C0298
import IrregularNine14P08C0299
import IrregularNine14P08C0300
import IrregularNine14P08C0301
import IrregularNine14P08C0302
import IrregularNine14P08C0303
import IrregularNine14P08C0304
import IrregularNine14P08C0305
import IrregularNine14P08C0306
import IrregularNine14P08C0307

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m23460_33 : Upper (D 8) (R 8) [320,12,18,160,33] 13 :=
  permutation_upper _ _ _ [320,12,18,33,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18253

theorem m23460_65 : Upper (D 8) (R 8) [320,12,18,160,65] 13 :=
  permutation_upper _ _ _ [320,12,18,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18256

theorem m23460_96 : Upper (D 8) (R 8) [320,12,18,160,96] 13 :=
  permutation_upper _ _ _ [320,12,18,96,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18258

theorem m23460_129 : Upper (D 8) (R 8) [320,12,18,160,129] 13 :=
  permutation_upper _ _ _ [320,12,18,129,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18260

def r23460 : Route 9 := (fun mask => (mask,id))

def c23460 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23460 : Upper (D 8) (R 8) [320,12,18,160] 13 := by
  apply FastRouting.sound _ _ [320,12,18,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23460 c23460
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23460_33
  · exact m23460_65
  · exact m23460_96
  · exact m23460_129
  · exact u18262
  · exact u18263

def b23461 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 22 200 177 161 225 161 417), lower := (rows 321 14 22 200 16 32 64 128 256), losses := [] }

theorem u23461 : Upper (D 8) (R 8) [320,12,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23462 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 41 242 242 242 242 498), lower := (rows 321 14 37 41 16 32 64 128 256), losses := [] }

theorem u23462 : Upper (D 8) (R 8) [320,12,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23463 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 42 241 241 241 241 497), lower := (rows 321 14 37 42 16 32 64 128 256), losses := [] }

theorem u23463 : Upper (D 8) (R 8) [320,12,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23464_3 : Upper (D 8) (R 8) [320,12,33,48,3] 13 :=
  permutation_upper _ _ _ [320,5,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17856

def r23464 : Route 9 := (fun mask => (mask,id))

def c23464 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23464 : Upper (D 8) (R 8) [320,12,33,48] 13 := by
  apply FastRouting.sound _ _ [320,12,33,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23464 c23464
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23464_3
  · exact u18275
  · exact u18276
  · exact u18277
  · exact u18278
  · exact u18279
  · exact u18280
  · exact u18281
  · exact u18282
  · exact u18283

def b23465 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 73 178 178 242 178 434), lower := (rows 321 14 37 73 16 32 64 128 256), losses := [] }

theorem u23465 : Upper (D 8) (R 8) [320,12,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23466 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 74 177 177 241 177 433), lower := (rows 321 14 37 74 16 32 64 128 256), losses := [] }

theorem u23466 : Upper (D 8) (R 8) [320,12,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23467_3 : Upper (D 8) (R 8) [320,12,33,80,3] 13 :=
  permutation_upper _ _ _ [320,5,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17857

def r23467 : Route 9 := (fun mask => (mask,id))

def c23467 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23467 : Upper (D 8) (R 8) [320,12,33,80] 13 := by
  apply FastRouting.sound _ _ [320,12,33,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23467 c23467
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23467_3
  · exact u18289
  · exact u18290
  · exact u18291
  · exact u18292
  · exact u18293

theorem m23468_3 : Upper (D 8) (R 8) [320,12,33,96,3] 13 :=
  permutation_upper _ _ _ [320,5,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17858

def r23468 : Route 9 := (fun mask => (mask,id))

def c23468 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23468 : Upper (D 8) (R 8) [320,12,33,96] 13 := by
  apply FastRouting.sound _ _ [320,12,33,96] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23468 c23468
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23468_3
  · exact u18294
  · exact u18295
  · exact u18296
  · exact u18297
  · exact u18298

def b23469 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 137 242 242 242 242 498), lower := (rows 321 14 37 137 16 32 64 128 256), losses := [] }

theorem u23469 : Upper (D 8) (R 8) [320,12,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23470 : Route 9 := (fun mask => (mask,id))

def c23470 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23470 : Upper (D 8) (R 8) [320,12,33,130] 13 := by
  apply FastRouting.sound _ _ [320,12,33,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23470 c23470
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18305
  · exact u18306
  · exact u18307
  · exact u18308
  · exact u18309
  · exact u18310

theorem m23471_3 : Upper (D 8) (R 8) [320,12,33,144,3] 13 :=
  permutation_upper _ _ _ [320,5,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17859

def r23471 : Route 9 := (fun mask => (mask,id))

def c23471 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23471 : Upper (D 8) (R 8) [320,12,33,144] 13 := by
  apply FastRouting.sound _ _ [320,12,33,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23471 c23471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23471_3
  · exact u18311
  · exact u18312
  · exact u18313
  · exact u18314
  · exact u18315
  · exact u18316
  · exact u18317
  · exact u18318
  · exact u18319

theorem m23472_3 : Upper (D 8) (R 8) [320,12,33,160,3] 13 :=
  permutation_upper _ _ _ [320,5,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17860

def r23472 : Route 9 := (fun mask => (mask,id))

def c23472 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23472 : Upper (D 8) (R 8) [320,12,33,160] 13 := by
  apply FastRouting.sound _ _ [320,12,33,160] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23472 c23472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23472_3
  · exact u18320
  · exact u18321
  · exact u18322
  · exact u18323
  · exact u18324
  · exact u18325
  · exact u18326
  · exact u18327
  · exact u18328

theorem m23473_3 : Upper (D 8) (R 8) [320,12,33,192,3] 13 :=
  permutation_upper _ _ _ [320,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17861

def r23473 : Route 9 := (fun mask => (mask,id))

def c23473 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23473 : Upper (D 8) (R 8) [320,12,33,192] 13 := by
  apply FastRouting.sound _ _ [320,12,33,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23473 c23473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23473_3
  · exact u18329
  · exact u18330
  · exact u18331
  · exact u18332
  · exact u18333

def b23474 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 56 241 225 225 225 481), lower := (rows 321 14 38 56 16 32 64 128 256), losses := [] }

theorem u23474 : Upper (D 8) (R 8) [320,12,34,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23475 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 73 177 177 241 177 433), lower := (rows 321 14 38 73 16 32 64 128 256), losses := [] }

theorem u23475 : Upper (D 8) (R 8) [320,12,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23476 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 38 88 177 161 225 161 417), lower := (rows 321 14 38 88 16 32 64 128 256), losses := [] }

theorem u23476 : Upper (D 8) (R 8) [320,12,34,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23477 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 104 177 177 241 177 433), lower := (rows 321 14 38 104 16 32 64 128 256), losses := [] }

theorem u23477 : Upper (D 8) (R 8) [320,12,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23478 : Route 9 := (fun mask => (mask,id))

def c23478 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23478 : Upper (D 8) (R 8) [320,12,34,129] 13 := by
  apply FastRouting.sound _ _ [320,12,34,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23478 c23478
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18348
  · exact u18349
  · exact u18350
  · exact u18351
  · exact u18352
  · exact u18353

def r23479 : Route 9 := (fun mask => (mask,id))

def c23479 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23479 : Upper (D 8) (R 8) [320,12,34,144] 13 := by
  apply FastRouting.sound _ _ [320,12,34,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23479 c23479
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18354
  · exact u18355
  · exact u18356
  · exact u18357
  · exact u18358
  · exact u18359

def b23480 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 168 241 241 241 241 497), lower := (rows 321 14 38 168 16 32 64 128 256), losses := [] }

theorem u23480 : Upper (D 8) (R 8) [320,12,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23481 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 38 200 177 177 241 177 433), lower := (rows 321 14 38 200 16 32 64 128 256), losses := [] }

theorem u23481 : Upper (D 8) (R 8) [320,12,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23482 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 52 73 179 163 227 163 419), lower := (rows 321 14 52 73 16 32 64 128 256), losses := [] }

theorem u23482 : Upper (D 8) (R 8) [320,12,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23483 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 52 74 177 161 225 161 417), lower := (rows 321 14 52 74 16 32 64 128 256), losses := [] }

theorem u23483 : Upper (D 8) (R 8) [320,12,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23484_3 : Upper (D 8) (R 8) [320,12,48,96,3] 13 :=
  permutation_upper _ _ _ [320,5,24,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17863

def r23484 : Route 9 := (fun mask => (mask,id))

def c23484 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23484 : Upper (D 8) (R 8) [320,12,48,96] 13 := by
  apply FastRouting.sound _ _ [320,12,48,96] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23484 c23484
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23484_3
  · exact u18371
  · exact u18372
  · exact u18373
  · exact u18374
  · exact u18375

theorem m23485_3 : Upper (D 8) (R 8) [320,12,48,129,3] 13 :=
  permutation_upper _ _ _ [320,5,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17864

def r23485 : Route 9 := (fun mask => (mask,id))

def c23485 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23485 : Upper (D 8) (R 8) [320,12,48,129] 13 := by
  apply FastRouting.sound _ _ [320,12,48,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23485 c23485
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23485_3
  · exact u18376
  · exact u18377
  · exact u18378
  · exact u18379
  · exact u18380
  · exact u18381
  · exact u18382
  · exact u18383
  · exact u18384

def r23486 : Route 9 := (fun mask => (mask,id))

def c23486 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23486 : Upper (D 8) (R 8) [320,12,48,130] 13 := by
  apply FastRouting.sound _ _ [320,12,48,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23486 c23486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u18385
  · exact u18386
  · exact u18387
  · exact u18388
  · exact u18389
  · exact u18390

theorem m23487_3 : Upper (D 8) (R 8) [320,12,48,160,3] 13 :=
  permutation_upper _ _ _ [320,5,24,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17865

def r23487 : Route 9 := (fun mask => (mask,id))

def c23487 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23487 : Upper (D 8) (R 8) [320,12,48,160] 13 := by
  apply FastRouting.sound _ _ [320,12,48,160] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23487 c23487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23487_3
  · exact u18391
  · exact u18392
  · exact u18393
  · exact u18394
  · exact u18395
  · exact u18396
  · exact u18397
  · exact u18398
  · exact u18399

theorem m23488_3 : Upper (D 8) (R 8) [320,12,48,192,3] 13 :=
  permutation_upper _ _ _ [320,5,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17866

def r23488 : Route 9 := (fun mask => (mask,id))

def c23488 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23488 : Upper (D 8) (R 8) [320,12,48,192] 13 := by
  apply FastRouting.sound _ _ [320,12,48,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23488 c23488
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23488_3
  · exact u18400
  · exact u18401
  · exact u18402
  · exact u18403
  · exact u18404

def b23489 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 137 178 178 242 178 434), lower := (rows 321 14 69 137 16 32 64 128 256), losses := [] }

theorem u23489 : Upper (D 8) (R 8) [320,12,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23490 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 138 177 177 241 177 433), lower := (rows 321 14 69 138 16 32 64 128 256), losses := [] }

theorem u23490 : Upper (D 8) (R 8) [320,12,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23491 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 152 179 163 227 163 419), lower := (rows 321 14 69 152 16 32 64 128 256), losses := [] }

theorem u23491 : Upper (D 8) (R 8) [320,12,65,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23492 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 168 179 179 243 179 435), lower := (rows 321 14 69 168 16 32 64 128 256), losses := [] }

theorem u23492 : Upper (D 8) (R 8) [320,12,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23493 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 70 137 177 177 241 177 433), lower := (rows 321 14 70 137 16 32 64 128 256), losses := [] }

theorem u23493 : Upper (D 8) (R 8) [320,12,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23494 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 70 152 177 161 225 161 417), lower := (rows 321 14 70 152 16 32 64 128 256), losses := [] }

theorem u23494 : Upper (D 8) (R 8) [320,12,66,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23495 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 70 168 177 177 241 177 433), lower := (rows 321 14 70 168 16 32 64 128 256), losses := [] }

theorem u23495 : Upper (D 8) (R 8) [320,12,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23496_3 : Upper (D 8) (R 8) [320,12,80,129,3] 13 :=
  permutation_upper _ _ _ [320,5,24,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17869

def r23496 : Route 9 := (fun mask => (mask,id))

def c23496 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23496 : Upper (D 8) (R 8) [320,12,80,129] 13 := by
  apply FastRouting.sound _ _ [320,12,80,129] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23496 c23496
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23496_3
  · exact u18418
  · exact u18419
  · exact u18420
  · exact u18421
  · exact u18422

def b23497 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 84 138 177 161 225 161 417), lower := (rows 321 14 84 138 16 32 64 128 256), losses := [] }

theorem u23497 : Upper (D 8) (R 8) [320,12,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23498_3 : Upper (D 8) (R 8) [320,12,80,160,3] 13 :=
  permutation_upper _ _ _ [320,5,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17870

def r23498 : Route 9 := (fun mask => (mask,id))

def c23498 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23498 : Upper (D 8) (R 8) [320,12,80,160] 13 := by
  apply FastRouting.sound _ _ [320,12,80,160] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23498 c23498
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23498_3
  · exact u18426
  · exact u18427
  · exact u18428
  · exact u18429
  · exact u18430

theorem m23499_3 : Upper (D 8) (R 8) [320,12,96,129,3] 13 :=
  permutation_upper _ _ _ [320,5,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17871

def r23499 : Route 9 := (fun mask => (mask,id))

def c23499 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23499 : Upper (D 8) (R 8) [320,12,96,129] 13 := by
  apply FastRouting.sound _ _ [320,12,96,129] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23499 c23499
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23499_3
  · exact u18431
  · exact u18432
  · exact u18433
  · exact u18434
  · exact u18435

def b23500 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 100 138 177 177 241 177 433), lower := (rows 321 14 100 138 16 32 64 128 256), losses := [] }

theorem u23500 : Upper (D 8) (R 8) [320,12,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23501_3 : Upper (D 8) (R 8) [320,12,96,144,3] 13 :=
  permutation_upper _ _ _ [320,5,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17872

def r23501 : Route 9 := (fun mask => (mask,id))

def c23501 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23501 : Upper (D 8) (R 8) [320,12,96,144] 13 := by
  apply FastRouting.sound _ _ [320,12,96,144] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23501 c23501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23501_3
  · exact u18439
  · exact u18440
  · exact u18441
  · exact u18442
  · exact u18443

theorem m23502_3 : Upper (D 8) (R 8) [320,12,96,160,3] 13 :=
  permutation_upper _ _ _ [320,5,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17873

def r23502 : Route 9 := (fun mask => (mask,id))

def c23502 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23502 : Upper (D 8) (R 8) [320,12,96,160] 13 := by
  apply FastRouting.sound _ _ [320,12,96,160] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23502 c23502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23502_3
  · exact u18444
  · exact u18445
  · exact u18446
  · exact u18447
  · exact u18448

def b23503 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 321 14 133 137 114 114 114 242 370), lower := (rows 321 14 133 137 16 32 64 128 256), losses := [] }

theorem u23503 : Upper (D 8) (R 8) [320,12,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23504 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 133 138 113 113 113 241 369), lower := (rows 321 14 133 138 16 32 64 128 256), losses := [] }

theorem u23504 : Upper (D 8) (R 8) [320,12,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23505 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 152 115 99 99 227 355), lower := (rows 321 14 133 152 16 32 64 128 256), losses := [] }

theorem u23505 : Upper (D 8) (R 8) [320,12,129,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23506 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 168 115 115 115 243 371), lower := (rows 321 14 133 168 16 32 64 128 256), losses := [] }

theorem u23506 : Upper (D 8) (R 8) [320,12,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23507 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 133 200 51 51 115 179 307), lower := (rows 321 14 133 200 16 32 64 128 256), losses := [] }

theorem u23507 : Upper (D 8) (R 8) [320,12,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23508 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 134 152 113 97 97 225 353), lower := (rows 321 14 134 152 16 32 64 128 256), losses := [] }

theorem u23508 : Upper (D 8) (R 8) [320,12,130,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23509 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 134 168 113 113 113 241 369), lower := (rows 321 14 134 168 16 32 64 128 256), losses := [] }

theorem u23509 : Upper (D 8) (R 8) [320,12,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23510 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 134 200 49 49 113 177 305), lower := (rows 321 14 134 200 16 32 64 128 256), losses := [] }

theorem u23510 : Upper (D 8) (R 8) [320,12,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23511 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 148 168 115 99 99 227 355), lower := (rows 321 14 148 168 16 32 64 128 256), losses := [] }

theorem u23511 : Upper (D 8) (R 8) [320,12,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23512 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 148 200 51 35 99 163 291), lower := (rows 321 14 148 200 16 32 64 128 256), losses := [] }

theorem u23512 : Upper (D 8) (R 8) [320,12,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23513 : PairBound 9 := { available := 115, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 164 168 115 115 115 243 371), lower := (rows 321 14 164 168 16 32 64 128 256), losses := [] }

theorem u23513 : Upper (D 8) (R 8) [320,12,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23514 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 164 200 51 51 115 179 307), lower := (rows 321 14 164 200 16 32 64 128 256), losses := [] }

theorem u23514 : Upper (D 8) (R 8) [320,12,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23515_12 : Upper (D 8) (R 8) [320,17,33,34,12] 13 :=
  permutation_upper _ _ _ [320,5,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17856

theorem m23515_36 : Upper (D 8) (R 8) [320,17,33,34,36] 13 :=
  permutation_upper _ _ _ [320,5,40,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17953

theorem m23515_40 : Upper (D 8) (R 8) [320,17,33,34,40] 13 :=
  permutation_upper _ _ _ [320,5,40,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17959

theorem m23515_68 : Upper (D 8) (R 8) [320,17,33,34,68] 13 :=
  permutation_upper _ _ _ [320,5,72,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18042

theorem m23515_72 : Upper (D 8) (R 8) [320,17,33,34,72] 13 :=
  permutation_upper _ _ _ [320,5,72,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18045

theorem m23515_96 : Upper (D 8) (R 8) [320,17,33,34,96] 13 :=
  permutation_upper _ _ _ [320,5,96,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18070

theorem m23515_132 : Upper (D 8) (R 8) [320,17,33,34,132] 13 :=
  permutation_upper _ _ _ [320,5,136,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18133

theorem m23515_136 : Upper (D 8) (R 8) [320,17,33,34,136] 13 :=
  permutation_upper _ _ _ [320,5,136,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18139

theorem m23515_160 : Upper (D 8) (R 8) [320,17,33,34,160] 13 :=
  permutation_upper _ _ _ [320,5,160,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18195

theorem m23515_192 : Upper (D 8) (R 8) [320,17,33,34,192] 13 :=
  permutation_upper _ _ _ [320,5,192,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18239

def r23515 : Route 9 := (fun mask => (mask,id))

def c23515 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23515 : Upper (D 8) (R 8) [320,17,33,34] 13 := by
  apply FastRouting.sound _ _ [320,17,33,34] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r23515 c23515
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23515_12
  · exact m23515_36
  · exact m23515_40
  · exact m23515_68
  · exact m23515_72
  · exact m23515_96
  · exact m23515_132
  · exact m23515_136
  · exact m23515_160
  · exact m23515_192

theorem m23516_12 : Upper (D 8) (R 8) [320,17,33,66,12] 13 :=
  permutation_upper _ _ _ [320,5,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17857

theorem m23516_36 : Upper (D 8) (R 8) [320,17,33,66,36] 13 :=
  permutation_upper _ _ _ [320,5,40,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17954

theorem m23516_40 : Upper (D 8) (R 8) [320,17,33,66,40] 13 :=
  permutation_upper _ _ _ [320,5,40,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17975

theorem m23516_132 : Upper (D 8) (R 8) [320,17,33,66,132] 13 :=
  permutation_upper _ _ _ [320,5,136,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18134

theorem m23516_136 : Upper (D 8) (R 8) [320,17,33,66,136] 13 :=
  permutation_upper _ _ _ [320,5,136,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18156

theorem m23516_160 : Upper (D 8) (R 8) [320,17,33,66,160] 13 :=
  permutation_upper _ _ _ [320,5,160,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18197

def r23516 : Route 9 := (fun mask => (mask,id))

def c23516 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23516 : Upper (D 8) (R 8) [320,17,33,66] 13 := by
  apply FastRouting.sound _ _ [320,17,33,66] 13 (by decide) (choices 2) [12,36,40,132,136,160] r23516 c23516
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23516_12
  · exact m23516_36
  · exact m23516_40
  · exact m23516_132
  · exact m23516_136
  · exact m23516_160

theorem m23517_10 : Upper (D 8) (R 8) [320,17,33,68,10] 13 :=
  permutation_upper _ _ _ [320,5,10,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17832

theorem m23517_34 : Upper (D 8) (R 8) [320,17,33,68,34] 13 :=
  permutation_upper _ _ _ [320,5,34,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17912

theorem m23517_40 : Upper (D 8) (R 8) [320,17,33,68,40] 13 :=
  permutation_upper _ _ _ [320,5,40,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17978

theorem m23517_130 : Upper (D 8) (R 8) [320,17,33,68,130] 13 :=
  permutation_upper _ _ _ [320,5,130,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18106

theorem m23517_136 : Upper (D 8) (R 8) [320,17,33,68,136] 13 :=
  permutation_upper _ _ _ [320,5,136,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18159

theorem m23517_160 : Upper (D 8) (R 8) [320,17,33,68,160] 13 :=
  permutation_upper _ _ _ [320,5,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18198

def r23517 : Route 9 := (fun mask => (mask,id))

def c23517 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23517 : Upper (D 8) (R 8) [320,17,33,68] 13 := by
  apply FastRouting.sound _ _ [320,17,33,68] 13 (by decide) (choices 2) [10,34,40,130,136,160] r23517 c23517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23517_10
  · exact m23517_34
  · exact m23517_40
  · exact m23517_130
  · exact m23517_136
  · exact m23517_160

theorem m23518_6 : Upper (D 8) (R 8) [320,17,33,96,6] 13 :=
  permutation_upper _ _ _ [320,5,10,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17822

theorem m23518_10 : Upper (D 8) (R 8) [320,17,33,96,10] 13 :=
  permutation_upper _ _ _ [320,5,10,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17835

theorem m23518_12 : Upper (D 8) (R 8) [320,17,33,96,12] 13 :=
  permutation_upper _ _ _ [320,5,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17858

theorem m23518_34 : Upper (D 8) (R 8) [320,17,33,96,34] 13 :=
  permutation_upper _ _ _ [320,5,34,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17913

theorem m23518_36 : Upper (D 8) (R 8) [320,17,33,96,36] 13 :=
  permutation_upper _ _ _ [320,5,40,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17955

theorem m23518_40 : Upper (D 8) (R 8) [320,17,33,96,40] 13 :=
  permutation_upper _ _ _ [320,5,40,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17983

theorem m23518_130 : Upper (D 8) (R 8) [320,17,33,96,130] 13 :=
  permutation_upper _ _ _ [320,5,130,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18107

theorem m23518_132 : Upper (D 8) (R 8) [320,17,33,96,132] 13 :=
  permutation_upper _ _ _ [320,5,136,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18135

theorem m23518_136 : Upper (D 8) (R 8) [320,17,33,96,136] 13 :=
  permutation_upper _ _ _ [320,5,136,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18164

theorem m23518_160 : Upper (D 8) (R 8) [320,17,33,96,160] 13 :=
  permutation_upper _ _ _ [320,5,160,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18199

def r23518 : Route 9 := (fun mask => (mask,id))

def c23518 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23518 : Upper (D 8) (R 8) [320,17,33,96] 13 := by
  apply FastRouting.sound _ _ [320,17,33,96] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160] r23518 c23518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23518_6
  · exact m23518_10
  · exact m23518_12
  · exact m23518_34
  · exact m23518_36
  · exact m23518_40
  · exact m23518_130
  · exact m23518_132
  · exact m23518_136
  · exact m23518_160

theorem m23519_12 : Upper (D 8) (R 8) [320,17,33,130,12] 13 :=
  permutation_upper _ _ _ [320,5,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17859

theorem m23519_36 : Upper (D 8) (R 8) [320,17,33,130,36] 13 :=
  permutation_upper _ _ _ [320,5,40,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17956

theorem m23519_40 : Upper (D 8) (R 8) [320,17,33,130,40] 13 :=
  permutation_upper _ _ _ [320,5,40,130,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17994

theorem m23519_68 : Upper (D 8) (R 8) [320,17,33,130,68] 13 :=
  permutation_upper _ _ _ [320,5,72,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18043

theorem m23519_72 : Upper (D 8) (R 8) [320,17,33,130,72] 13 :=
  permutation_upper _ _ _ [320,5,72,130,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18053

theorem m23519_96 : Upper (D 8) (R 8) [320,17,33,130,96] 13 :=
  permutation_upper _ _ _ [320,5,96,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18071

theorem m23519_132 : Upper (D 8) (R 8) [320,17,33,130,132] 13 :=
  permutation_upper _ _ _ [320,5,136,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18136

theorem m23519_136 : Upper (D 8) (R 8) [320,17,33,130,136] 13 :=
  permutation_upper _ _ _ [320,5,136,130,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18172

theorem m23519_160 : Upper (D 8) (R 8) [320,17,33,130,160] 13 :=
  permutation_upper _ _ _ [320,5,160,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18200

theorem m23519_192 : Upper (D 8) (R 8) [320,17,33,130,192] 13 :=
  permutation_upper _ _ _ [320,5,192,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18240

def r23519 : Route 9 := (fun mask => (mask,id))

def c23519 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23519 : Upper (D 8) (R 8) [320,17,33,130] 13 := by
  apply FastRouting.sound _ _ [320,17,33,130] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r23519 c23519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23519_12
  · exact m23519_36
  · exact m23519_40
  · exact m23519_68
  · exact m23519_72
  · exact m23519_96
  · exact m23519_132
  · exact m23519_136
  · exact m23519_160
  · exact m23519_192

#print axioms u23519
end Delivery.IrregularNine14.P08
