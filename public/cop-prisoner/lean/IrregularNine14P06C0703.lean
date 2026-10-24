import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0572
import IrregularNine14P06C0573
import IrregularNine14P06C0574
import IrregularNine14P06C0575
import IrregularNine14P06C0576

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b42180 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 292 74 85 117 85 213 341), lower := (rows 11 162 292 74 16 32 64 128 256), losses := [] }

theorem u42180 : Upper (D 6) (R 6) [10,160,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42181 : Route 9 := (fun mask => (mask,id))

def c42181 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42181 : Upper (D 6) (R 6) [10,160,288,68] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42181 c42181
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34356
  · exact u34357
  · exact u34358
  · exact u34359
  · exact u34360
  · exact u34361

def r42182 : Route 9 := (fun mask => (mask,id))

def c42182 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42182 : Upper (D 6) (R 6) [10,160,288,80] 13 := by
  apply FastRouting.sound _ _ [10,160,288,80] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42182 c42182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34362
  · exact u34363
  · exact u34364
  · exact u34365
  · exact u34366
  · exact u34367

def b42183 : PairBound 9 := { available := 117, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 324 11 117 117 117 245 373), lower := (rows 11 162 324 11 16 32 64 128 256), losses := [] }

theorem u42183 : Upper (D 6) (R 6) [10,160,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42184 : Route 9 := (fun mask => (mask,id))

def c42184 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42184 : Upper (D 6) (R 6) [10,160,320,5] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42184 c42184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34368
  · exact u34369
  · exact u34370
  · exact u34371
  · exact u34372
  · exact u34373
  · exact u34374
  · exact u34375
  · exact u34376
  · exact u34377

def b42185 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 324 14 117 117 117 245 373), lower := (rows 11 162 324 14 16 32 64 128 256), losses := [] }

theorem u42185 : Upper (D 6) (R 6) [10,160,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42186 : Route 9 := (fun mask => (mask,id))

def c42186 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42186 : Upper (D 6) (R 6) [10,160,320,17] 13 := by
  apply FastRouting.sound _ _ [10,160,320,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42186 c42186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34378
  · exact u34379
  · exact u34380
  · exact u34381
  · exact u34382
  · exact u34383
  · exact u34384
  · exact u34385
  · exact u34386
  · exact u34387

def b42187 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 324 26 117 101 101 229 357), lower := (rows 11 162 324 26 16 32 64 128 256), losses := [] }

theorem u42187 : Upper (D 6) (R 6) [10,160,320,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42188 : Route 9 := (fun mask => (mask,id))

def c42188 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42188 : Upper (D 6) (R 6) [10,160,320,20] 13 := by
  apply FastRouting.sound _ _ [10,160,320,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42188 c42188
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34388
  · exact u34389
  · exact u34390
  · exact u34391
  · exact u34392
  · exact u34393
  · exact u34394
  · exact u34395
  · exact u34396
  · exact u34397

def b42189 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 324 41 87 119 87 215 343), lower := (rows 11 162 324 41 16 32 64 128 256), losses := [] }

theorem u42189 : Upper (D 6) (R 6) [10,160,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42190 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 324 42 85 117 85 213 341), lower := (rows 11 162 324 42 16 32 64 128 256), losses := [] }

theorem u42190 : Upper (D 6) (R 6) [10,160,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42191 : Route 9 := (fun mask => (mask,id))

def c42191 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42191 : Upper (D 6) (R 6) [10,160,320,36] 13 := by
  apply FastRouting.sound _ _ [10,160,320,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42191 c42191
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34398
  · exact u34399
  · exact u34400
  · exact u34401
  · exact u34402
  · exact u34403

def r42192 : Route 9 := (fun mask => (mask,id))

def c42192 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42192 : Upper (D 6) (R 6) [10,160,320,48] 13 := by
  apply FastRouting.sound _ _ [10,160,320,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42192 c42192
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34404
  · exact u34405
  · exact u34406
  · exact u34407
  · exact u34408
  · exact u34409

def r42193 : Route 9 := (fun mask => (mask,id))

def c42193 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42193 : Upper (D 6) (R 6) [10,160,320,65] 13 := by
  apply FastRouting.sound _ _ [10,160,320,65] 13 (by decide) (choices 2) [3,5,6,33,34,36] r42193 c42193
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34410
  · exact u34411
  · exact u34412
  · exact u34413
  · exact u34414
  · exact u34415

def b42194 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 324 74 53 53 117 181 309), lower := (rows 11 162 324 74 16 32 64 128 256), losses := [] }

theorem u42194 : Upper (D 6) (R 6) [10,160,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42195 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 324 76 55 55 119 183 311), lower := (rows 11 162 324 76 16 32 64 128 256), losses := [] }

theorem u42195 : Upper (D 6) (R 6) [10,160,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42196 : Route 9 := (fun mask => (mask,id))

def c42196 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42196 : Upper (D 6) (R 6) [10,160,320,80] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80] 13 (by decide) (choices 2) [3,5,6,33,34,36] r42196 c42196
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34416
  · exact u34417
  · exact u34418
  · exact u34419
  · exact u34420
  · exact u34421

def r42197 : Route 9 := (fun mask => (mask,id))

def c42197 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42197 : Upper (D 6) (R 6) [10,160,320,96] 13 := by
  apply FastRouting.sound _ _ [10,160,320,96] 13 (by decide) (choices 2) [3,5,6] r42197 c42197
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34422
  · exact u34423
  · exact u34424

def b42198 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 22 13 117 101 101 229 357), lower := (rows 11 386 22 13 16 32 64 128 256), losses := [] }

theorem u42198 : Upper (D 6) (R 6) [10,384,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42199_5 : Upper (D 6) (R 6) [10,384,18,33,5] 13 :=
  permutation_upper _ _ _ [10,384,18,5,36] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34426

def r42199 : Route 9 := (fun mask => (mask,id))

def c42199 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42199 : Upper (D 6) (R 6) [10,384,18,33] 13 := by
  apply FastRouting.sound _ _ [10,384,18,33] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42199 c42199
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42199_5
  · exact u34428
  · exact u34429
  · exact u34430
  · exact u34431
  · exact u34432

theorem m42200_5 : Upper (D 6) (R 6) [10,384,18,36,5] 13 :=
  permutation_upper _ _ _ [10,384,18,5,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34425

theorem m42200_36 : Upper (D 6) (R 6) [10,384,18,36,36] 13 :=
  permutation_upper _ _ _ [10,384,18,33,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34428

theorem m42200_68 : Upper (D 6) (R 6) [10,384,18,36,68] 13 :=
  permutation_upper _ _ _ [10,384,18,33,65] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34430

def r42200 : Route 9 := (fun mask => (mask,id))

def c42200 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42200 : Upper (D 6) (R 6) [10,384,18,36] 13 := by
  apply FastRouting.sound _ _ [10,384,18,36] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42200 c42200
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42200_5
  · exact u34433
  · exact m42200_36
  · exact u34434
  · exact m42200_68
  · exact u34435

theorem m42201_5 : Upper (D 6) (R 6) [10,384,18,96,5] 13 :=
  permutation_upper _ _ _ [10,384,18,5,96] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34427

theorem m42201_33 : Upper (D 6) (R 6) [10,384,18,96,33] 13 :=
  permutation_upper _ _ _ [10,384,18,36,96] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34435

theorem m42201_36 : Upper (D 6) (R 6) [10,384,18,96,36] 13 :=
  permutation_upper _ _ _ [10,384,18,33,96] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34432

def r42201 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42201 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42201 : Upper (D 6) (R 6) [10,384,18,96] 13 := by
  apply FastRouting.sound _ _ [10,384,18,96] 13 (by decide) (choices 2) [5,33,36,96] r42201 c42201
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m42201_5
  · exact m42201_33
  · exact m42201_36
  · exact u34436

def b42202 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 37 11 116 116 116 244 372), lower := (rows 11 386 37 11 16 32 64 128 256), losses := [] }

theorem u42202 : Upper (D 6) (R 6) [10,384,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42203 : PairBound 9 := { available := 118, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 386 37 13 118 118 118 246 374), lower := (rows 11 386 37 13 16 32 64 128 256), losses := [] }

theorem u42203 : Upper (D 6) (R 6) [10,384,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42204 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 37 14 117 117 117 245 373), lower := (rows 11 386 37 14 16 32 64 128 256), losses := [] }

theorem u42204 : Upper (D 6) (R 6) [10,384,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42205 : Route 9 := (fun mask => (mask,id))

def c42205 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42205 : Upper (D 6) (R 6) [10,384,33,17] 13 := by
  apply FastRouting.sound _ _ [10,384,33,17] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42205 c42205
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34437
  · exact u34438
  · exact u34439
  · exact u34440
  · exact u34441
  · exact u34442

def b42206 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 37 26 117 101 101 229 357), lower := (rows 11 386 37 26 16 32 64 128 256), losses := [] }

theorem u42206 : Upper (D 6) (R 6) [10,384,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42207 : Route 9 := (fun mask => (mask,id))

def c42207 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42207 : Upper (D 6) (R 6) [10,384,33,20] 13 := by
  apply FastRouting.sound _ _ [10,384,33,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42207 c42207
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34443
  · exact u34444
  · exact u34445
  · exact u34446
  · exact u34447
  · exact u34448
  · exact u34449
  · exact u34450
  · exact u34451
  · exact u34452

def b42208 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 8, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 386 37 41 86 118 86 214 342), lower := (rows 11 386 37 41 16 32 64 128 256), losses := [] }

theorem u42208 : Upper (D 6) (R 6) [10,384,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42209 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 386 37 42 85 117 85 213 341), lower := (rows 11 386 37 42 16 32 64 128 256), losses := [] }

theorem u42209 : Upper (D 6) (R 6) [10,384,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42210 : PairBound 9 := { available := 87, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 386 37 44 87 119 87 215 343), lower := (rows 11 386 37 44 16 32 64 128 256), losses := [] }

theorem u42210 : Upper (D 6) (R 6) [10,384,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42211 : Route 9 := (fun mask => (mask,id))

def c42211 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42211 : Upper (D 6) (R 6) [10,384,33,48] 13 := by
  apply FastRouting.sound _ _ [10,384,33,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42211 c42211
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34453
  · exact u34454
  · exact u34455
  · exact u34456
  · exact u34457
  · exact u34458

def r42212 : Route 9 := (fun mask => (mask,id))

def c42212 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42212 : Upper (D 6) (R 6) [10,384,33,65] 13 := by
  apply FastRouting.sound _ _ [10,384,33,65] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42212 c42212
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34459
  · exact u34460
  · exact u34461
  · exact u34462
  · exact u34463
  · exact u34464

def b42213 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 37 74 117 117 117 245 373), lower := (rows 11 386 37 74 16 32 64 128 256), losses := [] }

theorem u42213 : Upper (D 6) (R 6) [10,384,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42214 : Route 9 := (fun mask => (mask,id))

def c42214 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42214 : Upper (D 6) (R 6) [10,384,33,68] 13 := by
  apply FastRouting.sound _ _ [10,384,33,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42214 c42214
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34465
  · exact u34466
  · exact u34467
  · exact u34468
  · exact u34469
  · exact u34470
  · exact u34471
  · exact u34472
  · exact u34473
  · exact u34474

def r42215 : Route 9 := (fun mask => (mask,id))

def c42215 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42215 : Upper (D 6) (R 6) [10,384,33,80] 13 := by
  apply FastRouting.sound _ _ [10,384,33,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42215 c42215
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34475
  · exact u34476
  · exact u34477
  · exact u34478
  · exact u34479
  · exact u34480
  · exact u34481
  · exact u34482
  · exact u34483
  · exact u34484

def r42216 : Route 9 := (fun mask => (mask,id))

def c42216 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42216 : Upper (D 6) (R 6) [10,384,33,96] 13 := by
  apply FastRouting.sound _ _ [10,384,33,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42216 c42216
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34485
  · exact u34486
  · exact u34487
  · exact u34488
  · exact u34489
  · exact u34490

def b42217 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 38 13 117 117 117 245 373), lower := (rows 11 386 38 13 16 32 64 128 256), losses := [] }

theorem u42217 : Upper (D 6) (R 6) [10,384,34,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42218 : Route 9 := (fun mask => (mask,id))

def c42218 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42218 : Upper (D 6) (R 6) [10,384,34,17] 13 := by
  apply FastRouting.sound _ _ [10,384,34,17] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42218 c42218
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34491
  · exact u34492
  · exact u34493
  · exact u34494
  · exact u34495
  · exact u34496

def r42219 : Route 9 := (fun mask => (mask,id))

def c42219 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42219 : Upper (D 6) (R 6) [10,384,34,20] 13 := by
  apply FastRouting.sound _ _ [10,384,34,20] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42219 c42219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34497
  · exact u34498
  · exact u34499
  · exact u34500
  · exact u34501
  · exact u34502

def b42220 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 9, targets := 4 },{ cop := 2, region := 9, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 38 41 85 117 85 213 341), lower := (rows 11 386 38 41 16 32 64 128 256), losses := [] }

theorem u42220 : Upper (D 6) (R 6) [10,384,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42221 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 386 38 44 85 117 85 213 341), lower := (rows 11 386 38 44 16 32 64 128 256), losses := [] }

theorem u42221 : Upper (D 6) (R 6) [10,384,34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42222 : Route 9 := (fun mask => (mask,id))

def c42222 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42222 : Upper (D 6) (R 6) [10,384,34,48] 13 := by
  apply FastRouting.sound _ _ [10,384,34,48] 13 (by decide) (choices 2) [5,65,68] r42222 c42222
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34503
  · exact u34504
  · exact u34505

def r42223 : Route 9 := (fun mask => (mask,id))

def c42223 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42223 : Upper (D 6) (R 6) [10,384,34,65] 13 := by
  apply FastRouting.sound _ _ [10,384,34,65] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42223 c42223
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34506
  · exact u34507
  · exact u34508
  · exact u34509
  · exact u34510
  · exact u34511

def r42224 : Route 9 := (fun mask => (mask,id))

def c42224 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42224 : Upper (D 6) (R 6) [10,384,34,68] 13 := by
  apply FastRouting.sound _ _ [10,384,34,68] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42224 c42224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34512
  · exact u34513
  · exact u34514
  · exact u34515
  · exact u34516
  · exact u34517

def r42225 : Route 9 := (fun mask => (mask,id))

def c42225 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42225 : Upper (D 6) (R 6) [10,384,34,80] 13 := by
  apply FastRouting.sound _ _ [10,384,34,80] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42225 c42225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34518
  · exact u34519
  · exact u34520
  · exact u34521
  · exact u34522
  · exact u34523

def r42226 : Route 9 := (fun mask => (mask,id))

def c42226 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42226 : Upper (D 6) (R 6) [10,384,34,96] 13 := by
  apply FastRouting.sound _ _ [10,384,34,96] 13 (by decide) (choices 2) [5,65,68] r42226 c42226
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34524
  · exact u34525
  · exact u34526

def b42227 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 52 11 117 101 101 229 357), lower := (rows 11 386 52 11 16 32 64 128 256), losses := [] }

theorem u42227 : Upper (D 6) (R 6) [10,384,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42228 : Route 9 := (fun mask => (mask,id))

def c42228 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42228 : Upper (D 6) (R 6) [10,384,48,5] 13 := by
  apply FastRouting.sound _ _ [10,384,48,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42228 c42228
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34527
  · exact u34528
  · exact u34529
  · exact u34530
  · exact u34531
  · exact u34532
  · exact u34533
  · exact u34534
  · exact u34535
  · exact u34536

def b42229 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 52 14 117 101 101 229 357), lower := (rows 11 386 52 14 16 32 64 128 256), losses := [] }

theorem u42229 : Upper (D 6) (R 6) [10,384,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42230 : Route 9 := (fun mask => (mask,id))

def c42230 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42230 : Upper (D 6) (R 6) [10,384,48,33] 13 := by
  apply FastRouting.sound _ _ [10,384,48,33] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42230 c42230
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34537
  · exact u34538
  · exact u34539
  · exact u34540
  · exact u34541
  · exact u34542

def b42231 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 52 42 85 101 69 197 325), lower := (rows 11 386 52 42 16 32 64 128 256), losses := [] }

theorem u42231 : Upper (D 6) (R 6) [10,384,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42232 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 386 52 44 87 103 71 199 327), lower := (rows 11 386 52 44 16 32 64 128 256), losses := [] }

theorem u42232 : Upper (D 6) (R 6) [10,384,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42233 : Route 9 := (fun mask => (mask,id))

def c42233 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42233 : Upper (D 6) (R 6) [10,384,48,65] 13 := by
  apply FastRouting.sound _ _ [10,384,48,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42233 c42233
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34543
  · exact u34544
  · exact u34545
  · exact u34546
  · exact u34547
  · exact u34548
  · exact u34549
  · exact u34550
  · exact u34551
  · exact u34552

def b42234 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 52 74 117 101 101 229 357), lower := (rows 11 386 52 74 16 32 64 128 256), losses := [] }

theorem u42234 : Upper (D 6) (R 6) [10,384,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42235 : Route 9 := (fun mask => (mask,id))

def c42235 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42235 : Upper (D 6) (R 6) [10,384,48,68] 13 := by
  apply FastRouting.sound _ _ [10,384,48,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42235 c42235
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34553
  · exact u34554
  · exact u34555
  · exact u34556
  · exact u34557
  · exact u34558
  · exact u34559
  · exact u34560
  · exact u34561
  · exact u34562

def r42236 : Route 9 := (fun mask => (mask,id))

def c42236 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42236 : Upper (D 6) (R 6) [10,384,48,96] 13 := by
  apply FastRouting.sound _ _ [10,384,48,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42236 c42236
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34563
  · exact u34564
  · exact u34565
  · exact u34566
  · exact u34567
  · exact u34568

def b42237 : PairBound 9 := { available := 117, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 100 11 117 117 117 245 373), lower := (rows 11 386 100 11 16 32 64 128 256), losses := [] }

theorem u42237 : Upper (D 6) (R 6) [10,384,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42238 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42238 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42238 : Upper (D 6) (R 6) [10,384,96,5] 13 := by
  apply FastRouting.sound _ _ [10,384,96,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r42238 c42238
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34569
  · exact u34570
  · exact u34571
  · exact u34572
  · exact u34573
  · exact u34574
  · exact u34575

def b42239 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 100 14 117 117 117 245 373), lower := (rows 11 386 100 14 16 32 64 128 256), losses := [] }

theorem u42239 : Upper (D 6) (R 6) [10,384,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u42239
end Delivery.IrregularNine14.P06
