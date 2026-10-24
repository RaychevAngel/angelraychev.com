import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0454
import IrregularNine14P06C0455
import IrregularNine14P06C0456

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40320 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 131 268 25 112 38 70 134 262), lower := (rows 97 131 268 25 112 32 64 128 256), losses := [] }

theorem u40320 : Upper (D 6) (R 6) [96,129,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40321 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 268 26 19 100 100 228 356), lower := (rows 97 131 268 26 19 32 64 128 256), losses := [] }

theorem u40321 : Upper (D 6) (R 6) [96,129,264,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40322 : Route 9 := (fun mask => (mask,id))

def c40322 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40322 : Upper (D 6) (R 6) [96,129,264,18,5] 13 := by
  apply FastRouting.sound _ _ [96,129,264,18,5] 13 (by decide) (choices 1) [2,4,64] r40322 c40322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27273
  · exact u27274
  · exact u27275

def b40323 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 131 268 26 22 101 101 229 357), lower := (rows 97 131 268 26 22 32 64 128 256), losses := [] }

theorem u40323 : Upper (D 6) (R 6) [96,129,264,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40324 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 131 268 26 49 102 70 198 326), lower := (rows 97 131 268 26 49 32 64 128 256), losses := [] }

theorem u40324 : Upper (D 6) (R 6) [96,129,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40325 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 131 268 26 50 101 69 197 325), lower := (rows 97 131 268 26 50 32 64 128 256), losses := [] }

theorem u40325 : Upper (D 6) (R 6) [96,129,264,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40326 : Route 9 := (fun mask => (mask,id))

def c40326 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40326 : Upper (D 6) (R 6) [96,129,264,18,36] 13 := by
  apply FastRouting.sound _ _ [96,129,264,18,36] 13 (by decide) (choices 1) [1,2,4,64] r40326 c40326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27276
  · exact u27277
  · exact u27278
  · exact u27279

def b40327 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 268 26 112 39 71 135 263), lower := (rows 97 131 268 26 112 32 64 128 256), losses := [] }

theorem u40327 : Upper (D 6) (R 6) [96,129,264,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40328 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 131 268 28 19 102 102 230 358), lower := (rows 97 131 268 28 19 32 64 128 256), losses := [] }

theorem u40328 : Upper (D 6) (R 6) [96,129,264,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40329 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 131 268 28 21 98 98 226 354), lower := (rows 97 131 268 28 21 32 64 128 256), losses := [] }

theorem u40329 : Upper (D 6) (R 6) [96,129,264,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40330 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 131 268 28 22 99 99 227 355), lower := (rows 97 131 268 28 22 32 64 128 256), losses := [] }

theorem u40330 : Upper (D 6) (R 6) [96,129,264,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40331 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 131 268 28 49 102 70 198 326), lower := (rows 97 131 268 28 49 32 64 128 256), losses := [] }

theorem u40331 : Upper (D 6) (R 6) [96,129,264,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40332 : Route 9 := (fun mask => (mask,id))

def c40332 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40332 : Upper (D 6) (R 6) [96,129,264,20,34] 13 := by
  apply FastRouting.sound _ _ [96,129,264,20,34] 13 (by decide) (choices 1) [1,2,4,64] r40332 c40332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27280
  · exact u27281
  · exact u27282
  · exact u27283

def b40333 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 131 268 28 52 99 67 195 323), lower := (rows 97 131 268 28 52 32 64 128 256), losses := [] }

theorem u40333 : Upper (D 6) (R 6) [96,129,264,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40334 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 268 28 112 39 71 135 263), lower := (rows 97 131 268 28 112 32 64 128 256), losses := [] }

theorem u40334 : Upper (D 6) (R 6) [96,129,264,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40335 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 131 268 42 19 116 84 212 340), lower := (rows 97 131 268 42 19 32 64 128 256), losses := [] }

theorem u40335 : Upper (D 6) (R 6) [96,129,264,34,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40336 : Route 9 := (fun mask => (mask,id))

def c40336 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40336 : Upper (D 6) (R 6) [96,129,264,34,5] 13 := by
  apply FastRouting.sound _ _ [96,129,264,34,5] 13 (by decide) (choices 1) [2,4,16,64] r40336 c40336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27284
  · exact u27285
  · exact u27286
  · exact u27287

def r40337 : Route 9 := (fun mask => (mask,id))

def c40337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40337 : Upper (D 6) (R 6) [96,129,264,34,6] 13 := by
  apply FastRouting.sound _ _ [96,129,264,34,6] 13 (by decide) (choices 1) [1,4,16,64] r40337 c40337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27288
  · exact u27289
  · exact u27290
  · exact u27291

def b40338 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 131 268 42 81 54 86 150 278), lower := (rows 97 131 268 42 81 32 64 128 256), losses := [] }

theorem u40338 : Upper (D 6) (R 6) [96,129,264,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40339 : Route 9 := (fun mask => (mask,id))

def c40339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40339 : Upper (D 6) (R 6) [96,129,264,34,66] 13 := by
  apply FastRouting.sound _ _ [96,129,264,34,66] 13 (by decide) (choices 1) [1,4,16] r40339 c40339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27292
  · exact u27293
  · exact u27294

def r40340 : Route 9 := (fun mask => (mask,id))

def c40340 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40340 : Upper (D 6) (R 6) [96,129,264,34,68] 13 := by
  apply FastRouting.sound _ _ [96,129,264,34,68] 13 (by decide) (choices 1) [1,2,4,16] r40340 c40340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27295
  · exact u27296
  · exact u27297
  · exact u27298

def b40341 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 131 268 44 19 118 86 214 342), lower := (rows 97 131 268 44 19 32 64 128 256), losses := [] }

theorem u40341 : Upper (D 6) (R 6) [96,129,264,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40342 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 227, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 97 131 268 44 21 114 82 210 338), lower := (rows 97 131 268 44 21 32 64 128 256), losses := [] }

theorem u40342 : Upper (D 6) (R 6) [96,129,264,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40343 : Route 9 := (fun mask => (mask,id))

def c40343 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40343 : Upper (D 6) (R 6) [96,129,264,36,6] 13 := by
  apply FastRouting.sound _ _ [96,129,264,36,6] 13 (by decide) (choices 1) [1,2,16,64] r40343 c40343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27299
  · exact u27300
  · exact u27301
  · exact u27302

def b40344 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 131 268 44 81 54 86 150 278), lower := (rows 97 131 268 44 81 32 64 128 256), losses := [] }

theorem u40344 : Upper (D 6) (R 6) [96,129,264,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40345 : Route 9 := (fun mask => (mask,id))

def c40345 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40345 : Upper (D 6) (R 6) [96,129,264,36,66] 13 := by
  apply FastRouting.sound _ _ [96,129,264,36,66] 13 (by decide) (choices 1) [1,2,4,16] r40345 c40345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27303
  · exact u27304
  · exact u27305
  · exact u27306

def r40346 : Route 9 := (fun mask => (mask,id))

def c40346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40346 : Upper (D 6) (R 6) [96,129,264,36,68] 13 := by
  apply FastRouting.sound _ _ [96,129,264,36,68] 13 (by decide) (choices 1) [1,2,16] r40346 c40346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27307
  · exact u27308
  · exact u27309

def b40347 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 131 268 56 19 102 70 198 326), lower := (rows 97 131 268 56 19 32 64 128 256), losses := [] }

theorem u40347 : Upper (D 6) (R 6) [96,129,264,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40348 : Route 9 := (fun mask => (mask,id))

def c40348 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40348 : Upper (D 6) (R 6) [96,129,264,48,5] 13 := by
  apply FastRouting.sound _ _ [96,129,264,48,5] 13 (by decide) (choices 1) [2,4,64] r40348 c40348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27310
  · exact u27311
  · exact u27312

def r40349 : Route 9 := (fun mask => (mask,id))

def c40349 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40349 : Upper (D 6) (R 6) [96,129,264,48,6] 13 := by
  apply FastRouting.sound _ _ [96,129,264,48,6] 13 (by decide) (choices 1) [1,2,4,64] r40349 c40349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27313
  · exact u27314
  · exact u27315
  · exact u27316

def b40350 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 131 268 56 81 38 70 134 262), lower := (rows 97 131 268 56 81 32 64 128 256), losses := [] }

theorem u40350 : Upper (D 6) (R 6) [96,129,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40351 : Route 9 := (fun mask => (mask,id))

def c40351 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40351 : Upper (D 6) (R 6) [96,129,264,48,66] 13 := by
  apply FastRouting.sound _ _ [96,129,264,48,66] 13 (by decide) (choices 1) [1,2,4] r40351 c40351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27317
  · exact u27318
  · exact u27319

def r40352 : Route 9 := (fun mask => (mask,id))

def c40352 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40352 : Upper (D 6) (R 6) [96,129,264,48,68] 13 := by
  apply FastRouting.sound _ _ [96,129,264,48,68] 13 (by decide) (choices 1) [1,2,4] r40352 c40352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27320
  · exact u27321
  · exact u27322

def b40353 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 292 11 22 124 92 220 348), lower := (rows 97 131 292 11 22 32 64 128 256), losses := [] }

theorem u40353 : Upper (D 6) (R 6) [96,129,288,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40354 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 292 11 26 116 84 212 340), lower := (rows 97 131 292 11 26 32 64 128 256), losses := [] }

theorem u40354 : Upper (D 6) (R 6) [96,129,288,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40355 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 292 11 28 118 86 214 342), lower := (rows 97 131 292 11 28 32 64 128 256), losses := [] }

theorem u40355 : Upper (D 6) (R 6) [96,129,288,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40356 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 292 11 82 60 92 156 284), lower := (rows 97 131 292 11 82 32 64 128 256), losses := [] }

theorem u40356 : Upper (D 6) (R 6) [96,129,288,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40357 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 292 11 84 62 94 158 286), lower := (rows 97 131 292 11 84 32 64 128 256), losses := [] }

theorem u40357 : Upper (D 6) (R 6) [96,129,288,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40358 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 292 11 88 54 86 150 278), lower := (rows 97 131 292 11 88 32 64 128 256), losses := [] }

theorem u40358 : Upper (D 6) (R 6) [96,129,288,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40359 : Route 9 := (fun mask => (mask,id))

def c40359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40359 : Upper (D 6) (R 6) [96,129,288,5,6] 13 := by
  apply FastRouting.sound _ _ [96,129,288,5,6] 13 (by decide) (choices 1) [2,8,16,64] r40359 c40359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27323
  · exact u27324
  · exact u27325
  · exact u27326

def b40360 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 97 131 292 13 26 118 86 214 342), lower := (rows 97 131 292 13 26 32 64 128 256), losses := [] }

theorem u40360 : Upper (D 6) (R 6) [96,129,288,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40361 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 97 131 292 13 28 114 82 210 338), lower := (rows 97 131 292 13 28 32 64 128 256), losses := [] }

theorem u40361 : Upper (D 6) (R 6) [96,129,288,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40362 : Route 9 := (fun mask => (mask,id))

def c40362 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40362 : Upper (D 6) (R 6) [96,129,288,5,66] 13 := by
  apply FastRouting.sound _ _ [96,129,288,5,66] 13 (by decide) (choices 1) [2,4,8,16] r40362 c40362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27327
  · exact u27328
  · exact u27329
  · exact u27330

def r40363 : Route 9 := (fun mask => (mask,id))

def c40363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40363 : Upper (D 6) (R 6) [96,129,288,5,68] 13 := by
  apply FastRouting.sound _ _ [96,129,288,5,68] 13 (by decide) (choices 1) [2,8,16] r40363 c40363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27331
  · exact u27332
  · exact u27333

def r40364 : Route 9 := (fun mask => (mask,id))

def c40364 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40364 : Upper (D 6) (R 6) [96,129,288,5,72] 13 := by
  apply FastRouting.sound _ _ [96,129,288,5,72] 13 (by decide) (choices 1) [2,4,16] r40364 c40364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27334
  · exact u27335
  · exact u27336

def b40365 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 131 292 14 22 121 89 217 345), lower := (rows 97 131 292 14 22 32 64 128 256), losses := [] }

theorem u40365 : Upper (D 6) (R 6) [96,129,288,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40366 : Route 9 := (fun mask => (mask,id))

def c40366 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40366 : Upper (D 6) (R 6) [96,129,288,6,9] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,9] 13 (by decide) (choices 1) [2,4,16,64] r40366 c40366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27337
  · exact u27338
  · exact u27339
  · exact u27340

def b40367 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 97 131 292 14 26 117 85 213 341), lower := (rows 97 131 292 14 26 32 64 128 256), losses := [] }

theorem u40367 : Upper (D 6) (R 6) [96,129,288,6,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40368 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 97 131 292 14 28 115 83 211 339), lower := (rows 97 131 292 14 28 32 64 128 256), losses := [] }

theorem u40368 : Upper (D 6) (R 6) [96,129,288,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40369 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 131 292 14 81 62 94 158 286), lower := (rows 97 131 292 14 81 32 64 128 256), losses := [] }

theorem u40369 : Upper (D 6) (R 6) [96,129,288,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40370 : Route 9 := (fun mask => (mask,id))

def c40370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40370 : Upper (D 6) (R 6) [96,129,288,6,66] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,66] 13 (by decide) (choices 1) [1,4,8,16] r40370 c40370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27341
  · exact u27342
  · exact u27343
  · exact u27344

def r40371 : Route 9 := (fun mask => (mask,id))

def c40371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40371 : Upper (D 6) (R 6) [96,129,288,6,68] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,68] 13 (by decide) (choices 1) [1,2,8,16] r40371 c40371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27345
  · exact u27346
  · exact u27347
  · exact u27348

def r40372 : Route 9 := (fun mask => (mask,id))

def c40372 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40372 : Upper (D 6) (R 6) [96,129,288,6,72] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6,72] 13 (by decide) (choices 1) [1,2,4,16] r40372 c40372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27349
  · exact u27350
  · exact u27351
  · exact u27352

def b40373 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 292 25 26 102 70 198 326), lower := (rows 97 131 292 25 26 32 64 128 256), losses := [] }

theorem u40373 : Upper (D 6) (R 6) [96,129,288,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40374 : Route 9 := (fun mask => (mask,id))

def c40374 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40374 : Upper (D 6) (R 6) [96,129,288,17,12] 13 := by
  apply FastRouting.sound _ _ [96,129,288,17,12] 13 (by decide) (choices 1) [2,4,64] r40374 c40374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27353
  · exact u27354
  · exact u27355

def r40375 : Route 9 := (fun mask => (mask,id))

def c40375 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40375 : Upper (D 6) (R 6) [96,129,288,17,66] 13 := by
  apply FastRouting.sound _ _ [96,129,288,17,66] 13 (by decide) (choices 1) [2,4,8] r40375 c40375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27356
  · exact u27357
  · exact u27358

def r40376 : Route 9 := (fun mask => (mask,id))

def c40376 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40376 : Upper (D 6) (R 6) [96,129,288,17,68] 13 := by
  apply FastRouting.sound _ _ [96,129,288,17,68] 13 (by decide) (choices 1) [2,4,8] r40376 c40376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27359
  · exact u27360
  · exact u27361

def b40377 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 131 292 25 88 38 70 134 262), lower := (rows 97 131 292 25 88 32 64 128 256), losses := [] }

theorem u40377 : Upper (D 6) (R 6) [96,129,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40378 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 131 292 26 26 101 69 197 325), lower := (rows 97 131 292 26 26 32 64 128 256), losses := [] }

theorem u40378 : Upper (D 6) (R 6) [96,129,288,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40379 : Route 9 := (fun mask => (mask,id))

def c40379 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40379 : Upper (D 6) (R 6) [96,129,288,18,12] 13 := by
  apply FastRouting.sound _ _ [96,129,288,18,12] 13 (by decide) (choices 1) [1,2,4,64] r40379 c40379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27362
  · exact u27363
  · exact u27364
  · exact u27365

#print axioms u40379
end Delivery.IrregularNine14.P06
