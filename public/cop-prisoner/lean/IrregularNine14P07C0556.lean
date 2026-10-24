import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0288
import IrregularNine14P07C0289

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33360 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 164 392 82 51 83 147 275), lower := (rows 13 98 164 392 82 32 64 128 256), losses := [] }

theorem u33360 : Upper (D 7) (R 7) [12,96,160,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33361 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 259 21 42 50 224 192 192 448), lower := (rows 13 259 21 42 50 32 64 128 256), losses := [] }

theorem u33361 : Upper (D 7) (R 7) [12,257,17,34,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33362 : Route 9 := (fun mask => (mask,id))

def c33362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33362 : Upper (D 7) (R 7) [12,257,17,34,66] 13 := by
  apply FastRouting.sound _ _ [12,257,17,34,66] 13 (by decide) (choices 1) [64,128] r33362 c33362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17291
  · exact u17292

def r33363 : Route 9 := (fun mask => (mask,id))

def c33363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33363 : Upper (D 7) (R 7) [12,257,17,34,96] 13 := by
  apply FastRouting.sound _ _ [12,257,17,34,96] 13 (by decide) (choices 1) [2,64,128] r33363 c33363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17293
  · exact u17294
  · exact u17295

def r33364 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33364 : Upper (D 7) (R 7) [12,257,17,34,192] 13 := by
  apply FastRouting.sound _ _ [12,257,17,34,192] 13 (by decide) (choices 1) [2,64] r33364 c33364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17296
  · exact u17297

def r33365 : Route 9 := (fun mask => (mask,id))

def c33365 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33365 : Upper (D 7) (R 7) [12,257,17,96,34] 13 := by
  apply FastRouting.sound _ _ [12,257,17,96,34] 13 (by decide) (choices 1) [2,64,128] r33365 c33365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17298
  · exact u17299
  · exact u17300

def b33366 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 21, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 21 104 112 162 194 130 386), lower := (rows 13 259 21 104 112 32 64 128 256), losses := [] }

theorem u33366 : Upper (D 7) (R 7) [12,257,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33367 : Route 9 := (fun mask => (mask,id))

def c33367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33367 : Upper (D 7) (R 7) [12,257,17,96,130] 13 := by
  apply FastRouting.sound _ _ [12,257,17,96,130] 13 (by decide) (choices 1) [2,64,128] r33367 c33367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17301
  · exact u17302
  · exact u17303

def r33368 : Route 9 := (fun mask => (mask,id))

def c33368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33368 : Upper (D 7) (R 7) [12,257,17,96,160] 13 := by
  apply FastRouting.sound _ _ [12,257,17,96,160] 13 (by decide) (choices 1) [2,64,128] r33368 c33368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17304
  · exact u17305
  · exact u17306

def b33369 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 259 22 41 50 224 192 192 448), lower := (rows 13 259 22 41 50 32 64 128 256), losses := [] }

theorem u33369 : Upper (D 7) (R 7) [12,257,18,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33370 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 1, region := 244, targets := 1 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 259 22 41 82 224 224 224 480), lower := (rows 13 259 22 41 82 32 64 128 256), losses := [] }

theorem u33370 : Upper (D 7) (R 7) [12,257,18,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33371 : Route 9 := (fun mask => (mask,id))

def c33371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33371 : Upper (D 7) (R 7) [12,257,18,33,96] 13 := by
  apply FastRouting.sound _ _ [12,257,18,33,96] 13 (by decide) (choices 1) [2,64,128] r33371 c33371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17307
  · exact u17308
  · exact u17309

def r33372 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33372 : Upper (D 7) (R 7) [12,257,18,33,192] 13 := by
  apply FastRouting.sound _ _ [12,257,18,33,192] 13 (by decide) (choices 1) [2,64] r33372 c33372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17310
  · exact u17311

def b33373 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 259 22 42 49 224 192 192 448), lower := (rows 13 259 22 42 49 32 64 128 256), losses := [] }

theorem u33373 : Upper (D 7) (R 7) [12,257,18,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33374 : Route 9 := (fun mask => (mask,id))

def c33374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33374 : Upper (D 7) (R 7) [12,257,18,34,65] 13 := by
  apply FastRouting.sound _ _ [12,257,18,34,65] 13 (by decide) (choices 1) [64,128] r33374 c33374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17312
  · exact u17313

def r33375 : Route 9 := (fun mask => (mask,id))

def c33375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33375 : Upper (D 7) (R 7) [12,257,18,34,96] 13 := by
  apply FastRouting.sound _ _ [12,257,18,34,96] 13 (by decide) (choices 1) [1,64,128] r33375 c33375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17314
  · exact u17315
  · exact u17316

def r33376 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33376 : Upper (D 7) (R 7) [12,257,18,34,192] 13 := by
  apply FastRouting.sound _ _ [12,257,18,34,192] 13 (by decide) (choices 1) [1,64] r33376 c33376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17317
  · exact u17318

def b33377 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 20, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(4,5)], upper := (rows 13 259 22 104 19 224 224 224 480), lower := (rows 13 259 22 104 19 32 64 128 256), losses := [] }

theorem u33377 : Upper (D 7) (R 7) [12,257,18,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33378 : Route 9 := (fun mask => (mask,id))

def c33378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33378 : Upper (D 7) (R 7) [12,257,18,96,33] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96,33] 13 (by decide) (choices 1) [2,64,128] r33378 c33378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17319
  · exact u17320
  · exact u17321

def b33379 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 259 22 104 50 225 193 193 449), lower := (rows 13 259 22 104 50 32 64 128 256), losses := [] }

theorem u33379 : Upper (D 7) (R 7) [12,257,18,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33380 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 16, targets := 131 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,7)], upper := (rows 13 259 22 104 112 163 195 131 387), lower := (rows 13 259 22 104 112 32 64 128 256), losses := [] }

theorem u33380 : Upper (D 7) (R 7) [12,257,18,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33381 : Route 9 := (fun mask => (mask,id))

def c33381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33381 : Upper (D 7) (R 7) [12,257,18,96,129] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96,129] 13 (by decide) (choices 1) [2,64,128] r33381 c33381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17322
  · exact u17323
  · exact u17324

def b33382 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 259 22 104 146 225 225 225 481), lower := (rows 13 259 22 104 146 32 64 128 256), losses := [] }

theorem u33382 : Upper (D 7) (R 7) [12,257,18,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33383 : Route 9 := (fun mask => (mask,id))

def c33383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33383 : Upper (D 7) (R 7) [12,257,18,96,160] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96,160] 13 (by decide) (choices 1) [1,2,64,128] r33383 c33383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17325
  · exact u17326
  · exact u17327
  · exact u17328

def r33384 : Route 9 := (fun mask => (mask,id))

def c33384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33384 : Upper (D 7) (R 7) [12,257,33,66,34] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,34] 13 (by decide) (choices 1) [16,64,128] r33384 c33384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17329
  · exact u17330
  · exact u17331

def b33385 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 16, targets := 160 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 13 259 37 74 82 176 240 176 432), lower := (rows 13 259 37 74 82 32 64 128 256), losses := [] }

theorem u33385 : Upper (D 7) (R 7) [12,257,33,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33386 : Route 9 := (fun mask => (mask,id))

def c33386 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33386 : Upper (D 7) (R 7) [12,257,33,66,96] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,96] 13 (by decide) (choices 1) [2,16,128] r33386 c33386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17332
  · exact u17333
  · exact u17334

def r33387 : Route 9 := (fun mask => (mask,id))

def c33387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33387 : Upper (D 7) (R 7) [12,257,33,66,130] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,130] 13 (by decide) (choices 1) [16,64,128] r33387 c33387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17335
  · exact u17336
  · exact u17337

def r33388 : Route 9 := (fun mask => (mask,id))

def c33388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33388 : Upper (D 7) (R 7) [12,257,33,66,160] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,160] 13 (by decide) (choices 1) [2,16,64,128] r33388 c33388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17338
  · exact u17339
  · exact u17340
  · exact u17341

def r33389 : Route 9 := (fun mask => (mask,id))

def c33389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33389 : Upper (D 7) (R 7) [12,257,33,66,192] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,192] 13 (by decide) (choices 1) [2,16,128] r33389 c33389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17342
  · exact u17343
  · exact u17344

def b33390 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 450, targets := 32 },{ cop := 4, region := 200, targets := 32 }], pairs := [(1,5),(3,0),(3,5),(4,0)], upper := (rows 13 259 37 88 50 226 194 194 450), lower := (rows 13 259 37 88 50 32 64 128 256), losses := [] }

theorem u33390 : Upper (D 7) (R 7) [12,257,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33391 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 13 259 37 88 82 162 226 162 418), lower := (rows 13 259 37 88 82 32 64 128 256), losses := [] }

theorem u33391 : Upper (D 7) (R 7) [12,257,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33392 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 37 88 112 162 194 130 386), lower := (rows 13 259 37 88 112 32 64 128 256), losses := [] }

theorem u33392 : Upper (D 7) (R 7) [12,257,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33393 : Route 9 := (fun mask => (mask,id))

def c33393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33393 : Upper (D 7) (R 7) [12,257,33,80,130] 13 := by
  apply FastRouting.sound _ _ [12,257,33,80,130] 13 (by decide) (choices 1) [2,64,128] r33393 c33393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17345
  · exact u17346
  · exact u17347

def r33394 : Route 9 := (fun mask => (mask,id))

def c33394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33394 : Upper (D 7) (R 7) [12,257,33,80,160] 13 := by
  apply FastRouting.sound _ _ [12,257,33,80,160] 13 (by decide) (choices 1) [2,64,128] r33394 c33394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17348
  · exact u17349
  · exact u17350

def b33395 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 259 37 88 208 162 226 162 418), lower := (rows 13 259 37 88 208 32 64 128 256), losses := [] }

theorem u33395 : Upper (D 7) (R 7) [12,257,33,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33396 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33396 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33396 : Upper (D 7) (R 7) [12,257,33,192,34] 13 := by
  apply FastRouting.sound _ _ [12,257,33,192,34] 13 (by decide) (choices 1) [2,16,64] r33396 c33396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17351
  · exact u17352
  · exact u17353

def r33397 : Route 9 := (fun mask => (mask,id))

def c33397 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33397 : Upper (D 7) (R 7) [12,257,33,192,66] 13 := by
  apply FastRouting.sound _ _ [12,257,33,192,66] 13 (by decide) (choices 1) [2,16,128] r33397 c33397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17354
  · exact u17355
  · exact u17356

def r33398 : Route 9 := (fun mask => (mask,id))

def c33398 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33398 : Upper (D 7) (R 7) [12,257,33,192,96] 13 := by
  apply FastRouting.sound _ _ [12,257,33,192,96] 13 (by decide) (choices 1) [2,16,128] r33398 c33398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17357
  · exact u17358
  · exact u17359

def b33399 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 259 37 200 208 50 114 178 306), lower := (rows 13 259 37 200 208 32 64 128 256), losses := [] }

theorem u33399 : Upper (D 7) (R 7) [12,257,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33400 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 25, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 259 38 56 19 224 192 192 448), lower := (rows 13 259 38 56 19 32 64 128 256), losses := [] }

theorem u33400 : Upper (D 7) (R 7) [12,257,34,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33401 : Route 9 := (fun mask => (mask,id))

def c33401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33401 : Upper (D 7) (R 7) [12,257,34,48,65] 13 := by
  apply FastRouting.sound _ _ [12,257,34,48,65] 13 (by decide) (choices 1) [2,64,128] r33401 c33401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17360
  · exact u17361
  · exact u17362

def r33402 : Route 9 := (fun mask => (mask,id))

def c33402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33402 : Upper (D 7) (R 7) [12,257,34,48,66] 13 := by
  apply FastRouting.sound _ _ [12,257,34,48,66] 13 (by decide) (choices 1) [1,64,128] r33402 c33402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17363
  · exact u17364
  · exact u17365

def r33403 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33403 : Upper (D 7) (R 7) [12,257,34,48,192] 13 := by
  apply FastRouting.sound _ _ [12,257,34,48,192] 13 (by decide) (choices 1) [1,2,64] r33403 c33403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17366
  · exact u17367
  · exact u17368

def r33404 : Route 9 := (fun mask => (mask,id))

def c33404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33404 : Upper (D 7) (R 7) [12,257,34,66,33] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,33] 13 (by decide) (choices 1) [16,64,128] r33404 c33404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17369
  · exact u17370
  · exact u17371

def r33405 : Route 9 := (fun mask => (mask,id))

def c33405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33405 : Upper (D 7) (R 7) [12,257,34,66,96] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,96] 13 (by decide) (choices 1) [1,16,128] r33405 c33405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17372
  · exact u17373
  · exact u17374

def r33406 : Route 9 := (fun mask => (mask,id))

def c33406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33406 : Upper (D 7) (R 7) [12,257,34,66,129] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,129] 13 (by decide) (choices 1) [16,64,128] r33406 c33406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17375
  · exact u17376
  · exact u17377

def r33407 : Route 9 := (fun mask => (mask,id))

def c33407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33407 : Upper (D 7) (R 7) [12,257,34,66,160] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,160] 13 (by decide) (choices 1) [1,16,64,128] r33407 c33407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17378
  · exact u17379
  · exact u17380
  · exact u17381

def b33408 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 259 38 88 19 224 224 224 480), lower := (rows 13 259 38 88 19 32 64 128 256), losses := [] }

theorem u33408 : Upper (D 7) (R 7) [12,257,34,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33409 : Route 9 := (fun mask => (mask,id))

def c33409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33409 : Upper (D 7) (R 7) [12,257,34,80,33] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,33] 13 (by decide) (choices 1) [2,64,128] r33409 c33409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17382
  · exact u17383
  · exact u17384

def b33410 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 16, targets := 193 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,6),(4,7)], upper := (rows 13 259 38 88 50 225 193 193 449), lower := (rows 13 259 38 88 50 32 64 128 256), losses := [] }

theorem u33410 : Upper (D 7) (R 7) [12,257,34,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33411 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 259 38 88 81 162 226 162 418), lower := (rows 13 259 38 88 81 32 64 128 256), losses := [] }

theorem u33411 : Upper (D 7) (R 7) [12,257,34,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33412 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 259 38 88 82 161 225 161 417), lower := (rows 13 259 38 88 82 32 64 128 256), losses := [] }

theorem u33412 : Upper (D 7) (R 7) [12,257,34,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33413 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 259 38 88 112 163 195 131 387), lower := (rows 13 259 38 88 112 32 64 128 256), losses := [] }

theorem u33413 : Upper (D 7) (R 7) [12,257,34,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33414 : Route 9 := (fun mask => (mask,id))

def c33414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33414 : Upper (D 7) (R 7) [12,257,34,80,129] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,129] 13 (by decide) (choices 1) [2,64,128] r33414 c33414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17385
  · exact u17386
  · exact u17387

def r33415 : Route 9 := (fun mask => (mask,id))

def c33415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33415 : Upper (D 7) (R 7) [12,257,34,80,130] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,130] 13 (by decide) (choices 1) [1,64,128] r33415 c33415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17388
  · exact u17389
  · exact u17390

def r33416 : Route 9 := (fun mask => (mask,id))

def c33416 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33416 : Upper (D 7) (R 7) [12,257,34,80,160] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,160] 13 (by decide) (choices 1) [1,2,64,128] r33416 c33416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17391
  · exact u17392
  · exact u17393
  · exact u17394

def b33417 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 259 38 88 208 163 227 163 419), lower := (rows 13 259 38 88 208 32 64 128 256), losses := [] }

theorem u33417 : Upper (D 7) (R 7) [12,257,34,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33418 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 13 259 38 104 19 240 208 208 464), lower := (rows 13 259 38 104 19 32 64 128 256), losses := [] }

theorem u33418 : Upper (D 7) (R 7) [12,257,34,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33419 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,5),(1,6),(2,6),(4,5)], upper := (rows 13 259 38 104 81 178 210 146 402), lower := (rows 13 259 38 104 81 32 64 128 256), losses := [] }

theorem u33419 : Upper (D 7) (R 7) [12,257,34,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33419
end Delivery.IrregularNine14.P07
