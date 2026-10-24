import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0105
import IrregularNine14P08C0106
import IrregularNine14P08C0107

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17340 : Route 9 := (fun mask => (mask,id))

def c17340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17340 : Upper (D 8) (R 8) [288,5,96,34,65] 13 := by
  apply FastRouting.sound _ _ [288,5,96,34,65] 13 (by decide) (choices 1) [8,16,128] r17340 c17340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6337
  · exact u6338
  · exact u6339

def b17341 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 42 88 177 209 145 401), lower := (rows 289 7 100 42 88 32 64 128 256), losses := [] }

theorem u17341 : Upper (D 8) (R 8) [288,5,96,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17342 : Route 9 := (fun mask => (mask,id))

def c17342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u17342 : Upper (D 8) (R 8) [288,5,96,34,129] 13 := by
  apply FastRouting.sound _ _ [288,5,96,34,129] 13 (by decide) (choices 1) [8,16,64,128] r17342 c17342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6340
  · exact u6341
  · exact u6342
  · exact u6343

def r17343 : Route 9 := (fun mask => (mask,id))

def c17343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17343 : Upper (D 8) (R 8) [288,5,96,34,136] 13 := by
  apply FastRouting.sound _ _ [288,5,96,34,136] 13 (by decide) (choices 1) [1,16,64,128] r17343 c17343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6344
  · exact u6345
  · exact u6346
  · exact u6347

def r17344 : Route 9 := (fun mask => (mask,id))

def c17344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17344 : Upper (D 8) (R 8) [288,5,96,34,192] 13 := by
  apply FastRouting.sound _ _ [288,5,96,34,192] 13 (by decide) (choices 1) [1,8,16,128] r17344 c17344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6348
  · exact u6349
  · exact u6350
  · exact u6351

def r17345 : Route 9 := (fun mask => (mask,id))

def c17345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17345 : Upper (D 8) (R 8) [288,5,96,48,65] 13 := by
  apply FastRouting.sound _ _ [288,5,96,48,65] 13 (by decide) (choices 1) [2,8,128] r17345 c17345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6352
  · exact u6353
  · exact u6354

def b17346 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 56 82 169 201 137 393), lower := (rows 289 7 100 56 82 32 64 128 256), losses := [] }

theorem u17346 : Upper (D 8) (R 8) [288,5,96,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17347 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 100 56 88 163 195 131 387), lower := (rows 289 7 100 56 88 32 64 128 256), losses := [] }

theorem u17347 : Upper (D 8) (R 8) [288,5,96,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17348 : Route 9 := (fun mask => (mask,id))

def c17348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17348 : Upper (D 8) (R 8) [288,5,96,48,129] 13 := by
  apply FastRouting.sound _ _ [288,5,96,48,129] 13 (by decide) (choices 1) [2,8,64,128] r17348 c17348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6355
  · exact u6356
  · exact u6357
  · exact u6358

def r17349 : Route 9 := (fun mask => (mask,id))

def c17349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17349 : Upper (D 8) (R 8) [288,5,96,48,130] 13 := by
  apply FastRouting.sound _ _ [288,5,96,48,130] 13 (by decide) (choices 1) [1,8,64,128] r17349 c17349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6359
  · exact u6360
  · exact u6361
  · exact u6362

def r17350 : Route 9 := (fun mask => (mask,id))

def c17350 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17350 : Upper (D 8) (R 8) [288,5,96,48,136] 13 := by
  apply FastRouting.sound _ _ [288,5,96,48,136] 13 (by decide) (choices 1) [1,2,64,128] r17350 c17350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6363
  · exact u6364
  · exact u6365
  · exact u6366

def r17351 : Route 9 := (fun mask => (mask,id))

def c17351 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17351 : Upper (D 8) (R 8) [288,5,96,48,192] 13 := by
  apply FastRouting.sound _ _ [288,5,96,48,192] 13 (by decide) (choices 1) [1,2,8,128] r17351 c17351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6367
  · exact u6368
  · exact u6369
  · exact u6370

def r17352 : Route 9 := (fun mask => (mask,id))

def c17352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17352 : Upper (D 8) (R 8) [288,5,96,65,130] 13 := by
  apply FastRouting.sound _ _ [288,5,96,65,130] 13 (by decide) (choices 1) [8,16,128] r17352 c17352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6371
  · exact u6372
  · exact u6373

def r17353 : Route 9 := (fun mask => (mask,id))

def c17353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17353 : Upper (D 8) (R 8) [288,5,96,65,136] 13 := by
  apply FastRouting.sound _ _ [288,5,96,65,136] 13 (by decide) (choices 1) [2,16,128] r17353 c17353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6374
  · exact u6375
  · exact u6376

def r17354 : Route 9 := (fun mask => (mask,id))

def c17354 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17354 : Upper (D 8) (R 8) [288,5,96,65,160] 13 := by
  apply FastRouting.sound _ _ [288,5,96,65,160] 13 (by decide) (choices 1) [2,8,16,128] r17354 c17354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6377
  · exact u6378
  · exact u6379
  · exact u6380

def b17355 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 74 145 184 248 184 440), lower := (rows 289 7 100 74 145 32 64 128 256), losses := [] }

theorem u17355 : Upper (D 8) (R 8) [288,5,96,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17356 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 74 152 177 241 177 433), lower := (rows 289 7 100 74 152 32 64 128 256), losses := [] }

theorem u17356 : Upper (D 8) (R 8) [288,5,96,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17357 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 74 176 185 217 153 409), lower := (rows 289 7 100 74 176 32 64 128 256), losses := [] }

theorem u17357 : Upper (D 8) (R 8) [288,5,96,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17358 : Route 9 := (fun mask => (mask,id))

def c17358 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17358 : Upper (D 8) (R 8) [288,5,96,80,129] 13 := by
  apply FastRouting.sound _ _ [288,5,96,80,129] 13 (by decide) (choices 1) [2,8,128] r17358 c17358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6381
  · exact u6382
  · exact u6383

def b17359 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 88 146 169 233 169 425), lower := (rows 289 7 100 88 146 32 64 128 256), losses := [] }

theorem u17359 : Upper (D 8) (R 8) [288,5,96,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17360 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 88 152 163 227 163 419), lower := (rows 289 7 100 88 152 32 64 128 256), losses := [] }

theorem u17360 : Upper (D 8) (R 8) [288,5,96,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17361 : Route 9 := (fun mask => (mask,id))

def c17361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17361 : Upper (D 8) (R 8) [288,5,96,80,160] 13 := by
  apply FastRouting.sound _ _ [288,5,96,80,160] 13 (by decide) (choices 1) [1,2,8,128] r17361 c17361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6384
  · exact u6385
  · exact u6386
  · exact u6387

def b17362 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 100 104 145 186 218 154 410), lower := (rows 289 7 100 104 145 32 64 128 256), losses := [] }

theorem u17362 : Upper (D 8) (R 8) [288,5,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17363 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 100 104 146 185 217 153 409), lower := (rows 289 7 100 104 146 32 64 128 256), losses := [] }

theorem u17363 : Upper (D 8) (R 8) [288,5,96,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17364 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 100 104 152 179 211 147 403), lower := (rows 289 7 100 104 152 32 64 128 256), losses := [] }

theorem u17364 : Upper (D 8) (R 8) [288,5,96,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17365 : Route 9 := (fun mask => (mask,id))

def c17365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17365 : Upper (D 8) (R 8) [288,5,96,129,130] 13 := by
  apply FastRouting.sound _ _ [288,5,96,129,130] 13 (by decide) (choices 1) [8,16,64] r17365 c17365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6388
  · exact u6389
  · exact u6390

def b17366 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 100 137 152 114 114 242 370), lower := (rows 289 7 100 137 152 32 64 128 256), losses := [] }

theorem u17366 : Upper (D 8) (R 8) [288,5,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17367 : Route 9 := (fun mask => (mask,id))

def c17367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17367 : Upper (D 8) (R 8) [288,5,96,129,160] 13 := by
  apply FastRouting.sound _ _ [288,5,96,129,160] 13 (by decide) (choices 1) [2,8,16,64] r17367 c17367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6391
  · exact u6392
  · exact u6393
  · exact u6394

def r17368 : Route 9 := (fun mask => (mask,id))

def c17368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17368 : Upper (D 8) (R 8) [288,5,96,129,192] 13 := by
  apply FastRouting.sound _ _ [288,5,96,129,192] 13 (by decide) (choices 1) [2,8,16] r17368 c17368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6395
  · exact u6396
  · exact u6397

def b17369 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 100 138 152 113 113 241 369), lower := (rows 289 7 100 138 152 32 64 128 256), losses := [] }

theorem u17369 : Upper (D 8) (R 8) [288,5,96,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17370 : Route 9 := (fun mask => (mask,id))

def c17370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17370 : Upper (D 8) (R 8) [288,5,96,130,160] 13 := by
  apply FastRouting.sound _ _ [288,5,96,130,160] 13 (by decide) (choices 1) [1,8,16,64] r17370 c17370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6398
  · exact u6399
  · exact u6400
  · exact u6401

def r17371 : Route 9 := (fun mask => (mask,id))

def c17371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17371 : Upper (D 8) (R 8) [288,5,96,130,192] 13 := by
  apply FastRouting.sound _ _ [288,5,96,130,192] 13 (by decide) (choices 1) [1,8,16] r17371 c17371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6402
  · exact u6403
  · exact u6404

def b17372 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 100 152 152 99 99 227 355), lower := (rows 289 7 100 152 152 32 64 128 256), losses := [] }

theorem u17372 : Upper (D 8) (R 8) [288,5,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17373 : PairBound 9 := { available := 75, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 152 176 107 75 203 331), lower := (rows 289 7 100 152 176 32 64 128 256), losses := [] }

theorem u17373 : Upper (D 8) (R 8) [288,5,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17374 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 152 208 43 107 171 299), lower := (rows 289 7 100 152 208 32 64 128 256), losses := [] }

theorem u17374 : Upper (D 8) (R 8) [288,5,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17375 : Route 9 := (fun mask => (mask,id))

def c17375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17375 : Upper (D 8) (R 8) [288,5,96,160,192] 13 := by
  apply FastRouting.sound _ _ [288,5,96,160,192] 13 (by decide) (choices 1) [1,2,8,16] r17375 c17375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6405
  · exact u6406
  · exact u6407
  · exact u6408

def b17376 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 25 208 42 106 170 298), lower := (rows 289 7 196 25 208 32 64 128 256), losses := [] }

theorem u17376 : Upper (D 8) (R 8) [288,5,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17377 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 196 26 49 232 232 232 488), lower := (rows 289 7 196 26 49 32 64 128 256), losses := [] }

theorem u17377 : Upper (D 8) (R 8) [288,5,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17378 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c17378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17378 : Upper (D 8) (R 8) [288,5,192,18,40] 13 := by
  apply FastRouting.sound _ _ [288,5,192,18,40] 13 (by decide) (choices 1) [1,64] r17378 c17378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6409
  · exact u6410

def b17379 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 196 26 81 168 232 168 424), lower := (rows 289 7 196 26 81 32 64 128 256), losses := [] }

theorem u17379 : Upper (D 8) (R 8) [288,5,192,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17380 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 26 88 161 225 161 417), lower := (rows 289 7 196 26 88 32 64 128 256), losses := [] }

theorem u17380 : Upper (D 8) (R 8) [288,5,192,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17381 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 26 112 169 233 169 425), lower := (rows 289 7 196 26 112 32 64 128 256), losses := [] }

theorem u17381 : Upper (D 8) (R 8) [288,5,192,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17382 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 26 208 41 105 169 297), lower := (rows 289 7 196 26 208 32 64 128 256), losses := [] }

theorem u17382 : Upper (D 8) (R 8) [288,5,192,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17383 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 196 41 50 248 216 216 472), lower := (rows 289 7 196 41 50 32 64 128 256), losses := [] }

theorem u17383 : Upper (D 8) (R 8) [288,5,192,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17384 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 196 41 56 242 210 210 466), lower := (rows 289 7 196 41 56 32 64 128 256), losses := [] }

theorem u17384 : Upper (D 8) (R 8) [288,5,192,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17385 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 196 41 88 178 242 178 434), lower := (rows 289 7 196 41 88 32 64 128 256), losses := [] }

theorem u17385 : Upper (D 8) (R 8) [288,5,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17386 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 196 41 112 186 218 154 410), lower := (rows 289 7 196 41 112 32 64 128 256), losses := [] }

theorem u17386 : Upper (D 8) (R 8) [288,5,192,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17387 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 42 56 241 209 209 465), lower := (rows 289 7 196 42 56 32 64 128 256), losses := [] }

theorem u17387 : Upper (D 8) (R 8) [288,5,192,34,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17388 : Route 9 := (fun mask => (mask,id))

def c17388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17388 : Upper (D 8) (R 8) [288,5,192,34,65] 13 := by
  apply FastRouting.sound _ _ [288,5,192,34,65] 13 (by decide) (choices 1) [8,16,128] r17388 c17388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6411
  · exact u6412
  · exact u6413

def b17389 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 42 88 177 241 177 433), lower := (rows 289 7 196 42 88 32 64 128 256), losses := [] }

theorem u17389 : Upper (D 8) (R 8) [288,5,192,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17390 : Route 9 := (fun mask => (mask,id))

def c17390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17390 : Upper (D 8) (R 8) [288,5,192,34,96] 13 := by
  apply FastRouting.sound _ _ [288,5,192,34,96] 13 (by decide) (choices 1) [1,8,16,128] r17390 c17390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6414
  · exact u6415
  · exact u6416
  · exact u6417

def b17391 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 42 208 57 121 185 313), lower := (rows 289 7 196 42 208 32 64 128 256), losses := [] }

theorem u17391 : Upper (D 8) (R 8) [288,5,192,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17392 : PairBound 9 := { available := 195, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 196 56 56 227 195 195 451), lower := (rows 289 7 196 56 56 32 64 128 256), losses := [] }

theorem u17392 : Upper (D 8) (R 8) [288,5,192,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17393 : Route 9 := (fun mask => (mask,id))

def c17393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17393 : Upper (D 8) (R 8) [288,5,192,48,65] 13 := by
  apply FastRouting.sound _ _ [288,5,192,48,65] 13 (by decide) (choices 1) [2,8,128] r17393 c17393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6418
  · exact u6419
  · exact u6420

def b17394 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 56 82 169 233 169 425), lower := (rows 289 7 196 56 82 32 64 128 256), losses := [] }

theorem u17394 : Upper (D 8) (R 8) [288,5,192,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17395 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 56 88 163 227 163 419), lower := (rows 289 7 196 56 88 32 64 128 256), losses := [] }

theorem u17395 : Upper (D 8) (R 8) [288,5,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17396 : PairBound 9 := { available := 139, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 196 56 112 171 203 139 395), lower := (rows 289 7 196 56 112 32 64 128 256), losses := [] }

theorem u17396 : Upper (D 8) (R 8) [288,5,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17397 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 56 208 43 107 171 299), lower := (rows 289 7 196 56 208 32 64 128 256), losses := [] }

theorem u17397 : Upper (D 8) (R 8) [288,5,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17398 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 196 73 146 56 120 184 312), lower := (rows 289 7 196 73 146 32 64 128 256), losses := [] }

theorem u17398 : Upper (D 8) (R 8) [288,5,192,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17399 : Route 9 := (fun mask => (mask,id))

def c17399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17399 : Upper (D 8) (R 8) [288,5,192,65,136] 13 := by
  apply FastRouting.sound _ _ [288,5,192,65,136] 13 (by decide) (choices 1) [2,16] r17399 c17399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6421
  · exact u6422

#print axioms u17399
end Delivery.IrregularNine14.P08
