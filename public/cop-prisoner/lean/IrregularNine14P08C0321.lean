import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0139
import IrregularNine14P08C0140
import IrregularNine14P08C0141
import IrregularNine14P08C0142
import IrregularNine14P08C0143

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r19260 : Route 9 := (fun mask => (mask,id))

def c19260 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19260 : Upper (D 8) (R 8) [34,12,48,320] 13 := by
  apply FastRouting.sound _ _ [34,12,48,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19260 c19260
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8369
  · exact u8370
  · exact u8371
  · exact u8372
  · exact u8373
  · exact u8374

def b19261 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 73 432 432 496 432 432), lower := (rows 35 14 69 73 16 32 64 128 256), losses := [] }

theorem u19261 : Upper (D 8) (R 8) [34,12,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19262 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 88 433 417 481 417 417), lower := (rows 35 14 69 88 16 32 64 128 256), losses := [] }

theorem u19262 : Upper (D 8) (R 8) [34,12,65,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19263 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 104 433 433 497 433 433), lower := (rows 35 14 69 104 16 32 64 128 256), losses := [] }

theorem u19263 : Upper (D 8) (R 8) [34,12,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19264 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 69 137 496 496 496 496 496), lower := (rows 35 14 69 137 16 32 64 128 256), losses := [] }

theorem u19264 : Upper (D 8) (R 8) [34,12,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19265 : Route 9 := (fun mask => (mask,id))

def c19265 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19265 : Upper (D 8) (R 8) [34,12,65,144] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19265 c19265
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8375
  · exact u8376
  · exact u8377
  · exact u8378
  · exact u8379
  · exact u8380
  · exact u8381
  · exact u8382
  · exact u8383
  · exact u8384

def r19266 : Route 9 := (fun mask => (mask,id))

def c19266 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19266 : Upper (D 8) (R 8) [34,12,65,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19266 c19266
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8385
  · exact u8386
  · exact u8387
  · exact u8388
  · exact u8389
  · exact u8390
  · exact u8391
  · exact u8392
  · exact u8393
  · exact u8394

def b19267 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 200 433 433 497 433 433), lower := (rows 35 14 69 200 16 32 64 128 256), losses := [] }

theorem u19267 : Upper (D 8) (R 8) [34,12,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19268 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 69 265 240 240 240 240 496), lower := (rows 35 14 69 265 16 32 64 128 256), losses := [] }

theorem u19268 : Upper (D 8) (R 8) [34,12,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19269 : Route 9 := (fun mask => (mask,id))

def c19269 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19269 : Upper (D 8) (R 8) [34,12,65,272] 13 := by
  apply FastRouting.sound _ _ [34,12,65,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19269 c19269
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8395
  · exact u8396
  · exact u8397
  · exact u8398
  · exact u8399
  · exact u8400

def r19270 : Route 9 := (fun mask => (mask,id))

def c19270 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19270 : Upper (D 8) (R 8) [34,12,65,288] 13 := by
  apply FastRouting.sound _ _ [34,12,65,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19270 c19270
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8401
  · exact u8402
  · exact u8403
  · exact u8404
  · exact u8405
  · exact u8406

def b19271 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 328 177 177 241 177 433), lower := (rows 35 14 69 328 16 32 64 128 256), losses := [] }

theorem u19271 : Upper (D 8) (R 8) [34,12,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19272 : Route 9 := (fun mask => (mask,id))

def c19272 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19272 : Upper (D 8) (R 8) [34,12,65,384] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19272 c19272
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8407
  · exact u8408
  · exact u8409
  · exact u8410
  · exact u8411
  · exact u8412

def b19273 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 104 433 417 481 417 417), lower := (rows 35 14 84 104 16 32 64 128 256), losses := [] }

theorem u19273 : Upper (D 8) (R 8) [34,12,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19274 : Route 9 := (fun mask => (mask,id))

def c19274 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19274 : Upper (D 8) (R 8) [34,12,80,160] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19274 c19274
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8413
  · exact u8414
  · exact u8415
  · exact u8416
  · exact u8417
  · exact u8418
  · exact u8419
  · exact u8420
  · exact u8421
  · exact u8422

def b19275 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 200 433 417 481 417 417), lower := (rows 35 14 84 200 16 32 64 128 256), losses := [] }

theorem u19275 : Upper (D 8) (R 8) [34,12,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19276 : Route 9 := (fun mask => (mask,id))

def c19276 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19276 : Upper (D 8) (R 8) [34,12,80,257] 13 := by
  apply FastRouting.sound _ _ [34,12,80,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19276 c19276
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8423
  · exact u8424
  · exact u8425
  · exact u8426
  · exact u8427
  · exact u8428

def r19277 : Route 9 := (fun mask => (mask,id))

def c19277 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19277 : Upper (D 8) (R 8) [34,12,80,288] 13 := by
  apply FastRouting.sound _ _ [34,12,80,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19277 c19277
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8429
  · exact u8430
  · exact u8431
  · exact u8432
  · exact u8433
  · exact u8434

def b19278 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 328 177 161 225 161 417), lower := (rows 35 14 84 328 16 32 64 128 256), losses := [] }

theorem u19278 : Upper (D 8) (R 8) [34,12,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19279 : Route 9 := (fun mask => (mask,id))

def c19279 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19279 : Upper (D 8) (R 8) [34,12,80,384] 13 := by
  apply FastRouting.sound _ _ [34,12,80,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19279 c19279
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8435
  · exact u8436
  · exact u8437
  · exact u8438
  · exact u8439
  · exact u8440

def b19280 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 11, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 100 104 401 433 465 401 401), lower := (rows 35 14 100 104 16 32 64 128 256), losses := [] }

theorem u19280 : Upper (D 8) (R 8) [34,12,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19281 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 100 168 465 497 465 465 465), lower := (rows 35 14 100 168 16 32 64 128 256), losses := [] }

theorem u19281 : Upper (D 8) (R 8) [34,12,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19282 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 200 433 433 497 433 433), lower := (rows 35 14 100 200 16 32 64 128 256), losses := [] }

theorem u19282 : Upper (D 8) (R 8) [34,12,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19283 : Route 9 := (fun mask => (mask,id))

def c19283 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19283 : Upper (D 8) (R 8) [34,12,96,257] 13 := by
  apply FastRouting.sound _ _ [34,12,96,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19283 c19283
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8441
  · exact u8442
  · exact u8443
  · exact u8444
  · exact u8445
  · exact u8446

def r19284 : Route 9 := (fun mask => (mask,id))

def c19284 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19284 : Upper (D 8) (R 8) [34,12,96,272] 13 := by
  apply FastRouting.sound _ _ [34,12,96,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19284 c19284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8447
  · exact u8448
  · exact u8449
  · exact u8450
  · exact u8451
  · exact u8452

def b19285 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 100 296 209 241 209 209 465), lower := (rows 35 14 100 296 16 32 64 128 256), losses := [] }

theorem u19285 : Upper (D 8) (R 8) [34,12,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19286 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 328 177 177 241 177 433), lower := (rows 35 14 100 328 16 32 64 128 256), losses := [] }

theorem u19286 : Upper (D 8) (R 8) [34,12,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19287 : Route 9 := (fun mask => (mask,id))

def c19287 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19287 : Upper (D 8) (R 8) [34,12,96,384] 13 := by
  apply FastRouting.sound _ _ [34,12,96,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19287 c19287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8453
  · exact u8454
  · exact u8455
  · exact u8456
  · exact u8457
  · exact u8458

def b19288 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 35 14 196 200 305 305 369 433 305), lower := (rows 35 14 196 200 16 32 64 128 256), losses := [] }

theorem u19288 : Upper (D 8) (R 8) [34,12,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19289 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19289 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19289 : Upper (D 8) (R 8) [34,12,192,257] 13 := by
  apply FastRouting.sound _ _ [34,12,192,257] 13 (by decide) (choices 2) [33,65,96,192] r19289 c19289
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8459
  · exact u8460
  · exact u8461
  · exact u8462

def r19290 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19290 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19290 : Upper (D 8) (R 8) [34,12,192,272] 13 := by
  apply FastRouting.sound _ _ [34,12,192,272] 13 (by decide) (choices 2) [33,65,96,192] r19290 c19290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8463
  · exact u8464
  · exact u8465
  · exact u8466

def r19291 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19291 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19291 : Upper (D 8) (R 8) [34,12,192,288] 13 := by
  apply FastRouting.sound _ _ [34,12,192,288] 13 (by decide) (choices 2) [33,65,96,192] r19291 c19291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8467
  · exact u8468
  · exact u8469
  · exact u8470

def b19292 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 196 328 177 177 241 177 433), lower := (rows 35 14 196 328 16 32 64 128 256), losses := [] }

theorem u19292 : Upper (D 8) (R 8) [34,12,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19293 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 28 496 480 480 480 480), lower := (rows 35 67 13 28 16 32 64 128 256), losses := [] }

theorem u19293 : Upper (D 8) (R 8) [34,65,9,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19294 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 496 496 496 496 496), lower := (rows 35 67 13 44 16 32 64 128 256), losses := [] }

theorem u19294 : Upper (D 8) (R 8) [34,65,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19295 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 432 432 496 432 432), lower := (rows 35 67 13 76 16 32 64 128 256), losses := [] }

theorem u19295 : Upper (D 8) (R 8) [34,65,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19296 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 140 496 496 496 496 496), lower := (rows 35 67 13 140 16 32 64 128 256), losses := [] }

theorem u19296 : Upper (D 8) (R 8) [34,65,9,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19297 : PairBound 9 := { available := 500, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 500 500 500 500 500), lower := (rows 35 67 13 168 16 32 64 128 256), losses := [] }

theorem u19297 : Upper (D 8) (R 8) [34,65,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19298 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 200 436 436 500 436 436), lower := (rows 35 67 13 200 16 32 64 128 256), losses := [] }

theorem u19298 : Upper (D 8) (R 8) [34,65,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19299 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 268 240 240 240 240 496), lower := (rows 35 67 13 268 16 32 64 128 256), losses := [] }

theorem u19299 : Upper (D 8) (R 8) [34,65,9,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19300 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 296 244 244 244 244 500), lower := (rows 35 67 13 296 16 32 64 128 256), losses := [] }

theorem u19300 : Upper (D 8) (R 8) [34,65,9,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19301 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 328 180 180 244 180 436), lower := (rows 35 67 13 328 16 32 64 128 256), losses := [] }

theorem u19301 : Upper (D 8) (R 8) [34,65,9,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19302 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 392 244 244 244 244 500), lower := (rows 35 67 13 392 16 32 64 128 256), losses := [] }

theorem u19302 : Upper (D 8) (R 8) [34,65,9,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19303 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 44 504 488 488 488 488), lower := (rows 35 67 21 44 16 32 64 128 256), losses := [] }

theorem u19303 : Upper (D 8) (R 8) [34,65,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19304 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 76 440 424 488 424 424), lower := (rows 35 67 21 76 16 32 64 128 256), losses := [] }

theorem u19304 : Upper (D 8) (R 8) [34,65,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19305 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 140 504 488 488 488 488), lower := (rows 35 67 21 140 16 32 64 128 256), losses := [] }

theorem u19305 : Upper (D 8) (R 8) [34,65,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19306 : PairBound 9 := { available := 492, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 168 508 492 492 492 492), lower := (rows 35 67 21 168 16 32 64 128 256), losses := [] }

theorem u19306 : Upper (D 8) (R 8) [34,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19307 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 200 444 428 492 428 428), lower := (rows 35 67 21 200 16 32 64 128 256), losses := [] }

theorem u19307 : Upper (D 8) (R 8) [34,65,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19308 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 268 248 232 232 232 488), lower := (rows 35 67 21 268 16 32 64 128 256), losses := [] }

theorem u19308 : Upper (D 8) (R 8) [34,65,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19309 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 296 252 236 236 236 492), lower := (rows 35 67 21 296 16 32 64 128 256), losses := [] }

theorem u19309 : Upper (D 8) (R 8) [34,65,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19310 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 328 188 172 236 172 428), lower := (rows 35 67 21 328 16 32 64 128 256), losses := [] }

theorem u19310 : Upper (D 8) (R 8) [34,65,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19311 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 21 392 252 236 236 236 492), lower := (rows 35 67 21 392 16 32 64 128 256), losses := [] }

theorem u19311 : Upper (D 8) (R 8) [34,65,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19312 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 67 28 41 500 484 484 484 484), lower := (rows 35 67 28 41 16 32 64 128 256), losses := [] }

theorem u19312 : Upper (D 8) (R 8) [34,65,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19313_33 : Upper (D 8) (R 8) [34,65,24,36,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8540

def r19313 : Route 9 := (fun mask => (mask,id))

def c19313 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19313 : Upper (D 8) (R 8) [34,65,24,36] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19313 c19313
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19313_33
  · exact u8548
  · exact u8549
  · exact u8550
  · exact u8551
  · exact u8552
  · exact u8553
  · exact u8554
  · exact u8555
  · exact u8556

def b19314 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 436 420 484 420 420), lower := (rows 35 67 28 73 16 32 64 128 256), losses := [] }

theorem u19314 : Upper (D 8) (R 8) [34,65,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19315 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 433 417 481 417 417), lower := (rows 35 67 28 76 16 32 64 128 256), losses := [] }

theorem u19315 : Upper (D 8) (R 8) [34,65,24,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19316 : PairBound 9 := { available := 421, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 437 421 485 421 421), lower := (rows 35 67 28 104 16 32 64 128 256), losses := [] }

theorem u19316 : Upper (D 8) (R 8) [34,65,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19317 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 137 500 484 484 484 484), lower := (rows 35 67 28 137 16 32 64 128 256), losses := [] }

theorem u19317 : Upper (D 8) (R 8) [34,65,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19318_33 : Upper (D 8) (R 8) [34,65,24,132,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8541

theorem m19318_65 : Upper (D 8) (R 8) [34,65,24,132,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8557

theorem m19318_96 : Upper (D 8) (R 8) [34,65,24,132,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8565

theorem m19318_129 : Upper (D 8) (R 8) [34,65,24,132,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8570

def r19318 : Route 9 := (fun mask => (mask,id))

def c19318 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19318 : Upper (D 8) (R 8) [34,65,24,132] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19318 c19318
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19318_33
  · exact m19318_65
  · exact m19318_96
  · exact m19318_129
  · exact u8577
  · exact u8578
  · exact u8579
  · exact u8580
  · exact u8581
  · exact u8582

theorem m19319_5 : Upper (D 8) (R 8) [34,65,24,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8471

theorem m19319_33 : Upper (D 8) (R 8) [34,65,24,160,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8542

theorem m19319_36 : Upper (D 8) (R 8) [34,65,24,160,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8551

theorem m19319_65 : Upper (D 8) (R 8) [34,65,24,160,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8558

theorem m19319_68 : Upper (D 8) (R 8) [34,65,24,160,68] 13 :=
  permutation_upper _ _ _ [34,65,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8562

theorem m19319_96 : Upper (D 8) (R 8) [34,65,24,160,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8566

theorem m19319_129 : Upper (D 8) (R 8) [34,65,24,160,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8571

theorem m19319_132 : Upper (D 8) (R 8) [34,65,24,160,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8577

def r19319 : Route 9 := (fun mask => (mask,id))

def c19319 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19319 : Upper (D 8) (R 8) [34,65,24,160] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r19319 c19319
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19319_5
  · exact m19319_33
  · exact m19319_36
  · exact m19319_65
  · exact m19319_68
  · exact m19319_96
  · exact m19319_129
  · exact m19319_132
  · exact u8583
  · exact u8584
  · exact u8585
  · exact u8586
  · exact u8587
  · exact u8588
  · exact u8589

#print axioms u19319
end Delivery.IrregularNine14.P08
