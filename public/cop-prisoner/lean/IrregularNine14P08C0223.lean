import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0073
import IrregularNine14P08C0074

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13380 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 164 74 176 313 345 409 281), lower := (rows 97 7 164 74 176 32 64 128 256), losses := [] }

theorem u13380 : Upper (D 8) (R 8) [96,5,160,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13381 : Route 9 := (fun mask => (mask,id))

def c13381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13381 : Upper (D 8) (R 8) [96,5,160,66,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,257] 13 (by decide) (choices 1) [8,16,128] r13381 c13381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4405
  · exact u4406
  · exact u4407

def r13382 : Route 9 := (fun mask => (mask,id))

def c13382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13382 : Upper (D 8) (R 8) [96,5,160,66,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,264] 13 (by decide) (choices 1) [1,16,128] r13382 c13382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4408
  · exact u4409
  · exact u4410

def r13383 : Route 9 := (fun mask => (mask,id))

def c13383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13383 : Upper (D 8) (R 8) [96,5,160,66,288] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,288] 13 (by decide) (choices 1) [1,8,16,128] r13383 c13383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4411
  · exact u4412
  · exact u4413
  · exact u4414

def r13384 : Route 9 := (fun mask => (mask,id))

def c13384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13384 : Upper (D 8) (R 8) [96,5,160,66,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,384] 13 (by decide) (choices 1) [1,8,16] r13384 c13384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4415
  · exact u4416
  · exact u4417

def r13385 : Route 9 := (fun mask => (mask,id))

def c13385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u13385 : Upper (D 8) (R 8) [96,5,160,80,129] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,129] 13 (by decide) (choices 1) [2,8,256] r13385 c13385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4418
  · exact u4419
  · exact u4420

def b13386 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 88 146 297 361 425 297), lower := (rows 97 7 164 88 146 32 64 128 256), losses := [] }

theorem u13386 : Upper (D 8) (R 8) [96,5,160,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13387 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 88 152 291 355 419 291), lower := (rows 97 7 164 88 152 32 64 128 256), losses := [] }

theorem u13387 : Upper (D 8) (R 8) [96,5,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13388 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 164 88 176 299 331 395 267), lower := (rows 97 7 164 88 176 32 64 128 256), losses := [] }

theorem u13388 : Upper (D 8) (R 8) [96,5,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13389 : Route 9 := (fun mask => (mask,id))

def c13389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13389 : Upper (D 8) (R 8) [96,5,160,80,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,257] 13 (by decide) (choices 1) [2,8,128] r13389 c13389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4421
  · exact u4422
  · exact u4423

def r13390 : Route 9 := (fun mask => (mask,id))

def c13390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13390 : Upper (D 8) (R 8) [96,5,160,80,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,258] 13 (by decide) (choices 1) [1,8,128] r13390 c13390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4424
  · exact u4425
  · exact u4426

def b13391 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 88 280 163 227 163 419), lower := (rows 97 7 164 88 280 32 64 128 256), losses := [] }

theorem u13391 : Upper (D 8) (R 8) [96,5,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13392 : Route 9 := (fun mask => (mask,id))

def c13392 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13392 : Upper (D 8) (R 8) [96,5,160,80,288] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,288] 13 (by decide) (choices 1) [1,2,8,128] r13392 c13392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4427
  · exact u4428
  · exact u4429
  · exact u4430

def r13393 : Route 9 := (fun mask => (mask,id))

def c13393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13393 : Upper (D 8) (R 8) [96,5,160,80,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,384] 13 (by decide) (choices 1) [1,2,8] r13393 c13393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4431
  · exact u4432
  · exact u4433

def b13394 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 104 145 314 346 410 282), lower := (rows 97 7 164 104 145 32 64 128 256), losses := [] }

theorem u13394 : Upper (D 8) (R 8) [96,5,160,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13395 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 104 152 307 339 403 275), lower := (rows 97 7 164 104 152 32 64 128 256), losses := [] }

theorem u13395 : Upper (D 8) (R 8) [96,5,160,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13396 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 104 273 186 218 154 410), lower := (rows 97 7 164 104 273 32 64 128 256), losses := [] }

theorem u13396 : Upper (D 8) (R 8) [96,5,160,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13397 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 104 274 185 217 153 409), lower := (rows 97 7 164 104 274 32 64 128 256), losses := [] }

theorem u13397 : Upper (D 8) (R 8) [96,5,160,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13398 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 104 280 179 211 147 403), lower := (rows 97 7 164 104 280 32 64 128 256), losses := [] }

theorem u13398 : Upper (D 8) (R 8) [96,5,160,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13399 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 104 400 59 91 155 283), lower := (rows 97 7 164 104 400 32 64 128 256), losses := [] }

theorem u13399 : Upper (D 8) (R 8) [96,5,160,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13400 : Route 9 := (fun mask => (mask,id))

def c13400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13400 : Upper (D 8) (R 8) [96,5,160,129,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,258] 13 (by decide) (choices 1) [8,16,64] r13400 c13400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4434
  · exact u4435
  · exact u4436

def r13401 : Route 9 := (fun mask => (mask,id))

def c13401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13401 : Upper (D 8) (R 8) [96,5,160,129,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,264] 13 (by decide) (choices 1) [2,16,64] r13401 c13401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4437
  · exact u4438
  · exact u4439

def r13402 : Route 9 := (fun mask => (mask,id))

def c13402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13402 : Upper (D 8) (R 8) [96,5,160,129,288] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,288] 13 (by decide) (choices 1) [2,8,16,64] r13402 c13402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4440
  · exact u4441
  · exact u4442
  · exact u4443

def r13403 : Route 9 := (fun mask => (mask,id))

def c13403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13403 : Upper (D 8) (R 8) [96,5,160,129,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,320] 13 (by decide) (choices 1) [2,8,16] r13403 c13403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4444
  · exact u4445
  · exact u4446

def b13404 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 138 273 120 120 248 376), lower := (rows 97 7 164 138 273 32 64 128 256), losses := [] }

theorem u13404 : Upper (D 8) (R 8) [96,5,160,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13405 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 138 280 113 113 241 369), lower := (rows 97 7 164 138 280 32 64 128 256), losses := [] }

theorem u13405 : Upper (D 8) (R 8) [96,5,160,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13406 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 138 304 121 89 217 345), lower := (rows 97 7 164 138 304 32 64 128 256), losses := [] }

theorem u13406 : Upper (D 8) (R 8) [96,5,160,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13407 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 138 336 57 121 185 313), lower := (rows 97 7 164 138 336 32 64 128 256), losses := [] }

theorem u13407 : Upper (D 8) (R 8) [96,5,160,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13408 : Route 9 := (fun mask => (mask,id))

def c13408 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13408 : Upper (D 8) (R 8) [96,5,160,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,257] 13 (by decide) (choices 1) [2,8,64] r13408 c13408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4447
  · exact u4448
  · exact u4449

def b13409 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 152 274 105 105 233 361), lower := (rows 97 7 164 152 274 32 64 128 256), losses := [] }

theorem u13409 : Upper (D 8) (R 8) [96,5,160,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13410 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 152 280 99 99 227 355), lower := (rows 97 7 164 152 280 32 64 128 256), losses := [] }

theorem u13410 : Upper (D 8) (R 8) [96,5,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13411 : Route 9 := (fun mask => (mask,id))

def c13411 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13411 : Upper (D 8) (R 8) [96,5,160,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,288] 13 (by decide) (choices 1) [1,2,8,64] r13411 c13411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4450
  · exact u4451
  · exact u4452
  · exact u4453

def r13412 : Route 9 := (fun mask => (mask,id))

def c13412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13412 : Upper (D 8) (R 8) [96,5,160,144,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,320] 13 (by decide) (choices 1) [1,2,8] r13412 c13412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4454
  · exact u4455
  · exact u4456

def b13413 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 168 273 122 90 218 346), lower := (rows 97 7 164 168 273 32 64 128 256), losses := [] }

theorem u13413 : Upper (D 8) (R 8) [96,5,160,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13414 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 168 274 121 89 217 345), lower := (rows 97 7 164 168 274 32 64 128 256), losses := [] }

theorem u13414 : Upper (D 8) (R 8) [96,5,160,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13415 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 168 280 115 83 211 339), lower := (rows 97 7 164 168 280 32 64 128 256), losses := [] }

theorem u13415 : Upper (D 8) (R 8) [96,5,160,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13416 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 168 336 59 91 155 283), lower := (rows 97 7 164 168 336 32 64 128 256), losses := [] }

theorem u13416 : Upper (D 8) (R 8) [96,5,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13417 : Route 9 := (fun mask => (mask,id))

def c13417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13417 : Upper (D 8) (R 8) [96,5,160,192,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,257] 13 (by decide) (choices 1) [2,8,16] r13417 c13417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4457
  · exact u4458
  · exact u4459

def r13418 : Route 9 := (fun mask => (mask,id))

def c13418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13418 : Upper (D 8) (R 8) [96,5,160,192,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,258] 13 (by decide) (choices 1) [1,8,16] r13418 c13418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4460
  · exact u4461
  · exact u4462

def r13419 : Route 9 := (fun mask => (mask,id))

def c13419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13419 : Upper (D 8) (R 8) [96,5,160,192,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,264] 13 (by decide) (choices 1) [1,2,16] r13419 c13419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4463
  · exact u4464
  · exact u4465

def r13420 : Route 9 := (fun mask => (mask,id))

def c13420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13420 : Upper (D 8) (R 8) [96,5,160,192,288] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,288] 13 (by decide) (choices 1) [1,2,8,16] r13420 c13420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4466
  · exact u4467
  · exact u4468
  · exact u4469

def b13421 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 25 274 168 232 168 424), lower := (rows 97 7 196 25 274 32 64 128 256), losses := [] }

theorem u13421 : Upper (D 8) (R 8) [96,5,192,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13422 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 25 280 162 226 162 418), lower := (rows 97 7 196 25 280 32 64 128 256), losses := [] }

theorem u13422 : Upper (D 8) (R 8) [96,5,192,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13423 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 25 304 170 234 170 426), lower := (rows 97 7 196 25 304 32 64 128 256), losses := [] }

theorem u13423 : Upper (D 8) (R 8) [96,5,192,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13424 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 25 400 42 106 170 298), lower := (rows 97 7 196 25 400 32 64 128 256), losses := [] }

theorem u13424 : Upper (D 8) (R 8) [96,5,192,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13425 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 56 417 481 417 417), lower := (rows 97 7 196 26 56 32 64 128 256), losses := [] }

theorem u13425 : Upper (D 8) (R 8) [96,5,192,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13426 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 145 296 360 424 296), lower := (rows 97 7 196 26 145 32 64 128 256), losses := [] }

theorem u13426 : Upper (D 8) (R 8) [96,5,192,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13427 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 152 289 353 417 289), lower := (rows 97 7 196 26 152 32 64 128 256), losses := [] }

theorem u13427 : Upper (D 8) (R 8) [96,5,192,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13428 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 176 297 361 425 297), lower := (rows 97 7 196 26 176 32 64 128 256), losses := [] }

theorem u13428 : Upper (D 8) (R 8) [96,5,192,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13429 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 273 168 232 168 424), lower := (rows 97 7 196 26 273 32 64 128 256), losses := [] }

theorem u13429 : Upper (D 8) (R 8) [96,5,192,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13430 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 280 161 225 161 417), lower := (rows 97 7 196 26 280 32 64 128 256), losses := [] }

theorem u13430 : Upper (D 8) (R 8) [96,5,192,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13431 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 304 169 233 169 425), lower := (rows 97 7 196 26 304 32 64 128 256), losses := [] }

theorem u13431 : Upper (D 8) (R 8) [96,5,192,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13432 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 26 400 41 105 169 297), lower := (rows 97 7 196 26 400 32 64 128 256), losses := [] }

theorem u13432 : Upper (D 8) (R 8) [96,5,192,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13433 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 42 145 312 376 440 312), lower := (rows 97 7 196 42 145 32 64 128 256), losses := [] }

theorem u13433 : Upper (D 8) (R 8) [96,5,192,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13434 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 42 152 305 369 433 305), lower := (rows 97 7 196 42 152 32 64 128 256), losses := [] }

theorem u13434 : Upper (D 8) (R 8) [96,5,192,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13435 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 42 176 313 345 409 281), lower := (rows 97 7 196 42 176 32 64 128 256), losses := [] }

theorem u13435 : Upper (D 8) (R 8) [96,5,192,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13436 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 42 273 184 248 184 440), lower := (rows 97 7 196 42 273 32 64 128 256), losses := [] }

theorem u13436 : Upper (D 8) (R 8) [96,5,192,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13437 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 42 280 177 241 177 433), lower := (rows 97 7 196 42 280 32 64 128 256), losses := [] }

theorem u13437 : Upper (D 8) (R 8) [96,5,192,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13438 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 42 304 185 217 153 409), lower := (rows 97 7 196 42 304 32 64 128 256), losses := [] }

theorem u13438 : Upper (D 8) (R 8) [96,5,192,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13439 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 42 400 57 121 185 313), lower := (rows 97 7 196 42 400 32 64 128 256), losses := [] }

theorem u13439 : Upper (D 8) (R 8) [96,5,192,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13439
end Delivery.IrregularNine14.P08
