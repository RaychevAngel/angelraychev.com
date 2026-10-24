import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0206
import IrregularNine14P07C0207
import IrregularNine14P07C0208

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30480 : Route 9 := (fun mask => (mask,id))

def c30480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30480 : Upper (D 7) (R 7) [6,33,72,288,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,66] 13 (by decide) (choices 1) [1,16,128] r30480 c30480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12400
  · exact u12401
  · exact u12402

def r30481 : Route 9 := (fun mask => (mask,id))

def c30481 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30481 : Upper (D 7) (R 7) [6,33,72,288,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,129] 13 (by decide) (choices 1) [2,16,64,128] r30481 c30481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12403
  · exact u12404
  · exact u12405
  · exact u12406

def r30482 : Route 9 := (fun mask => (mask,id))

def c30482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30482 : Upper (D 7) (R 7) [6,33,72,288,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,130] 13 (by decide) (choices 1) [1,16,64,128] r30482 c30482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12407
  · exact u12408
  · exact u12409
  · exact u12410

def r30483 : Route 9 := (fun mask => (mask,id))

def c30483 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30483 : Upper (D 7) (R 7) [6,33,72,288,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,192] 13 (by decide) (choices 1) [1,2,16,128] r30483 c30483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12411
  · exact u12412
  · exact u12413
  · exact u12414

def b30484 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 76 392 19 240 240 240 496), lower := (rows 7 35 76 392 19 32 64 128 256), losses := [] }

theorem u30484 : Upper (D 7) (R 7) [6,33,72,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30485 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 76 392 49 242 210 210 466), lower := (rows 7 35 76 392 49 32 64 128 256), losses := [] }

theorem u30485 : Upper (D 7) (R 7) [6,33,72,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30486 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 35 76 392 50 241 209 209 465), lower := (rows 7 35 76 392 50 32 64 128 256), losses := [] }

theorem u30486 : Upper (D 7) (R 7) [6,33,72,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30487 : Route 9 := (fun mask => (mask,id))

def c30487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30487 : Upper (D 7) (R 7) [6,33,72,384,65] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,65] 13 (by decide) (choices 1) [2,16,128] r30487 c30487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12415
  · exact u12416
  · exact u12417

def r30488 : Route 9 := (fun mask => (mask,id))

def c30488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30488 : Upper (D 7) (R 7) [6,33,72,384,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,66] 13 (by decide) (choices 1) [1,16,128] r30488 c30488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12418
  · exact u12419
  · exact u12420

def r30489 : Route 9 := (fun mask => (mask,id))

def c30489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30489 : Upper (D 7) (R 7) [6,33,72,384,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,96] 13 (by decide) (choices 1) [1,2,16,128] r30489 c30489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12421
  · exact u12422
  · exact u12423
  · exact u12424

def r30490 : Route 9 := (fun mask => (mask,id))

def c30490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30490 : Upper (D 7) (R 7) [6,33,72,384,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,129] 13 (by decide) (choices 1) [2,16,64] r30490 c30490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12425
  · exact u12426
  · exact u12427

def r30491 : Route 9 := (fun mask => (mask,id))

def c30491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30491 : Upper (D 7) (R 7) [6,33,72,384,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,130] 13 (by decide) (choices 1) [1,16,64] r30491 c30491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12428
  · exact u12429
  · exact u12430

def r30492 : Route 9 := (fun mask => (mask,id))

def c30492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30492 : Upper (D 7) (R 7) [6,33,72,384,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,160] 13 (by decide) (choices 1) [1,2,16,64] r30492 c30492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12431
  · exact u12432
  · exact u12433
  · exact u12434

def r30493 : Route 9 := (fun mask => (mask,id))

def c30493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30493 : Upper (D 7) (R 7) [6,33,72,384,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,192] 13 (by decide) (choices 1) [1,2,16] r30493 c30493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12435
  · exact u12436
  · exact u12437

def b30494 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 196 11 56 496 464 464 464), lower := (rows 7 35 196 11 56 32 64 128 256), losses := [] }

theorem u30494 : Upper (D 7) (R 7) [6,33,192,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30495 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 196 11 88 432 496 432 432), lower := (rows 7 35 196 11 88 32 64 128 256), losses := [] }

theorem u30495 : Upper (D 7) (R 7) [6,33,192,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30496 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 196 11 112 440 472 408 408), lower := (rows 7 35 196 11 112 32 64 128 256), losses := [] }

theorem u30496 : Upper (D 7) (R 7) [6,33,192,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30497 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 196 11 280 240 240 240 496), lower := (rows 7 35 196 11 280 32 64 128 256), losses := [] }

theorem u30497 : Upper (D 7) (R 7) [6,33,192,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30498 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 196 11 304 248 216 216 472), lower := (rows 7 35 196 11 304 32 64 128 256), losses := [] }

theorem u30498 : Upper (D 7) (R 7) [6,33,192,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30499 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 196 11 336 184 248 184 440), lower := (rows 7 35 196 11 336 32 64 128 256), losses := [] }

theorem u30499 : Upper (D 7) (R 7) [6,33,192,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30500 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 35 196 25 26 480 480 480 480), lower := (rows 7 35 196 25 26 32 64 128 256), losses := [] }

theorem u30500 : Upper (D 7) (R 7) [6,33,192,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30501 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 196 25 50 488 456 456 456), lower := (rows 7 35 196 25 50 32 64 128 256), losses := [] }

theorem u30501 : Upper (D 7) (R 7) [6,33,192,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30502 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 196 25 56 482 450 450 450), lower := (rows 7 35 196 25 56 32 64 128 256), losses := [] }

theorem u30502 : Upper (D 7) (R 7) [6,33,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30503 : Route 9 := (fun mask => (mask,id))

def c30503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30503 : Upper (D 7) (R 7) [6,33,192,17,66] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,66] 13 (by decide) (choices 1) [8,128,256] r30503 c30503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12438
  · exact u12439
  · exact u12440

def b30504 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 0, region := 484, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 196 25 88 418 482 418 418), lower := (rows 7 35 196 25 88 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 35 67 131 259), good := (rows 486 486 196 508 92 32 64 128 256) }] }

theorem u30504 : Upper (D 7) (R 7) [6,33,192,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30505 : Route 9 := (fun mask => (mask,id))

def c30505 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30505 : Upper (D 7) (R 7) [6,33,192,17,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,96] 13 (by decide) (choices 1) [2,8,128,256] r30505 c30505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12441
  · exact u12442
  · exact u12443
  · exact u12444

def b30506 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 35 196 25 208 298 362 426 298), lower := (rows 7 35 196 25 208 32 64 128 256), losses := [] }

theorem u30506 : Upper (D 7) (R 7) [6,33,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30507 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30507 : Upper (D 7) (R 7) [6,33,192,17,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,258] 13 (by decide) (choices 1) [8,64] r30507 c30507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12445
  · exact u12446

def r30508 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30508 : Upper (D 7) (R 7) [6,33,192,17,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,264] 13 (by decide) (choices 1) [2,64] r30508 c30508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12447
  · exact u12448

def r30509 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30509 : Upper (D 7) (R 7) [6,33,192,17,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,288] 13 (by decide) (choices 1) [2,8,64] r30509 c30509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12449
  · exact u12450
  · exact u12451

def r30510 : Route 9 := (fun mask => (mask,id))

def c30510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30510 : Upper (D 7) (R 7) [6,33,192,17,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,320] 13 (by decide) (choices 1) [2,8,128] r30510 c30510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12452
  · exact u12453
  · exact u12454

def b30511 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 196 26 49 488 456 456 456), lower := (rows 7 35 196 26 49 32 64 128 256), losses := [] }

theorem u30511 : Upper (D 7) (R 7) [6,33,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30512 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 7 35 196 26 56 481 449 449 449), lower := (rows 7 35 196 26 56 32 64 128 256), losses := [] }

theorem u30512 : Upper (D 7) (R 7) [6,33,192,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30513 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 7 35 196 26 81 424 488 424 424), lower := (rows 7 35 196 26 81 32 64 128 256), losses := [] }

theorem u30513 : Upper (D 7) (R 7) [6,33,192,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30514 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 7 35 196 26 88 417 481 417 417), lower := (rows 7 35 196 26 88 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 35 67 131 259), good := (rows 485 485 196 508 92 32 64 128 256) }] }

theorem u30514 : Upper (D 7) (R 7) [6,33,192,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30515 : Route 9 := (fun mask => (mask,id))

def c30515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30515 : Upper (D 7) (R 7) [6,33,192,18,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,96] 13 (by decide) (choices 1) [1,8,128,256] r30515 c30515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12455
  · exact u12456
  · exact u12457
  · exact u12458

def b30516 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 35 196 26 208 297 361 425 297), lower := (rows 7 35 196 26 208 32 64 128 256), losses := [] }

theorem u30516 : Upper (D 7) (R 7) [6,33,192,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30517 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30517 : Upper (D 7) (R 7) [6,33,192,18,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,257] 13 (by decide) (choices 1) [8,64] r30517 c30517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12459
  · exact u12460

def r30518 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30518 : Upper (D 7) (R 7) [6,33,192,18,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,264] 13 (by decide) (choices 1) [1,64] r30518 c30518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12461
  · exact u12462

def r30519 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30519 : Upper (D 7) (R 7) [6,33,192,18,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,288] 13 (by decide) (choices 1) [1,8,64] r30519 c30519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12463
  · exact u12464
  · exact u12465

def r30520 : Route 9 := (fun mask => (mask,id))

def c30520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30520 : Upper (D 7) (R 7) [6,33,192,18,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,320] 13 (by decide) (choices 1) [1,8,128] r30520 c30520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12466
  · exact u12467
  · exact u12468

def b30521 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 196 41 82 440 472 408 408), lower := (rows 7 35 196 41 82 32 64 128 256), losses := [] }

theorem u30521 : Upper (D 7) (R 7) [6,33,192,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30522 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 196 41 88 434 466 402 402), lower := (rows 7 35 196 41 88 32 64 128 256), losses := [] }

theorem u30522 : Upper (D 7) (R 7) [6,33,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30523 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 196 41 274 248 216 216 472), lower := (rows 7 35 196 41 274 32 64 128 256), losses := [] }

theorem u30523 : Upper (D 7) (R 7) [6,33,192,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30524 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 196 41 280 242 210 210 466), lower := (rows 7 35 196 41 280 32 64 128 256), losses := [] }

theorem u30524 : Upper (D 7) (R 7) [6,33,192,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30525 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 196 41 336 186 218 154 410), lower := (rows 7 35 196 41 336 32 64 128 256), losses := [] }

theorem u30525 : Upper (D 7) (R 7) [6,33,192,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30526 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 196 42 81 440 472 408 408), lower := (rows 7 35 196 42 81 32 64 128 256), losses := [] }

theorem u30526 : Upper (D 7) (R 7) [6,33,192,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30527 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 196 42 88 433 465 401 401), lower := (rows 7 35 196 42 88 32 64 128 256), losses := [] }

theorem u30527 : Upper (D 7) (R 7) [6,33,192,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30528 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 196 42 273 248 216 216 472), lower := (rows 7 35 196 42 273 32 64 128 256), losses := [] }

theorem u30528 : Upper (D 7) (R 7) [6,33,192,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30529 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 196 42 280 241 209 209 465), lower := (rows 7 35 196 42 280 32 64 128 256), losses := [] }

theorem u30529 : Upper (D 7) (R 7) [6,33,192,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30530 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 196 42 336 185 217 153 409), lower := (rows 7 35 196 42 336 32 64 128 256), losses := [] }

theorem u30530 : Upper (D 7) (R 7) [6,33,192,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30531 : Route 9 := (fun mask => (mask,id))

def c30531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30531 : Upper (D 7) (R 7) [6,33,192,48,65] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,65] 13 (by decide) (choices 1) [2,8,128,256] r30531 c30531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12469
  · exact u12470
  · exact u12471
  · exact u12472

def r30532 : Route 9 := (fun mask => (mask,id))

def c30532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30532 : Upper (D 7) (R 7) [6,33,192,48,66] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,66] 13 (by decide) (choices 1) [1,8,128,256] r30532 c30532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12473
  · exact u12474
  · exact u12475
  · exact u12476

def b30533 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,5),(0,6),(1,6),(2,5)], upper := (rows 7 35 196 56 88 419 451 387 387), lower := (rows 7 35 196 56 88 32 64 128 256), losses := [] }

theorem u30533 : Upper (D 7) (R 7) [6,33,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30534 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 35 196 56 208 299 331 395 267), lower := (rows 7 35 196 56 208 32 64 128 256), losses := [] }

theorem u30534 : Upper (D 7) (R 7) [6,33,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30535 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30535 : Upper (D 7) (R 7) [6,33,192,48,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,257] 13 (by decide) (choices 1) [2,8,64] r30535 c30535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12477
  · exact u12478
  · exact u12479

def r30536 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30536 : Upper (D 7) (R 7) [6,33,192,48,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,258] 13 (by decide) (choices 1) [1,8,64] r30536 c30536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12480
  · exact u12481
  · exact u12482

def r30537 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30537 : Upper (D 7) (R 7) [6,33,192,48,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,264] 13 (by decide) (choices 1) [1,2,64] r30537 c30537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12483
  · exact u12484
  · exact u12485

def r30538 : Route 9 := (fun mask => (mask,id))

def c30538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30538 : Upper (D 7) (R 7) [6,33,192,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,320] 13 (by decide) (choices 1) [1,2,8,128] r30538 c30538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12486
  · exact u12487
  · exact u12488
  · exact u12489

def r30539 : Route 9 := (fun mask => (mask,id))

def c30539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30539 : Upper (D 7) (R 7) [6,33,192,65,130] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,130] 13 (by decide) (choices 1) [8,16,256] r30539 c30539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12490
  · exact u12491
  · exact u12492

#print axioms u30539
end Delivery.IrregularNine14.P07
