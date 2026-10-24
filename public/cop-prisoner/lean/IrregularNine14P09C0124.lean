import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0073
import IrregularNine14P09C0074
import IrregularNine14P09C0075

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7440 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7440 : Upper (D 9) (R 9) [34,68,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96,384] 13 (by decide) (choices 1) [1,128] r7440 c7440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4401
  · exact u4402

def b7441 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 20, targets := 352 }], pairs := [(2,5),(2,6),(2,8),(4,5),(4,6)], upper := (rows 35 70 28 137 145 352 352 480 352), lower := (rows 35 70 28 137 145 32 64 128 256), losses := [] }

theorem u7441 : Upper (D 9) (R 9) [34,68,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7441 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7442 : Route 9 := (fun mask => (mask,id))

def c7442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7442 : Upper (D 9) (R 9) [34,68,24,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,160] 13 (by decide) (choices 1) [1,64,256] r7442 c7442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4403
  · exact u4404
  · exact u4405

def r7443 : Route 9 := (fun mask => (mask,id))

def c7443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7443 : Upper (D 9) (R 9) [34,68,24,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,192] 13 (by decide) (choices 1) [1,256] r7443 c7443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4406
  · exact u4407

theorem m7444_256 : Upper (D 9) (R 9) [34,68,24,129,257,256] 13 :=
  permutation_upper _ _ _ [34,68,24,129,257,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4409

def r7444 : Route 9 := (fun mask => (mask,id))

def c7444 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7444 : Upper (D 9) (R 9) [34,68,24,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,257] 13 (by decide) (choices 1) [64,128,256] r7444 c7444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4408
  · exact u4409
  · exact m7444_256

def r7445 : Route 9 := (fun mask => (mask,id))

def c7445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7445 : Upper (D 9) (R 9) [34,68,24,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,288] 13 (by decide) (choices 1) [1,64,128,256] r7445 c7445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4410
  · exact u4411
  · exact u4412
  · exact u4413

def r7446 : Route 9 := (fun mask => (mask,id))

def c7446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7446 : Upper (D 9) (R 9) [34,68,24,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,320] 13 (by decide) (choices 1) [1,128,256] r7446 c7446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4414
  · exact u4415
  · exact u4416

def r7447 : Route 9 := (fun mask => (mask,id))

def c7447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7447 : Upper (D 9) (R 9) [34,68,24,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,384] 13 (by decide) (choices 1) [1,64,256] r7447 c7447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4417
  · exact u4418
  · exact u4419

def b7448 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(1,7),(3,6),(4,5)], upper := (rows 35 70 28 168 208 289 321 385 257), lower := (rows 35 70 28 168 208 32 64 128 256), losses := [] }

theorem u7448 : Upper (D 9) (R 9) [34,68,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7448 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7449 : Route 9 := (fun mask => (mask,id))

def c7449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7449 : Upper (D 9) (R 9) [34,68,24,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,320] 13 (by decide) (choices 1) [1,128,256] r7449 c7449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4420
  · exact u4421
  · exact u4422

def r7450 : Route 9 := (fun mask => (mask,id))

def c7450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7450 : Upper (D 9) (R 9) [34,68,24,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,384] 13 (by decide) (choices 1) [1,64,256] r7450 c7450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4423
  · exact u4424
  · exact u4425

def r7451 : Route 9 := (fun mask => (mask,id))

def c7451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7451 : Upper (D 9) (R 9) [34,68,24,192,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,192,384] 13 (by decide) (choices 1) [1,256] r7451 c7451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4426
  · exact u4427

def b7452 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0),(4,5)], upper := (rows 35 70 28 392 400 97 97 225 353), lower := (rows 35 70 28 392 400 32 64 128 256), losses := [] }

theorem u7452 : Upper (D 9) (R 9) [34,68,24,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7452 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7453 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 486, targets := 1 },{ cop := 4, region := 428, targets := 64 }], pairs := [(1,0),(2,0),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 25 81 416 448 384 384), lower := (rows 35 70 44 25 81 32 64 128 256), losses := [] }

theorem u7453 : Upper (D 9) (R 9) [34,68,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7453 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7454 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 8, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(3,6),(3,7),(3,8),(4,5)], upper := (rows 35 70 44 25 145 480 448 448 448), lower := (rows 35 70 44 25 145 32 64 128 256), losses := [] }

theorem u7454 : Upper (D 9) (R 9) [34,68,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7454 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7455 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 417, targets := 64 },{ cop := 3, region := 420, targets := 64 }], pairs := [(0,6),(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 25 208 417 449 385 385), lower := (rows 35 70 44 25 208 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 29 0 73 137 265), good := (rows 475 86 478 473 208 0 64 128 256) }] }

theorem u7455 : Upper (D 9) (R 9) [34,68,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7455 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7456 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7456 : Upper (D 9) (R 9) [34,68,40,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,384] 13 (by decide) (choices 1) [1,64,128] r7456 c7456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4428
  · exact u4429
  · exact u4430

def b7457 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 44 88 145 417 449 385 385), lower := (rows 35 70 44 88 145 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 19 51 0 147 275), good := (rows 435 439 44 444 433 32 0 128 256) }] }

theorem u7457 : Upper (D 9) (R 9) [34,68,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7457 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7458 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7458 : Upper (D 9) (R 9) [34,68,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,80,384] 13 (by decide) (choices 1) [1,128] r7458 c7458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4431
  · exact u4432

def b7459 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 428, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(3,6),(4,5)], upper := (rows 35 70 44 137 81 432 464 400 400), lower := (rows 35 70 44 137 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 25 25 0 93 157 285), good := (rows 475 454 478 473 473 0 64 128 256) }] }

theorem u7459 : Upper (D 9) (R 9) [34,68,40,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7459 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7460 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 16, targets := 320 },{ cop := 4, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,8)], upper := (rows 35 70 44 137 145 368 336 464 336), lower := (rows 35 70 44 137 145 32 64 128 256), losses := [] }

theorem u7460 : Upper (D 9) (R 9) [34,68,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7461 : Route 9 := (fun mask => (mask,id))

def c7461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7461 : Upper (D 9) (R 9) [34,68,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,192] 13 (by decide) (choices 1) [1,16,256] r7461 c7461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4433
  · exact u4434
  · exact u4435

def r7462 : Route 9 := (fun mask => (mask,id))

def c7462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7462 : Upper (D 9) (R 9) [34,68,40,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,257] 13 (by decide) (choices 1) [16,64,128,256] r7462 c7462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4436
  · exact u4437
  · exact u4438
  · exact u4439

def r7463 : Route 9 := (fun mask => (mask,id))

def c7463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7463 : Upper (D 9) (R 9) [34,68,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,320] 13 (by decide) (choices 1) [1,16,128,256] r7463 c7463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4440
  · exact u4441
  · exact u4442
  · exact u4443

def r7464 : Route 9 := (fun mask => (mask,id))

def c7464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7464 : Upper (D 9) (R 9) [34,68,40,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,384] 13 (by decide) (choices 1) [1,16,64,256] r7464 c7464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4444
  · exact u4445
  · exact u4446
  · exact u4447

def b7465 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 428, targets := 64 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(3,6),(4,5)], upper := (rows 35 70 44 152 81 417 449 385 385), lower := (rows 35 70 44 152 81 32 64 128 256), losses := [] }

theorem u7465 : Upper (D 9) (R 9) [34,68,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7465 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7466 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 35 70 44 152 145 353 321 449 321), lower := (rows 35 70 44 152 145 32 64 128 256), losses := [] }

theorem u7466 : Upper (D 9) (R 9) [34,68,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7466 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7467 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 70 44 152 208 289 321 385 257), lower := (rows 35 70 44 152 208 32 64 128 256), losses := [] }

theorem u7467 : Upper (D 9) (R 9) [34,68,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7467 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7468 : Route 9 := (fun mask => (mask,id))

def c7468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7468 : Upper (D 9) (R 9) [34,68,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,257] 13 (by decide) (choices 1) [1,64,128,256] r7468 c7468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4448
  · exact u4449
  · exact u4450
  · exact u4451

def r7469 : Route 9 := (fun mask => (mask,id))

def c7469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7469 : Upper (D 9) (R 9) [34,68,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,320] 13 (by decide) (choices 1) [1,128,256] r7469 c7469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4452
  · exact u4453
  · exact u4454

def b7470 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 70 44 152 400 353 321 449 321), lower := (rows 35 70 44 152 400 32 64 128 256), losses := [] }

theorem u7470 : Upper (D 9) (R 9) [34,68,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7470 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7471 : Route 9 := (fun mask => (mask,id))

def c7471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7471 : Upper (D 9) (R 9) [34,68,40,192,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192,129] 13 (by decide) (choices 1) [1,16,256] r7471 c7471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4455
  · exact u4456
  · exact u4457

def r7472 : Route 9 := (fun mask => (mask,id))

def c7472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7472 : Upper (D 9) (R 9) [34,68,40,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192,257] 13 (by decide) (choices 1) [1,16,128,256] r7472 c7472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4458
  · exact u4459
  · exact u4460
  · exact u4461

def r7473 : Route 9 := (fun mask => (mask,id))

def c7473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7473 : Upper (D 9) (R 9) [34,68,40,192,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192,384] 13 (by decide) (choices 1) [1,16,256] r7473 c7473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4462
  · exact u4463
  · exact u4464

def r7474 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7474 : Upper (D 9) (R 9) [34,68,40,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,65] 13 (by decide) (choices 1) [1,16,128] r7474 c7474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4465
  · exact u4466
  · exact u4467

def r7475 : Route 9 := (fun mask => (mask,id))

def c7475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7475 : Upper (D 9) (R 9) [34,68,40,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,129] 13 (by decide) (choices 1) [1,16,64,256] r7475 c7475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4468
  · exact u4469
  · exact u4470
  · exact u4471

def r7476 : Route 9 := (fun mask => (mask,id))

def c7476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7476 : Upper (D 9) (R 9) [34,68,40,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,192] 13 (by decide) (choices 1) [1,16,256] r7476 c7476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4472
  · exact u4473
  · exact u4474

def b7477 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 70 44 392 400 113 81 209 337), lower := (rows 35 70 44 392 400 32 64 128 256), losses := [] }

theorem u7477 : Upper (D 9) (R 9) [34,68,40,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7477 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7478 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 24, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 35 70 133 25 56 480 448 448 448), lower := (rows 35 70 133 25 56 32 64 128 256), losses := [] }

theorem u7478 : Upper (D 9) (R 9) [34,68,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7478 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7479 : Route 9 := (fun mask => (mask,id))

def c7479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7479 : Upper (D 9) (R 9) [34,68,129,17,72] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,72] 13 (by decide) (choices 1) [128,256] r7479 c7479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4475
  · exact u4476

def r7480 : Route 9 := (fun mask => (mask,id))

def c7480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7480 : Upper (D 9) (R 9) [34,68,129,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,96] 13 (by decide) (choices 1) [8,128,256] r7480 c7480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4477
  · exact u4478
  · exact u4479

def b7481 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 24, targets := 352 }], pairs := [(3,5),(3,6),(3,8),(4,5),(4,6)], upper := (rows 35 70 133 25 152 352 352 480 352), lower := (rows 35 70 133 25 152 32 64 128 256), losses := [] }

theorem u7481 : Upper (D 9) (R 9) [34,68,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7481 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7482 : Route 9 := (fun mask => (mask,id))

def c7482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7482 : Upper (D 9) (R 9) [34,68,129,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,160] 13 (by decide) (choices 1) [8,64,256] r7482 c7482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4480
  · exact u4481
  · exact u4482

def r7483 : Route 9 := (fun mask => (mask,id))

def c7483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7483 : Upper (D 9) (R 9) [34,68,129,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,192] 13 (by decide) (choices 1) [8,256] r7483 c7483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4483
  · exact u4484

def r7484 : Route 9 := (fun mask => (mask,id))

def c7484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7484 : Upper (D 9) (R 9) [34,68,129,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,264] 13 (by decide) (choices 1) [64,128,256] r7484 c7484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4485
  · exact u4486
  · exact u4487

def r7485 : Route 9 := (fun mask => (mask,id))

def c7485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u7485 : Upper (D 9) (R 9) [34,68,129,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,288] 13 (by decide) (choices 1) [8,64,128,256] r7485 c7485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4488
  · exact u4489
  · exact u4490
  · exact u4491

def r7486 : Route 9 := (fun mask => (mask,id))

def c7486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7486 : Upper (D 9) (R 9) [34,68,129,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,320] 13 (by decide) (choices 1) [8,128,256] r7486 c7486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4492
  · exact u4493
  · exact u4494

def r7487 : Route 9 := (fun mask => (mask,id))

def c7487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7487 : Upper (D 9) (R 9) [34,68,129,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,384] 13 (by decide) (choices 1) [8,64,256] r7487 c7487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4495
  · exact u4496
  · exact u4497

def b7488 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 133 41 88 432 464 400 400), lower := (rows 35 70 133 41 88 32 64 128 256), losses := [] }

theorem u7488 : Upper (D 9) (R 9) [34,68,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7488 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7489 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 133 41 152 368 336 464 336), lower := (rows 35 70 133 41 152 32 64 128 256), losses := [] }

theorem u7489 : Upper (D 9) (R 9) [34,68,129,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7489 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7490 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 133 41 208 312 344 408 280), lower := (rows 35 70 133 41 208 32 64 128 256), losses := [] }

theorem u7490 : Upper (D 9) (R 9) [34,68,129,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7490 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7491 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 133 41 280 496 464 464 464), lower := (rows 35 70 133 41 280 32 64 128 256), losses := [] }

theorem u7491 : Upper (D 9) (R 9) [34,68,129,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7491 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7492 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 133 41 336 440 472 408 408), lower := (rows 35 70 133 41 336 32 64 128 256), losses := [] }

theorem u7492 : Upper (D 9) (R 9) [34,68,129,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7492 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7493 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 133 41 400 376 344 472 344), lower := (rows 35 70 133 41 400 32 64 128 256), losses := [] }

theorem u7493 : Upper (D 9) (R 9) [34,68,129,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7493 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7494 : Route 9 := (fun mask => (mask,id))

def c7494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7494 : Upper (D 9) (R 9) [34,68,129,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,65] 13 (by decide) (choices 1) [8,128,256] r7494 c7494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4498
  · exact u4499
  · exact u4500

def r7495 : Route 9 := (fun mask => (mask,id))

def c7495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7495 : Upper (D 9) (R 9) [34,68,129,48,72] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,72] 13 (by decide) (choices 1) [1,128,256] r7495 c7495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4501
  · exact u4502
  · exact u4503

def b7496 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 16, targets := 352 },{ cop := 4, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6),(4,8)], upper := (rows 35 70 133 56 145 360 328 456 328), lower := (rows 35 70 133 56 145 32 64 128 256), losses := [] }

theorem u7496 : Upper (D 9) (R 9) [34,68,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7496 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7497 : Route 9 := (fun mask => (mask,id))

def c7497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7497 : Upper (D 9) (R 9) [34,68,129,48,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,136] 13 (by decide) (choices 1) [1,64,256] r7497 c7497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4504
  · exact u4505
  · exact u4506

def r7498 : Route 9 := (fun mask => (mask,id))

def c7498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7498 : Upper (D 9) (R 9) [34,68,129,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,192] 13 (by decide) (choices 1) [1,8,256] r7498 c7498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4507
  · exact u4508
  · exact u4509

def r7499 : Route 9 := (fun mask => (mask,id))

def c7499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u7499 : Upper (D 9) (R 9) [34,68,129,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,257] 13 (by decide) (choices 1) [8,64,128,256] r7499 c7499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4510
  · exact u4511
  · exact u4512
  · exact u4513

#print axioms u7499
end Delivery.IrregularNine14.P09
