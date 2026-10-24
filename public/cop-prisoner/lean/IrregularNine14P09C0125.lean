import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0075
import IrregularNine14P09C0076
import IrregularNine14P09C0077

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7500 : Route 9 := (fun mask => (mask,id))

def c7500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7500 : Upper (D 9) (R 9) [34,68,129,48,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,264] 13 (by decide) (choices 1) [1,64,128,256] r7500 c7500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4514
  · exact u4515
  · exact u4516
  · exact u4517

def r7501 : Route 9 := (fun mask => (mask,id))

def c7501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7501 : Upper (D 9) (R 9) [34,68,129,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,320] 13 (by decide) (choices 1) [1,8,128,256] r7501 c7501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4518
  · exact u4519
  · exact u4520
  · exact u4521

def r7502 : Route 9 := (fun mask => (mask,id))

def c7502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7502 : Upper (D 9) (R 9) [34,68,129,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,384] 13 (by decide) (choices 1) [1,8,64,256] r7502 c7502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4522
  · exact u4523
  · exact u4524
  · exact u4525

def r7503 : Route 9 := (fun mask => (mask,id))

def c7503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7503 : Upper (D 9) (R 9) [34,68,129,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,136] 13 (by decide) (choices 1) [16,256] r7503 c7503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4526
  · exact u4527

def r7504 : Route 9 := (fun mask => (mask,id))

def c7504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7504 : Upper (D 9) (R 9) [34,68,129,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,160] 13 (by decide) (choices 1) [8,16,256] r7504 c7504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4528
  · exact u4529
  · exact u4530

def r7505 : Route 9 := (fun mask => (mask,id))

def c7505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7505 : Upper (D 9) (R 9) [34,68,129,65,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,264] 13 (by decide) (choices 1) [16,128,256] r7505 c7505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4531
  · exact u4532
  · exact u4533

def r7506 : Route 9 := (fun mask => (mask,id))

def c7506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u7506 : Upper (D 9) (R 9) [34,68,129,65,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,288] 13 (by decide) (choices 1) [8,16,128,256] r7506 c7506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4534
  · exact u4535
  · exact u4536
  · exact u4537

def r7507 : Route 9 := (fun mask => (mask,id))

def c7507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7507 : Upper (D 9) (R 9) [34,68,129,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,384] 13 (by decide) (choices 1) [8,16,256] r7507 c7507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4538
  · exact u4539
  · exact u4540

def b7508 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 16, targets := 352 },{ cop := 4, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6),(4,8)], upper := (rows 35 70 133 88 145 296 360 424 296), lower := (rows 35 70 133 88 145 32 64 128 256), losses := [] }

theorem u7508 : Upper (D 9) (R 9) [34,68,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7508 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7509 : Route 9 := (fun mask => (mask,id))

def c7509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7509 : Upper (D 9) (R 9) [34,68,129,80,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,136] 13 (by decide) (choices 1) [1,256] r7509 c7509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4541
  · exact u4542

def r7510 : Route 9 := (fun mask => (mask,id))

def c7510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7510 : Upper (D 9) (R 9) [34,68,129,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,160] 13 (by decide) (choices 1) [1,8,256] r7510 c7510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4543
  · exact u4544
  · exact u4545

def r7511 : Route 9 := (fun mask => (mask,id))

def c7511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7511 : Upper (D 9) (R 9) [34,68,129,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,257] 13 (by decide) (choices 1) [8,128,256] r7511 c7511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4546
  · exact u4547
  · exact u4548

def r7512 : Route 9 := (fun mask => (mask,id))

def c7512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7512 : Upper (D 9) (R 9) [34,68,129,80,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,264] 13 (by decide) (choices 1) [1,128,256] r7512 c7512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4549
  · exact u4550
  · exact u4551

def r7513 : Route 9 := (fun mask => (mask,id))

def c7513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7513 : Upper (D 9) (R 9) [34,68,129,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,288] 13 (by decide) (choices 1) [1,8,128,256] r7513 c7513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4552
  · exact u4553
  · exact u4554
  · exact u4555

def r7514 : Route 9 := (fun mask => (mask,id))

def c7514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7514 : Upper (D 9) (R 9) [34,68,129,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,384] 13 (by decide) (choices 1) [1,8,256] r7514 c7514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4556
  · exact u4557
  · exact u4558

def b7515 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 16, targets := 352 },{ cop := 4, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6),(4,8)], upper := (rows 35 70 133 104 145 312 344 408 280), lower := (rows 35 70 133 104 145 32 64 128 256), losses := [] }

theorem u7515 : Upper (D 9) (R 9) [34,68,129,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7515 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7516 : Route 9 := (fun mask => (mask,id))

def c7516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7516 : Upper (D 9) (R 9) [34,68,129,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,136] 13 (by decide) (choices 1) [1,16,256] r7516 c7516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4559
  · exact u4560
  · exact u4561

def r7517 : Route 9 := (fun mask => (mask,id))

def c7517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u7517 : Upper (D 9) (R 9) [34,68,129,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,257] 13 (by decide) (choices 1) [8,16,128,256] r7517 c7517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4562
  · exact u4563
  · exact u4564
  · exact u4565

def r7518 : Route 9 := (fun mask => (mask,id))

def c7518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7518 : Upper (D 9) (R 9) [34,68,129,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264] 13 (by decide) (choices 1) [1,16,128,256] r7518 c7518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4566
  · exact u4567
  · exact u4568
  · exact u4569

def r7519 : Route 9 := (fun mask => (mask,id))

def c7519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7519 : Upper (D 9) (R 9) [34,68,129,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,384] 13 (by decide) (choices 1) [1,8,16,256] r7519 c7519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4570
  · exact u4571
  · exact u4572
  · exact u4573

def b7520 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,8)], upper := (rows 35 70 133 137 280 368 368 496 368), lower := (rows 35 70 133 137 280 32 64 128 256), losses := [] }

theorem u7520 : Upper (D 9) (R 9) [34,68,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7520 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7521 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,8)], upper := (rows 35 70 133 137 304 376 344 472 344), lower := (rows 35 70 133 137 304 32 64 128 256), losses := [] }

theorem u7521 : Upper (D 9) (R 9) [34,68,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7521 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7522 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,8)], upper := (rows 35 70 133 137 336 312 376 440 312), lower := (rows 35 70 133 137 336 32 64 128 256), losses := [] }

theorem u7522 : Upper (D 9) (R 9) [34,68,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7522 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7523 : Route 9 := (fun mask => (mask,id))

def c7523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7523 : Upper (D 9) (R 9) [34,68,129,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,257] 13 (by decide) (choices 1) [8,64,256] r7523 c7523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4574
  · exact u4575
  · exact u4576

def r7524 : Route 9 := (fun mask => (mask,id))

def c7524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7524 : Upper (D 9) (R 9) [34,68,129,144,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,264] 13 (by decide) (choices 1) [1,64,256] r7524 c7524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4577
  · exact u4578
  · exact u4579

def r7525 : Route 9 := (fun mask => (mask,id))

def c7525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7525 : Upper (D 9) (R 9) [34,68,129,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,288] 13 (by decide) (choices 1) [1,8,64,256] r7525 c7525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4580
  · exact u4581
  · exact u4582
  · exact u4583

def r7526 : Route 9 := (fun mask => (mask,id))

def c7526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7526 : Upper (D 9) (R 9) [34,68,129,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,320] 13 (by decide) (choices 1) [1,8,256] r7526 c7526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4584
  · exact u4585
  · exact u4586

def r7527 : Route 9 := (fun mask => (mask,id))

def c7527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u7527 : Upper (D 9) (R 9) [34,68,129,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,257] 13 (by decide) (choices 1) [8,16,64,256] r7527 c7527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4587
  · exact u4588
  · exact u4589
  · exact u4590

def r7528 : Route 9 := (fun mask => (mask,id))

def c7528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7528 : Upper (D 9) (R 9) [34,68,129,160,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264] 13 (by decide) (choices 1) [1,16,64,256] r7528 c7528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4591
  · exact u4592
  · exact u4593
  · exact u4594

def r7529 : Route 9 := (fun mask => (mask,id))

def c7529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7529 : Upper (D 9) (R 9) [34,68,129,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,320] 13 (by decide) (choices 1) [1,8,16,256] r7529 c7529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4595
  · exact u4596
  · exact u4597
  · exact u4598

def r7530 : Route 9 := (fun mask => (mask,id))

def c7530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7530 : Upper (D 9) (R 9) [34,68,129,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,257] 13 (by decide) (choices 1) [8,16,256] r7530 c7530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4599
  · exact u4600
  · exact u4601

def r7531 : Route 9 := (fun mask => (mask,id))

def c7531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7531 : Upper (D 9) (R 9) [34,68,129,192,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,264] 13 (by decide) (choices 1) [1,16,256] r7531 c7531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4602
  · exact u4603
  · exact u4604

def r7532 : Route 9 := (fun mask => (mask,id))

def c7532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7532 : Upper (D 9) (R 9) [34,68,129,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,288] 13 (by decide) (choices 1) [1,8,16,256] r7532 c7532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4605
  · exact u4606
  · exact u4607
  · exact u4608

def b7533 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(1,8),(4,5),(4,6),(4,7)], upper := (rows 35 70 133 265 280 240 240 240 496), lower := (rows 35 70 133 265 280 32 64 128 256), losses := [] }

theorem u7533 : Upper (D 9) (R 9) [34,68,129,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7533 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7534 : Route 9 := (fun mask => (mask,id))

def c7534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7534 : Upper (D 9) (R 9) [34,68,129,257,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,288] 13 (by decide) (choices 1) [8,16,64,128] r7534 c7534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4609
  · exact u4610
  · exact u4611
  · exact u4612

def r7535 : Route 9 := (fun mask => (mask,id))

def c7535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7535 : Upper (D 9) (R 9) [34,68,129,257,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,320] 13 (by decide) (choices 1) [8,16,128] r7535 c7535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4613
  · exact u4614
  · exact u4615

def r7536 : Route 9 := (fun mask => (mask,id))

def c7536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7536 : Upper (D 9) (R 9) [34,68,129,257,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257,384] 13 (by decide) (choices 1) [8,16,64] r7536 c7536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4616
  · exact u4617
  · exact u4618

def b7537 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 35 70 133 280 280 225 225 225 481), lower := (rows 35 70 133 280 280 32 64 128 256), losses := [] }

theorem u7537 : Upper (D 9) (R 9) [34,68,129,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7537 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7538 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 280 304 233 201 201 457), lower := (rows 35 70 133 280 304 32 64 128 256), losses := [] }

theorem u7538 : Upper (D 9) (R 9) [34,68,129,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7538 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7539 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 280 336 169 233 169 425), lower := (rows 35 70 133 280 336 32 64 128 256), losses := [] }

theorem u7539 : Upper (D 9) (R 9) [34,68,129,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7539 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7540 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 280 400 105 105 233 361), lower := (rows 35 70 133 280 400 32 64 128 256), losses := [] }

theorem u7540 : Upper (D 9) (R 9) [34,68,129,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7540 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7541 : Route 9 := (fun mask => (mask,id))

def c7541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7541 : Upper (D 9) (R 9) [34,68,129,288,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288,320] 13 (by decide) (choices 1) [1,8,16,128] r7541 c7541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4619
  · exact u4620
  · exact u4621
  · exact u4622

def r7542 : Route 9 := (fun mask => (mask,id))

def c7542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7542 : Upper (D 9) (R 9) [34,68,129,288,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288,384] 13 (by decide) (choices 1) [1,8,16,64] r7542 c7542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4623
  · exact u4624
  · exact u4625
  · exact u4626

def r7543 : Route 9 := (fun mask => (mask,id))

def c7543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7543 : Upper (D 9) (R 9) [34,68,129,320,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,320,384] 13 (by decide) (choices 1) [1,8,16] r7543 c7543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4627
  · exact u4628
  · exact u4629

def b7544 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 24, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 35 70 140 25 49 480 448 448 448), lower := (rows 35 70 140 25 49 32 64 128 256), losses := [] }

theorem u7544 : Upper (D 9) (R 9) [34,68,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7544 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7545 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 8, targets := 416 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,7),(3,8)], upper := (rows 35 70 140 25 81 416 480 416 416), lower := (rows 35 70 140 25 81 32 64 128 256), losses := [] }

theorem u7545 : Upper (D 9) (R 9) [34,68,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7545 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7546 : Route 9 := (fun mask => (mask,id))

def c7546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7546 : Upper (D 9) (R 9) [34,68,136,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,96] 13 (by decide) (choices 1) [1,128,256] r7546 c7546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4630
  · exact u4631
  · exact u4632

def b7547 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 12, targets := 352 }], pairs := [(2,5),(2,6),(2,8),(3,5),(3,6)], upper := (rows 35 70 140 25 145 352 352 480 352), lower := (rows 35 70 140 25 145 32 64 128 256), losses := [] }

theorem u7547 : Upper (D 9) (R 9) [34,68,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7547 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7548 : Route 9 := (fun mask => (mask,id))

def c7548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7548 : Upper (D 9) (R 9) [34,68,136,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,160] 13 (by decide) (choices 1) [1,64,256] r7548 c7548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4633
  · exact u4634
  · exact u4635

def r7549 : Route 9 := (fun mask => (mask,id))

def c7549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7549 : Upper (D 9) (R 9) [34,68,136,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,192] 13 (by decide) (choices 1) [1,256] r7549 c7549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4636
  · exact u4637

def b7550 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 480 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 140 25 273 480 480 480 480), lower := (rows 35 70 140 25 273 32 64 128 256), losses := [] }

theorem u7550 : Upper (D 9) (R 9) [34,68,136,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7550 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7551 : Route 9 := (fun mask => (mask,id))

def c7551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7551 : Upper (D 9) (R 9) [34,68,136,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,288] 13 (by decide) (choices 1) [1,64,128,256] r7551 c7551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4638
  · exact u4639
  · exact u4640
  · exact u4641

def r7552 : Route 9 := (fun mask => (mask,id))

def c7552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7552 : Upper (D 9) (R 9) [34,68,136,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,320] 13 (by decide) (choices 1) [1,128,256] r7552 c7552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4642
  · exact u4643
  · exact u4644

def r7553 : Route 9 := (fun mask => (mask,id))

def c7553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7553 : Upper (D 9) (R 9) [34,68,136,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,384] 13 (by decide) (choices 1) [1,64,256] r7553 c7553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4645
  · exact u4646
  · exact u4647

def b7554 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 428, targets := 64 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,6),(3,6),(4,5)], upper := (rows 35 70 140 56 81 417 449 385 385), lower := (rows 35 70 140 56 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 17 0 81 145 273), good := (rows 467 70 142 478 465 0 64 128 256) }] }

theorem u7554 : Upper (D 9) (R 9) [34,68,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7554 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7555 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(3,7),(4,5)], upper := (rows 35 70 140 56 145 353 321 449 321), lower := (rows 35 70 140 56 145 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 17 0 81 145 273), good := (rows 467 70 142 478 465 0 64 128 256) }] }

theorem u7555 : Upper (D 9) (R 9) [34,68,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7555 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7556 : Route 9 := (fun mask => (mask,id))

def c7556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7556 : Upper (D 9) (R 9) [34,68,136,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,192] 13 (by decide) (choices 1) [1,256] r7556 c7556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4648
  · exact u4649

def r7557 : Route 9 := (fun mask => (mask,id))

def c7557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7557 : Upper (D 9) (R 9) [34,68,136,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,257] 13 (by decide) (choices 1) [1,64,128,256] r7557 c7557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4650
  · exact u4651
  · exact u4652
  · exact u4653

def r7558 : Route 9 := (fun mask => (mask,id))

def c7558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7558 : Upper (D 9) (R 9) [34,68,136,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,320] 13 (by decide) (choices 1) [1,128,256] r7558 c7558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4654
  · exact u4655
  · exact u4656

def r7559 : Route 9 := (fun mask => (mask,id))

def c7559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7559 : Upper (D 9) (R 9) [34,68,136,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,384] 13 (by decide) (choices 1) [1,64,256] r7559 c7559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4657
  · exact u4658
  · exact u4659

#print axioms u7559
end Delivery.IrregularNine14.P09
