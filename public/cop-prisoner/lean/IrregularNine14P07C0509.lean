import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0208
import IrregularNine14P07C0209
import IrregularNine14P07C0210

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30540 : Route 9 := (fun mask => (mask,id))

def c30540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30540 : Upper (D 7) (R 7) [6,33,192,65,136] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,136] 13 (by decide) (choices 1) [2,16,256] r30540 c30540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12493
  · exact u12494
  · exact u12495

def r30541 : Route 9 := (fun mask => (mask,id))

def c30541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30541 : Upper (D 7) (R 7) [6,33,192,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,160] 13 (by decide) (choices 1) [2,8,16,256] r30541 c30541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12496
  · exact u12497
  · exact u12498
  · exact u12499

def r30542 : Route 9 := (fun mask => (mask,id))

def c30542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30542 : Upper (D 7) (R 7) [6,33,192,65,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,258] 13 (by decide) (choices 1) [8,16,128] r30542 c30542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12500
  · exact u12501
  · exact u12502

def r30543 : Route 9 := (fun mask => (mask,id))

def c30543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30543 : Upper (D 7) (R 7) [6,33,192,65,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,264] 13 (by decide) (choices 1) [2,16,128] r30543 c30543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12503
  · exact u12504
  · exact u12505

def r30544 : Route 9 := (fun mask => (mask,id))

def c30544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30544 : Upper (D 7) (R 7) [6,33,192,65,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,288] 13 (by decide) (choices 1) [2,8,16,128] r30544 c30544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12506
  · exact u12507
  · exact u12508
  · exact u12509

def r30545 : Route 9 := (fun mask => (mask,id))

def c30545 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30545 : Upper (D 7) (R 7) [6,33,192,65,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,384] 13 (by decide) (choices 1) [2,8,16] r30545 c30545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12510
  · exact u12511
  · exact u12512

def r30546 : Route 9 := (fun mask => (mask,id))

def c30546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30546 : Upper (D 7) (R 7) [6,33,192,66,136] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,136] 13 (by decide) (choices 1) [1,16,256] r30546 c30546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12513
  · exact u12514
  · exact u12515

def r30547 : Route 9 := (fun mask => (mask,id))

def c30547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30547 : Upper (D 7) (R 7) [6,33,192,66,160] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,160] 13 (by decide) (choices 1) [1,8,16,256] r30547 c30547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12516
  · exact u12517
  · exact u12518
  · exact u12519

def r30548 : Route 9 := (fun mask => (mask,id))

def c30548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30548 : Upper (D 7) (R 7) [6,33,192,66,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,257] 13 (by decide) (choices 1) [8,16,128] r30548 c30548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12520
  · exact u12521
  · exact u12522

def r30549 : Route 9 := (fun mask => (mask,id))

def c30549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30549 : Upper (D 7) (R 7) [6,33,192,66,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,264] 13 (by decide) (choices 1) [1,16,128] r30549 c30549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12523
  · exact u12524
  · exact u12525

def r30550 : Route 9 := (fun mask => (mask,id))

def c30550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30550 : Upper (D 7) (R 7) [6,33,192,66,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,288] 13 (by decide) (choices 1) [1,8,16,128] r30550 c30550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12526
  · exact u12527
  · exact u12528
  · exact u12529

def r30551 : Route 9 := (fun mask => (mask,id))

def c30551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30551 : Upper (D 7) (R 7) [6,33,192,66,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,384] 13 (by decide) (choices 1) [1,8,16] r30551 c30551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12530
  · exact u12531
  · exact u12532

def b30552 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5),(4,0)], upper := (rows 7 35 196 88 152 291 355 419 291), lower := (rows 7 35 196 88 152 32 64 128 256), losses := [] }

theorem u30552 : Upper (D 7) (R 7) [6,33,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30553 : Route 9 := (fun mask => (mask,id))

def c30553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30553 : Upper (D 7) (R 7) [6,33,192,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,160] 13 (by decide) (choices 1) [1,2,8,256] r30553 c30553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12533
  · exact u12534
  · exact u12535
  · exact u12536

def r30554 : Route 9 := (fun mask => (mask,id))

def c30554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30554 : Upper (D 7) (R 7) [6,33,192,80,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,257] 13 (by decide) (choices 1) [2,8,128] r30554 c30554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12537
  · exact u12538
  · exact u12539

def r30555 : Route 9 := (fun mask => (mask,id))

def c30555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30555 : Upper (D 7) (R 7) [6,33,192,80,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,258] 13 (by decide) (choices 1) [1,8,128] r30555 c30555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12540
  · exact u12541
  · exact u12542

def r30556 : Route 9 := (fun mask => (mask,id))

def c30556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30556 : Upper (D 7) (R 7) [6,33,192,80,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,264] 13 (by decide) (choices 1) [1,2,128] r30556 c30556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12543
  · exact u12544
  · exact u12545

def r30557 : Route 9 := (fun mask => (mask,id))

def c30557 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30557 : Upper (D 7) (R 7) [6,33,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,288] 13 (by decide) (choices 1) [1,2,8,128] r30557 c30557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12546
  · exact u12547
  · exact u12548
  · exact u12549

def r30558 : Route 9 := (fun mask => (mask,id))

def c30558 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30558 : Upper (D 7) (R 7) [6,33,192,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384] 13 (by decide) (choices 1) [1,2,8] r30558 c30558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12550
  · exact u12551
  · exact u12552

def r30559 : Route 9 := (fun mask => (mask,id))

def c30559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30559 : Upper (D 7) (R 7) [6,33,192,96,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,257] 13 (by decide) (choices 1) [2,8,16,128] r30559 c30559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12553
  · exact u12554
  · exact u12555
  · exact u12556

def r30560 : Route 9 := (fun mask => (mask,id))

def c30560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30560 : Upper (D 7) (R 7) [6,33,192,96,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,258] 13 (by decide) (choices 1) [1,8,16,128] r30560 c30560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12557
  · exact u12558
  · exact u12559
  · exact u12560

def r30561 : Route 9 := (fun mask => (mask,id))

def c30561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30561 : Upper (D 7) (R 7) [6,33,192,96,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264] 13 (by decide) (choices 1) [1,2,16,128] r30561 c30561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12561
  · exact u12562
  · exact u12563
  · exact u12564

def r30562 : Route 9 := (fun mask => (mask,id))

def c30562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30562 : Upper (D 7) (R 7) [6,33,192,96,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,384] 13 (by decide) (choices 1) [1,2,8,16] r30562 c30562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12565
  · exact u12566
  · exact u12567
  · exact u12568

def b30563 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 7 35 196 200 273 58 122 186 314), lower := (rows 7 35 196 200 273 32 64 128 256), losses := [] }

theorem u30563 : Upper (D 7) (R 7) [6,33,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30564 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 7 35 196 200 274 57 121 185 313), lower := (rows 7 35 196 200 274 32 64 128 256), losses := [] }

theorem u30564 : Upper (D 7) (R 7) [6,33,192,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30565 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 7 35 196 200 280 51 115 179 307), lower := (rows 7 35 196 200 280 32 64 128 256), losses := [] }

theorem u30565 : Upper (D 7) (R 7) [6,33,192,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30566 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 7 35 196 200 304 59 91 155 283), lower := (rows 7 35 196 200 304 32 64 128 256), losses := [] }

theorem u30566 : Upper (D 7) (R 7) [6,33,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30567 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 261 26 56 224 192 192 448), lower := (rows 7 35 261 26 56 32 64 128 256), losses := [] }

theorem u30567 : Upper (D 7) (R 7) [6,33,257,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30568 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 0, region := 484, targets := 2 },{ cop := 3, region := 240, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 35 261 26 88 224 224 224 480), lower := (rows 7 35 261 26 88 32 64 128 256), losses := [] }

theorem u30568 : Upper (D 7) (R 7) [6,33,257,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30569 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 7 35 261 26 112 232 200 200 456), lower := (rows 7 35 261 26 112 32 64 128 256), losses := [] }

theorem u30569 : Upper (D 7) (R 7) [6,33,257,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30570 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30570 : Upper (D 7) (R 7) [6,33,257,18,192] 13 := by
  apply FastRouting.sound _ _ [6,33,257,18,192] 13 (by decide) (choices 1) [8,64] r30570 c30570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12569
  · exact u12570

def b30571 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 261 42 88 240 208 208 464), lower := (rows 7 35 261 42 88 32 64 128 256), losses := [] }

theorem u30571 : Upper (D 7) (R 7) [6,33,257,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30572 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 261 42 208 248 216 216 472), lower := (rows 7 35 261 42 208 32 64 128 256), losses := [] }

theorem u30572 : Upper (D 7) (R 7) [6,33,257,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30573 : Route 9 := (fun mask => (mask,id))

def c30573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30573 : Upper (D 7) (R 7) [6,33,257,48,66] 13 := by
  apply FastRouting.sound _ _ [6,33,257,48,66] 13 (by decide) (choices 1) [8,64,128] r30573 c30573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12571
  · exact u12572
  · exact u12573

def b30574 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 7 35 261 56 88 226 194 194 450), lower := (rows 7 35 261 56 88 32 64 128 256), losses := [] }

theorem u30574 : Upper (D 7) (R 7) [6,33,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30575 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30575 : Upper (D 7) (R 7) [6,33,257,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,257,48,192] 13 (by decide) (choices 1) [2,8,64] r30575 c30575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12574
  · exact u12575
  · exact u12576

def b30576 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 423, targets := 64 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 261 74 88 176 240 176 432), lower := (rows 7 35 261 74 88 32 64 128 256), losses := [] }

theorem u30576 : Upper (D 7) (R 7) [6,33,257,66,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30577 : Route 9 := (fun mask => (mask,id))

def c30577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30577 : Upper (D 7) (R 7) [6,33,257,66,96] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,96] 13 (by decide) (choices 1) [8,16,128] r30577 c30577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12577
  · exact u12578
  · exact u12579

def r30578 : Route 9 := (fun mask => (mask,id))

def c30578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30578 : Upper (D 7) (R 7) [6,33,257,66,136] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,136] 13 (by decide) (choices 1) [16,64,128] r30578 c30578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12580
  · exact u12581
  · exact u12582

def r30579 : Route 9 := (fun mask => (mask,id))

def c30579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u30579 : Upper (D 7) (R 7) [6,33,257,66,160] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,160] 13 (by decide) (choices 1) [8,16,64,128] r30579 c30579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12583
  · exact u12584
  · exact u12585
  · exact u12586

def r30580 : Route 9 := (fun mask => (mask,id))

def c30580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30580 : Upper (D 7) (R 7) [6,33,257,66,192] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,192] 13 (by decide) (choices 1) [8,16,128] r30580 c30580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12587
  · exact u12588
  · exact u12589

def b30581 : PairBound 9 := { available := 162, camps := [{ cop := 6, region := 24, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 261 88 88 162 226 162 418), lower := (rows 7 35 261 88 88 32 64 128 256), losses := [] }

theorem u30581 : Upper (D 7) (R 7) [6,33,257,80,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30582 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 261 88 112 170 202 138 394), lower := (rows 7 35 261 88 112 32 64 128 256), losses := [] }

theorem u30582 : Upper (D 7) (R 7) [6,33,257,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m30583_128 : Upper (D 7) (R 7) [6,33,257,80,136,128] 13 :=
  permutation_upper _ _ _ [6,33,257,80,136,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12591

def r30583 : Route 9 := (fun mask => (mask,id))

def c30583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30583 : Upper (D 7) (R 7) [6,33,257,80,136] 13 := by
  apply FastRouting.sound _ _ [6,33,257,80,136] 13 (by decide) (choices 1) [2,64,128] r30583 c30583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12590
  · exact u12591
  · exact m30583_128

def r30584 : Route 9 := (fun mask => (mask,id))

def c30584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30584 : Upper (D 7) (R 7) [6,33,257,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,257,80,160] 13 (by decide) (choices 1) [2,8,64,128] r30584 c30584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12592
  · exact u12593
  · exact u12594
  · exact u12595

def b30585 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 261 88 208 170 234 170 426), lower := (rows 7 35 261 88 208 32 64 128 256), losses := [] }

theorem u30585 : Upper (D 7) (R 7) [6,33,257,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30586 : Route 9 := (fun mask => (mask,id))

def c30586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30586 : Upper (D 7) (R 7) [6,33,257,96,192] 13 := by
  apply FastRouting.sound _ _ [6,33,257,96,192] 13 (by decide) (choices 1) [2,8,16,128] r30586 c30586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12596
  · exact u12597
  · exact u12598
  · exact u12599

def b30587 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 35 261 200 208 58 122 186 314), lower := (rows 7 35 261 200 208 32 64 128 256), losses := [] }

theorem u30587 : Upper (D 7) (R 7) [6,33,257,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30588 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 268 25 50 224 192 192 448), lower := (rows 7 35 268 25 50 32 64 128 256), losses := [] }

theorem u30588 : Upper (D 7) (R 7) [6,33,264,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30589 : Route 9 := (fun mask => (mask,id))

def c30589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30589 : Upper (D 7) (R 7) [6,33,264,17,66] 13 := by
  apply FastRouting.sound _ _ [6,33,264,17,66] 13 (by decide) (choices 1) [64,128] r30589 c30589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12600
  · exact u12601

def r30590 : Route 9 := (fun mask => (mask,id))

def c30590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30590 : Upper (D 7) (R 7) [6,33,264,17,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,17,96] 13 (by decide) (choices 1) [2,64,128] r30590 c30590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12602
  · exact u12603
  · exact u12604

def r30591 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30591 : Upper (D 7) (R 7) [6,33,264,17,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,17,192] 13 (by decide) (choices 1) [2,64] r30591 c30591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12605
  · exact u12606

def b30592 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 268 26 49 224 192 192 448), lower := (rows 7 35 268 26 49 32 64 128 256), losses := [] }

theorem u30592 : Upper (D 7) (R 7) [6,33,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30593 : Route 9 := (fun mask => (mask,id))

def c30593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30593 : Upper (D 7) (R 7) [6,33,264,18,65] 13 := by
  apply FastRouting.sound _ _ [6,33,264,18,65] 13 (by decide) (choices 1) [64,128] r30593 c30593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12607
  · exact u12608

def b30594 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(2,1),(2,5),(4,1)], upper := (rows 7 35 268 26 112 225 193 193 449), lower := (rows 7 35 268 26 112 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 284 508 112 32 64 128 256) }] }

theorem u30594 : Upper (D 7) (R 7) [6,33,264,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30595 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30595 : Upper (D 7) (R 7) [6,33,264,18,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,18,192] 13 (by decide) (choices 1) [1,64] r30595 c30595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12609
  · exact u12610

def b30596 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 268 56 19 224 192 192 448), lower := (rows 7 35 268 56 19 32 64 128 256), losses := [] }

theorem u30596 : Upper (D 7) (R 7) [6,33,264,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30597 : Route 9 := (fun mask => (mask,id))

def c30597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30597 : Upper (D 7) (R 7) [6,33,264,48,65] 13 := by
  apply FastRouting.sound _ _ [6,33,264,48,65] 13 (by decide) (choices 1) [2,64,128] r30597 c30597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12611
  · exact u12612
  · exact u12613

def r30598 : Route 9 := (fun mask => (mask,id))

def c30598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30598 : Upper (D 7) (R 7) [6,33,264,48,66] 13 := by
  apply FastRouting.sound _ _ [6,33,264,48,66] 13 (by decide) (choices 1) [1,64,128] r30598 c30598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12614
  · exact u12615
  · exact u12616

def r30599 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30599 : Upper (D 7) (R 7) [6,33,264,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,48,192] 13 (by decide) (choices 1) [1,2,64] r30599 c30599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12617
  · exact u12618
  · exact u12619

#print axioms u30599
end Delivery.IrregularNine14.P07
