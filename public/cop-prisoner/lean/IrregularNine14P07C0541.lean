import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0262
import IrregularNine14P07C0263
import IrregularNine14P07C0264

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32460 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 162, targets := 64 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,6),(3,0),(3,6),(4,0)], upper := (rows 13 35 69 280 82 162 226 162 418), lower := (rows 13 35 69 280 82 32 64 128 256), losses := [] }

theorem u32460 : Upper (D 7) (R 7) [12,33,65,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32461 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,6),(2,5),(3,0),(4,0)], upper := (rows 13 35 69 280 112 162 194 130 386), lower := (rows 13 35 69 280 112 32 64 128 256), losses := [] }

theorem u32461 : Upper (D 7) (R 7) [12,33,65,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32462 : Route 9 := (fun mask => (mask,id))

def c32462 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32462 : Upper (D 7) (R 7) [12,33,65,272,130] 13 := by
  apply FastRouting.sound _ _ [12,33,65,272,130] 13 (by decide) (choices 1) [2,64,128] r32462 c32462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15729
  · exact u15730
  · exact u15731

def r32463 : Route 9 := (fun mask => (mask,id))

def c32463 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32463 : Upper (D 7) (R 7) [12,33,65,272,160] 13 := by
  apply FastRouting.sound _ _ [12,33,65,272,160] 13 (by decide) (choices 1) [2,64,128] r32463 c32463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15732
  · exact u15733
  · exact u15734

def r32464 : Route 9 := (fun mask => (mask,id))

def c32464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32464 : Upper (D 7) (R 7) [12,33,65,272,192] 13 := by
  apply FastRouting.sound _ _ [12,33,65,272,192] 13 (by decide) (choices 1) [2,128] r32464 c32464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15735
  · exact u15736

def b32465 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 35 69 392 50 242 210 210 466), lower := (rows 13 35 69 392 50 32 64 128 256), losses := [] }

theorem u32465 : Upper (D 7) (R 7) [12,33,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32466 : Route 9 := (fun mask => (mask,id))

def c32466 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32466 : Upper (D 7) (R 7) [12,33,65,384,66] 13 := by
  apply FastRouting.sound _ _ [12,33,65,384,66] 13 (by decide) (choices 1) [2,16,128] r32466 c32466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15737
  · exact u15738
  · exact u15739

def r32467 : Route 9 := (fun mask => (mask,id))

def c32467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32467 : Upper (D 7) (R 7) [12,33,65,384,96] 13 := by
  apply FastRouting.sound _ _ [12,33,65,384,96] 13 (by decide) (choices 1) [2,16,128] r32467 c32467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15740
  · exact u15741
  · exact u15742

def r32468 : Route 9 := (fun mask => (mask,id))

def c32468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32468 : Upper (D 7) (R 7) [12,33,65,384,130] 13 := by
  apply FastRouting.sound _ _ [12,33,65,384,130] 13 (by decide) (choices 1) [2,16,64] r32468 c32468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15743
  · exact u15744
  · exact u15745

def r32469 : Route 9 := (fun mask => (mask,id))

def c32469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32469 : Upper (D 7) (R 7) [12,33,65,384,160] 13 := by
  apply FastRouting.sound _ _ [12,33,65,384,160] 13 (by decide) (choices 1) [2,16,64] r32469 c32469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15746
  · exact u15747
  · exact u15748

def r32470 : Route 9 := (fun mask => (mask,id))

def c32470 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32470 : Upper (D 7) (R 7) [12,33,65,384,192] 13 := by
  apply FastRouting.sound _ _ [12,33,65,384,192] 13 (by decide) (choices 1) [2,16] r32470 c32470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15749
  · exact u15750

def b32471 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 25, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 35 70 88 19 416 480 416 416), lower := (rows 13 35 70 88 19 32 64 128 256), losses := [] }

theorem u32471 : Upper (D 7) (R 7) [12,33,66,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32472 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 452, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,6),(2,0),(4,1),(4,6)], upper := (rows 13 35 70 88 49 418 450 386 386), lower := (rows 13 35 70 88 49 32 64 128 256), losses := [] }

theorem u32472 : Upper (D 7) (R 7) [12,33,66,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32473 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 35 70 88 50 417 449 385 385), lower := (rows 13 35 70 88 50 32 64 128 256), losses := [] }

theorem u32473 : Upper (D 7) (R 7) [12,33,66,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32474 : Route 9 := (fun mask => (mask,id))

def c32474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32474 : Upper (D 7) (R 7) [12,33,66,80,129] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,129] 13 (by decide) (choices 1) [2,128,256] r32474 c32474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15751
  · exact u15752
  · exact u15753

def r32475 : Route 9 := (fun mask => (mask,id))

def c32475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32475 : Upper (D 7) (R 7) [12,33,66,80,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,130] 13 (by decide) (choices 1) [1,128,256] r32475 c32475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15754
  · exact u15755
  · exact u15756

def r32476 : Route 9 := (fun mask => (mask,id))

def c32476 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32476 : Upper (D 7) (R 7) [12,33,66,80,160] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,160] 13 (by decide) (choices 1) [1,2,128,256] r32476 c32476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15757
  · exact u15758
  · exact u15759
  · exact u15760

def r32477 : Route 9 := (fun mask => (mask,id))

def c32477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32477 : Upper (D 7) (R 7) [12,33,66,80,257] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,257] 13 (by decide) (choices 1) [2,128] r32477 c32477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15761
  · exact u15762

def r32478 : Route 9 := (fun mask => (mask,id))

def c32478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32478 : Upper (D 7) (R 7) [12,33,66,80,258] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,258] 13 (by decide) (choices 1) [1,128] r32478 c32478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15763
  · exact u15764

def r32479 : Route 9 := (fun mask => (mask,id))

def c32479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32479 : Upper (D 7) (R 7) [12,33,66,80,288] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,288] 13 (by decide) (choices 1) [1,2,128] r32479 c32479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15765
  · exact u15766
  · exact u15767

def r32480 : Route 9 := (fun mask => (mask,id))

def c32480 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32480 : Upper (D 7) (R 7) [12,33,66,80,384] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,384] 13 (by decide) (choices 1) [1,2,128] r32480 c32480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15768
  · exact u15769
  · exact u15770

def b32481 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 70 138 49 496 464 464 464), lower := (rows 13 35 70 138 49 32 64 128 256), losses := [] }

theorem u32481 : Upper (D 7) (R 7) [12,33,66,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32482 : Route 9 := (fun mask => (mask,id))

def c32482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u32482 : Upper (D 7) (R 7) [12,33,66,130,65] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130,65] 13 (by decide) (choices 1) [16,128,256] r32482 c32482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15771
  · exact u15772
  · exact u15773

def r32483 : Route 9 := (fun mask => (mask,id))

def c32483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u32483 : Upper (D 7) (R 7) [12,33,66,130,96] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130,96] 13 (by decide) (choices 1) [1,16,128,256] r32483 c32483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15774
  · exact u15775
  · exact u15776
  · exact u15777

def r32484 : Route 9 := (fun mask => (mask,id))

def c32484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32484 : Upper (D 7) (R 7) [12,33,66,130,192] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130,192] 13 (by decide) (choices 1) [1,16,256] r32484 c32484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15778
  · exact u15779
  · exact u15780

theorem m32485_128 : Upper (D 7) (R 7) [12,33,66,130,257,128] 13 :=
  permutation_upper _ _ _ [12,33,66,130,257,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15782

def r32485 : Route 9 := (fun mask => (mask,id))

def c32485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32485 : Upper (D 7) (R 7) [12,33,66,130,257] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130,257] 13 (by decide) (choices 1) [16,64,128] r32485 c32485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15781
  · exact u15782
  · exact m32485_128

theorem m32486_128 : Upper (D 7) (R 7) [12,33,66,130,288,128] 13 :=
  permutation_upper _ _ _ [12,33,66,130,288,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15785

def r32486 : Route 9 := (fun mask => (mask,id))

def c32486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32486 : Upper (D 7) (R 7) [12,33,66,130,288] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130,288] 13 (by decide) (choices 1) [1,16,64,128] r32486 c32486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15783
  · exact u15784
  · exact u15785
  · exact m32486_128

def r32487 : Route 9 := (fun mask => (mask,id))

def c32487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32487 : Upper (D 7) (R 7) [12,33,66,130,320] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130,320] 13 (by decide) (choices 1) [1,16,128] r32487 c32487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15786
  · exact u15787
  · exact u15788

def b32488 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 484, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 35 70 152 19 480 480 480 480), lower := (rows 13 35 70 152 19 32 64 128 256), losses := [] }

theorem u32488 : Upper (D 7) (R 7) [12,33,66,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32489 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 70 152 49 482 450 450 450), lower := (rows 13 35 70 152 49 32 64 128 256), losses := [] }

theorem u32489 : Upper (D 7) (R 7) [12,33,66,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32490 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 35 70 152 50 481 449 449 449), lower := (rows 13 35 70 152 50 32 64 128 256), losses := [] }

theorem u32490 : Upper (D 7) (R 7) [12,33,66,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32491 : Route 9 := (fun mask => (mask,id))

def c32491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32491 : Upper (D 7) (R 7) [12,33,66,144,65] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144,65] 13 (by decide) (choices 1) [2,128,256] r32491 c32491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15789
  · exact u15790
  · exact u15791

def b32492 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 35 70 152 82 417 481 417 417), lower := (rows 13 35 70 152 82 32 64 128 256), losses := [] }

theorem u32492 : Upper (D 7) (R 7) [12,33,66,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32493 : Route 9 := (fun mask => (mask,id))

def c32493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32493 : Upper (D 7) (R 7) [12,33,66,144,96] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144,96] 13 (by decide) (choices 1) [1,2,128,256] r32493 c32493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15792
  · exact u15793
  · exact u15794
  · exact u15795

def b32494 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 35 70 152 145 354 354 482 354), lower := (rows 13 35 70 152 145 32 64 128 256), losses := [] }

theorem u32494 : Upper (D 7) (R 7) [12,33,66,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32495 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 35 70 152 146 353 353 481 353), lower := (rows 13 35 70 152 146 32 64 128 256), losses := [] }

theorem u32495 : Upper (D 7) (R 7) [12,33,66,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32496 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 35 70 152 176 355 323 451 323), lower := (rows 13 35 70 152 176 32 64 128 256), losses := [] }

theorem u32496 : Upper (D 7) (R 7) [12,33,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32497 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 35 70 152 208 291 355 419 291), lower := (rows 13 35 70 152 208 32 64 128 256), losses := [] }

theorem u32497 : Upper (D 7) (R 7) [12,33,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32498 : Route 9 := (fun mask => (mask,id))

def c32498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32498 : Upper (D 7) (R 7) [12,33,66,144,257] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144,257] 13 (by decide) (choices 1) [2,64,128] r32498 c32498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15796
  · exact u15797
  · exact u15798

def r32499 : Route 9 := (fun mask => (mask,id))

def c32499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32499 : Upper (D 7) (R 7) [12,33,66,144,258] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144,258] 13 (by decide) (choices 1) [1,64,128] r32499 c32499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15799
  · exact u15800
  · exact u15801

def r32500 : Route 9 := (fun mask => (mask,id))

def c32500 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32500 : Upper (D 7) (R 7) [12,33,66,144,288] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144,288] 13 (by decide) (choices 1) [1,2,64,128] r32500 c32500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15802
  · exact u15803
  · exact u15804
  · exact u15805

def r32501 : Route 9 := (fun mask => (mask,id))

def c32501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32501 : Upper (D 7) (R 7) [12,33,66,144,320] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144,320] 13 (by decide) (choices 1) [1,2,128] r32501 c32501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15806
  · exact u15807
  · exact u15808

def b32502 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 35 70 152 400 99 99 227 355), lower := (rows 13 35 70 152 400 32 64 128 256), losses := [] }

theorem u32502 : Upper (D 7) (R 7) [12,33,66,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32503 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 35 70 168 19 496 464 464 464), lower := (rows 13 35 70 168 19 32 64 128 256), losses := [] }

theorem u32503 : Upper (D 7) (R 7) [12,33,66,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32504 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 13 35 70 168 81 434 466 402 402), lower := (rows 13 35 70 168 81 32 64 128 256), losses := [] }

theorem u32504 : Upper (D 7) (R 7) [12,33,66,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32505 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 35 70 168 82 433 465 401 401), lower := (rows 13 35 70 168 82 32 64 128 256), losses := [] }

theorem u32505 : Upper (D 7) (R 7) [12,33,66,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32506 : PairBound 9 := { available := 338, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,7),(2,5),(2,7),(4,5)], upper := (rows 13 35 70 168 145 370 338 466 338), lower := (rows 13 35 70 168 145 32 64 128 256), losses := [] }

theorem u32506 : Upper (D 7) (R 7) [12,33,66,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32507 : Route 9 := (fun mask => (mask,id))

def c32507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32507 : Upper (D 7) (R 7) [12,33,66,160,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160,130] 13 (by decide) (choices 1) [1,16,64,256] r32507 c32507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15809
  · exact u15810
  · exact u15811
  · exact u15812

def r32508 : Route 9 := (fun mask => (mask,id))

def c32508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32508 : Upper (D 7) (R 7) [12,33,66,160,192] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160,192] 13 (by decide) (choices 1) [1,2,16,256] r32508 c32508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15813
  · exact u15814
  · exact u15815
  · exact u15816

def r32509 : Route 9 := (fun mask => (mask,id))

def c32509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32509 : Upper (D 7) (R 7) [12,33,66,160,257] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160,257] 13 (by decide) (choices 1) [2,16,64,128] r32509 c32509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15817
  · exact u15818
  · exact u15819
  · exact u15820

def r32510 : Route 9 := (fun mask => (mask,id))

def c32510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32510 : Upper (D 7) (R 7) [12,33,66,160,258] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160,258] 13 (by decide) (choices 1) [1,16,64,128] r32510 c32510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15821
  · exact u15822
  · exact u15823
  · exact u15824

def r32511 : Route 9 := (fun mask => (mask,id))

def c32511 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32511 : Upper (D 7) (R 7) [12,33,66,160,320] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160,320] 13 (by decide) (choices 1) [1,2,16,128] r32511 c32511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15825
  · exact u15826
  · exact u15827
  · exact u15828

def r32512 : Route 9 := (fun mask => (mask,id))

def c32512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32512 : Upper (D 7) (R 7) [12,33,66,160,384] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160,384] 13 (by decide) (choices 1) [1,2,16,64] r32512 c32512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15829
  · exact u15830
  · exact u15831
  · exact u15832

def b32513 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 16, targets := 160 }], pairs := [(1,6),(4,5),(4,6),(4,7)], upper := (rows 13 35 70 200 19 432 496 432 432), lower := (rows 13 35 70 200 19 32 64 128 256), losses := [] }

theorem u32513 : Upper (D 7) (R 7) [12,33,66,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32514 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 16, targets := 2 },{ cop := 1, region := 16, targets := 128 }], pairs := [(1,6),(4,1),(4,6),(4,7)], upper := (rows 13 35 70 200 49 434 466 402 402), lower := (rows 13 35 70 200 49 32 64 128 256), losses := [] }

theorem u32514 : Upper (D 7) (R 7) [12,33,66,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32515 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 35 70 200 50 433 465 401 401), lower := (rows 13 35 70 200 50 32 64 128 256), losses := [] }

theorem u32515 : Upper (D 7) (R 7) [12,33,66,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32516 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,6),(1,7),(2,7),(4,6)], upper := (rows 13 35 70 200 145 306 370 434 306), lower := (rows 13 35 70 200 145 32 64 128 256), losses := [] }

theorem u32516 : Upper (D 7) (R 7) [12,33,66,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32517 : Route 9 := (fun mask => (mask,id))

def c32517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32517 : Upper (D 7) (R 7) [12,33,66,192,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192,130] 13 (by decide) (choices 1) [1,16,256] r32517 c32517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15833
  · exact u15834
  · exact u15835

def r32518 : Route 9 := (fun mask => (mask,id))

def c32518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32518 : Upper (D 7) (R 7) [12,33,66,192,160] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192,160] 13 (by decide) (choices 1) [1,2,16,256] r32518 c32518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15836
  · exact u15837
  · exact u15838
  · exact u15839

def r32519 : Route 9 := (fun mask => (mask,id))

def c32519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32519 : Upper (D 7) (R 7) [12,33,66,192,257] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192,257] 13 (by decide) (choices 1) [2,16,128] r32519 c32519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15840
  · exact u15841
  · exact u15842

#print axioms u32519
end Delivery.IrregularNine14.P07
