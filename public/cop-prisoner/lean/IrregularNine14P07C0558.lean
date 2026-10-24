import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0291
import IrregularNine14P07C0292
import IrregularNine14P07C0293

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33480 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,1)], upper := (rows 13 274 38 74 49 225 193 193 449), lower := (rows 13 274 38 74 49 32 64 128 256), losses := [] }

theorem u33480 : Upper (D 7) (R 7) [12,272,34,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33481 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,5),(0,6),(2,6),(3,5)], upper := (rows 13 274 38 74 112 161 193 129 385), lower := (rows 13 274 38 74 112 32 64 128 256), losses := [] }

theorem u33481 : Upper (D 7) (R 7) [12,272,34,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33482 : Route 9 := (fun mask => (mask,id))

def c33482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33482 : Upper (D 7) (R 7) [12,272,34,66,129] 13 := by
  apply FastRouting.sound _ _ [12,272,34,66,129] 13 (by decide) (choices 1) [1,64,128] r33482 c33482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17502
  · exact u17503
  · exact u17504

def r33483 : Route 9 := (fun mask => (mask,id))

def c33483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33483 : Upper (D 7) (R 7) [12,272,34,66,160] 13 := by
  apply FastRouting.sound _ _ [12,272,34,66,160] 13 (by decide) (choices 1) [1,64,128] r33483 c33483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17505
  · exact u17506
  · exact u17507

def b33484 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(1,5),(3,1),(4,5)], upper := (rows 13 274 38 104 19 225 193 193 449), lower := (rows 13 274 38 104 19 32 64 128 256), losses := [] }

theorem u33484 : Upper (D 7) (R 7) [12,272,34,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33485 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,5),(1,6),(2,6),(4,5)], upper := (rows 13 274 38 104 81 163 195 131 387), lower := (rows 13 274 38 104 81 32 64 128 256), losses := [] }

theorem u33485 : Upper (D 7) (R 7) [12,272,34,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33486 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(1,5),(3,1),(4,5)], upper := (rows 13 274 38 104 82 161 193 129 385), lower := (rows 13 274 38 104 82 32 64 128 256), losses := [] }

theorem u33486 : Upper (D 7) (R 7) [12,272,34,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33487 : Route 9 := (fun mask => (mask,id))

def c33487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33487 : Upper (D 7) (R 7) [12,272,34,96,129] 13 := by
  apply FastRouting.sound _ _ [12,272,34,96,129] 13 (by decide) (choices 1) [1,2,64,128] r33487 c33487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17508
  · exact u17509
  · exact u17510
  · exact u17511

def b33488 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(1,5),(3,1),(4,5)], upper := (rows 13 274 38 104 146 225 193 193 449), lower := (rows 13 274 38 104 146 32 64 128 256), losses := [] }

theorem u33488 : Upper (D 7) (R 7) [12,272,34,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33489 : Route 9 := (fun mask => (mask,id))

def c33489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33489 : Upper (D 7) (R 7) [12,272,34,96,192] 13 := by
  apply FastRouting.sound _ _ [12,272,34,96,192] 13 (by decide) (choices 1) [1,2,128] r33489 c33489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17512
  · exact u17513
  · exact u17514

def r33490 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33490 : Upper (D 7) (R 7) [12,272,34,192,3] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,3] 13 (by decide) (choices 1) [1,64] r33490 c33490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17515
  · exact u17516

def r33491 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33491 : Upper (D 7) (R 7) [12,272,34,192,33] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,33] 13 (by decide) (choices 1) [1,2,64] r33491 c33491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17517
  · exact u17518
  · exact u17519

def b33492 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 16, targets := 193 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,6),(4,7)], upper := (rows 13 274 38 200 50 225 193 193 449), lower := (rows 13 274 38 200 50 32 64 128 256), losses := [] }

theorem u33492 : Upper (D 7) (R 7) [12,272,34,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33493 : Route 9 := (fun mask => (mask,id))

def c33493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33493 : Upper (D 7) (R 7) [12,272,34,192,65] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,65] 13 (by decide) (choices 1) [1,2,128] r33493 c33493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17520
  · exact u17521
  · exact u17522

def r33494 : Route 9 := (fun mask => (mask,id))

def c33494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33494 : Upper (D 7) (R 7) [12,272,34,192,66] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,66] 13 (by decide) (choices 1) [1,128] r33494 c33494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17523
  · exact u17524

def r33495 : Route 9 := (fun mask => (mask,id))

def c33495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33495 : Upper (D 7) (R 7) [12,272,34,192,96] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,96] 13 (by decide) (choices 1) [1,2,128] r33495 c33495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17525
  · exact u17526
  · exact u17527

def b33496 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 274 38 200 208 35 99 163 291), lower := (rows 13 274 38 200 208 32 64 128 256), losses := [] }

theorem u33496 : Upper (D 7) (R 7) [12,272,34,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m33497_128 : Upper (D 7) (R 7) [12,272,96,160,3,128] 13 :=
  permutation_upper _ _ _ [12,272,96,160,3,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17530

def r33497 : Route 9 := (fun mask => (mask,id))

def c33497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33497 : Upper (D 7) (R 7) [12,272,96,160,3] 13 := by
  apply FastRouting.sound _ _ [12,272,96,160,3] 13 (by decide) (choices 1) [1,2,64,128] r33497 c33497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17528
  · exact u17529
  · exact u17530
  · exact m33497_128

def b33498 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 13 274 100 168 81 163 195 131 387), lower := (rows 13 274 100 168 81 32 64 128 256), losses := [] }

theorem u33498 : Upper (D 7) (R 7) [12,272,96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33499 : Route 9 := (fun mask => (mask,id))

def c33499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33499 : Upper (D 7) (R 7) [12,272,96,160,66] 13 := by
  apply FastRouting.sound _ _ [12,272,96,160,66] 13 (by decide) (choices 1) [1,2,128] r33499 c33499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17531
  · exact u17532
  · exact u17533

def r33500 : Route 9 := (fun mask => (mask,id))

def c33500 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33500 : Upper (D 7) (R 7) [12,272,96,160,192] 13 := by
  apply FastRouting.sound _ _ [12,272,96,160,192] 13 (by decide) (choices 1) [1,2] r33500 c33500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17534
  · exact u17535

def b33501 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 7 25 50 224 192 192 448), lower := (rows 13 290 7 25 50 32 64 128 256), losses := [] }

theorem u33501 : Upper (D 7) (R 7) [12,288,3,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33502 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 290 7 25 82 224 224 224 480), lower := (rows 13 290 7 25 82 32 64 128 256), losses := [] }

theorem u33502 : Upper (D 7) (R 7) [12,288,3,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33503 : Route 9 := (fun mask => (mask,id))

def c33503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33503 : Upper (D 7) (R 7) [12,288,3,17,96] 13 := by
  apply FastRouting.sound _ _ [12,288,3,17,96] 13 (by decide) (choices 1) [2,64,128] r33503 c33503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17536
  · exact u17537
  · exact u17538

def r33504 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33504 : Upper (D 7) (R 7) [12,288,3,17,192] 13 := by
  apply FastRouting.sound _ _ [12,288,3,17,192] 13 (by decide) (choices 1) [2,64] r33504 c33504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17539
  · exact u17540

def b33505 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 7 56 19 224 192 192 448), lower := (rows 13 290 7 56 19 32 64 128 256), losses := [] }

theorem u33505 : Upper (D 7) (R 7) [12,288,3,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33506 : Route 9 := (fun mask => (mask,id))

def c33506 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33506 : Upper (D 7) (R 7) [12,288,3,48,65] 13 := by
  apply FastRouting.sound _ _ [12,288,3,48,65] 13 (by decide) (choices 1) [2,64,128] r33506 c33506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17541
  · exact u17542
  · exact u17543

def r33507 : Route 9 := (fun mask => (mask,id))

def c33507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33507 : Upper (D 7) (R 7) [12,288,3,48,66] 13 := by
  apply FastRouting.sound _ _ [12,288,3,48,66] 13 (by decide) (choices 1) [1,64,128] r33507 c33507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17544
  · exact u17545
  · exact u17546

def r33508 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33508 : Upper (D 7) (R 7) [12,288,3,48,192] 13 := by
  apply FastRouting.sound _ _ [12,288,3,48,192] 13 (by decide) (choices 1) [1,2,64] r33508 c33508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17547
  · exact u17548
  · exact u17549

def b33509 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 205, targets := 32 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 290 7 73 50 240 208 208 464), lower := (rows 13 290 7 73 50 32 64 128 256), losses := [] }

theorem u33509 : Upper (D 7) (R 7) [12,288,3,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33510 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 7 73 82 176 240 176 432), lower := (rows 13 290 7 73 82 32 64 128 256), losses := [] }

theorem u33510 : Upper (D 7) (R 7) [12,288,3,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33511 : Route 9 := (fun mask => (mask,id))

def c33511 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33511 : Upper (D 7) (R 7) [12,288,3,65,96] 13 := by
  apply FastRouting.sound _ _ [12,288,3,65,96] 13 (by decide) (choices 1) [2,16,128] r33511 c33511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17550
  · exact u17551
  · exact u17552

def r33512 : Route 9 := (fun mask => (mask,id))

def c33512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33512 : Upper (D 7) (R 7) [12,288,3,65,130] 13 := by
  apply FastRouting.sound _ _ [12,288,3,65,130] 13 (by decide) (choices 1) [16,64,128] r33512 c33512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17553
  · exact u17554
  · exact u17555

def r33513 : Route 9 := (fun mask => (mask,id))

def c33513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33513 : Upper (D 7) (R 7) [12,288,3,65,160] 13 := by
  apply FastRouting.sound _ _ [12,288,3,65,160] 13 (by decide) (choices 1) [2,16,64,128] r33513 c33513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17556
  · exact u17557
  · exact u17558
  · exact u17559

def r33514 : Route 9 := (fun mask => (mask,id))

def c33514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33514 : Upper (D 7) (R 7) [12,288,3,65,192] 13 := by
  apply FastRouting.sound _ _ [12,288,3,65,192] 13 (by decide) (choices 1) [2,16,128] r33514 c33514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17560
  · exact u17561
  · exact u17562

def b33515 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 290 7 88 19 224 224 224 480), lower := (rows 13 290 7 88 19 32 64 128 256), losses := [] }

theorem u33515 : Upper (D 7) (R 7) [12,288,3,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33516 : Route 9 := (fun mask => (mask,id))

def c33516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33516 : Upper (D 7) (R 7) [12,288,3,80,33] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,33] 13 (by decide) (choices 1) [2,64,128] r33516 c33516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17563
  · exact u17564
  · exact u17565

def b33517 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 7 88 50 225 193 193 449), lower := (rows 13 290 7 88 50 32 64 128 256), losses := [] }

theorem u33517 : Upper (D 7) (R 7) [12,288,3,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33518 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 13 290 7 88 81 162 226 162 418), lower := (rows 13 290 7 88 81 32 64 128 256), losses := [] }

theorem u33518 : Upper (D 7) (R 7) [12,288,3,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33519 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 7 88 82 161 225 161 417), lower := (rows 13 290 7 88 82 32 64 128 256), losses := [] }

theorem u33519 : Upper (D 7) (R 7) [12,288,3,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33520 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 290 7 88 112 163 195 131 387), lower := (rows 13 290 7 88 112 32 64 128 256), losses := [] }

theorem u33520 : Upper (D 7) (R 7) [12,288,3,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33521 : Route 9 := (fun mask => (mask,id))

def c33521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33521 : Upper (D 7) (R 7) [12,288,3,80,129] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,129] 13 (by decide) (choices 1) [2,64,128] r33521 c33521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17566
  · exact u17567
  · exact u17568

def r33522 : Route 9 := (fun mask => (mask,id))

def c33522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33522 : Upper (D 7) (R 7) [12,288,3,80,130] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,130] 13 (by decide) (choices 1) [1,64,128] r33522 c33522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17569
  · exact u17570
  · exact u17571

def r33523 : Route 9 := (fun mask => (mask,id))

def c33523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33523 : Upper (D 7) (R 7) [12,288,3,80,160] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,160] 13 (by decide) (choices 1) [1,2,64,128] r33523 c33523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17572
  · exact u17573
  · exact u17574
  · exact u17575

def b33524 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 13 290 7 88 208 163 227 163 419), lower := (rows 13 290 7 88 208 32 64 128 256), losses := [] }

theorem u33524 : Upper (D 7) (R 7) [12,288,3,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33525 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 13 290 7 104 19 240 208 208 464), lower := (rows 13 290 7 104 19 32 64 128 256), losses := [] }

theorem u33525 : Upper (D 7) (R 7) [12,288,3,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33526 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 290 7 104 81 178 210 146 402), lower := (rows 13 290 7 104 81 32 64 128 256), losses := [] }

theorem u33526 : Upper (D 7) (R 7) [12,288,3,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33527 : Route 9 := (fun mask => (mask,id))

def c33527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33527 : Upper (D 7) (R 7) [12,288,3,96,66] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,66] 13 (by decide) (choices 1) [1,16,128] r33527 c33527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17576
  · exact u17577
  · exact u17578

def r33528 : Route 9 := (fun mask => (mask,id))

def c33528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33528 : Upper (D 7) (R 7) [12,288,3,96,129] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,129] 13 (by decide) (choices 1) [2,16,64,128] r33528 c33528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17579
  · exact u17580
  · exact u17581
  · exact u17582

def r33529 : Route 9 := (fun mask => (mask,id))

def c33529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33529 : Upper (D 7) (R 7) [12,288,3,96,130] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,130] 13 (by decide) (choices 1) [1,16,64,128] r33529 c33529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17583
  · exact u17584
  · exact u17585
  · exact u17586

def r33530 : Route 9 := (fun mask => (mask,id))

def c33530 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33530 : Upper (D 7) (R 7) [12,288,3,96,192] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,192] 13 (by decide) (choices 1) [1,2,16,128] r33530 c33530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17587
  · exact u17588
  · exact u17589
  · exact u17590

def b33531 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 290 7 200 19 240 240 240 496), lower := (rows 13 290 7 200 19 32 64 128 256), losses := [] }

theorem u33531 : Upper (D 7) (R 7) [12,288,3,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33532 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33532 : Upper (D 7) (R 7) [12,288,3,192,33] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,33] 13 (by decide) (choices 1) [2,16,64] r33532 c33532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17591
  · exact u17592
  · exact u17593

def b33533 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 7 200 50 241 209 209 465), lower := (rows 13 290 7 200 50 32 64 128 256), losses := [] }

theorem u33533 : Upper (D 7) (R 7) [12,288,3,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33534 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 290 7 200 81 178 242 178 434), lower := (rows 13 290 7 200 81 32 64 128 256), losses := [] }

theorem u33534 : Upper (D 7) (R 7) [12,288,3,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33535 : Route 9 := (fun mask => (mask,id))

def c33535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33535 : Upper (D 7) (R 7) [12,288,3,192,66] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,66] 13 (by decide) (choices 1) [1,16,128] r33535 c33535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17594
  · exact u17595
  · exact u17596

def r33536 : Route 9 := (fun mask => (mask,id))

def c33536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33536 : Upper (D 7) (R 7) [12,288,3,192,96] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,96] 13 (by decide) (choices 1) [1,2,16,128] r33536 c33536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17597
  · exact u17598
  · exact u17599
  · exact u17600

def b33537 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 290 7 200 208 51 115 179 307), lower := (rows 13 290 7 200 208 32 64 128 256), losses := [] }

theorem u33537 : Upper (D 7) (R 7) [12,288,3,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33538 : Route 9 := (fun mask => (mask,id))

def c33538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33538 : Upper (D 7) (R 7) [12,288,17,33,66] 13 := by
  apply FastRouting.sound _ _ [12,288,17,33,66] 13 (by decide) (choices 1) [2,64,128] r33538 c33538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17601
  · exact u17602
  · exact u17603

def r33539 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33539 : Upper (D 7) (R 7) [12,288,17,33,192] 13 := by
  apply FastRouting.sound _ _ [12,288,17,33,192] 13 (by decide) (choices 1) [2,64] r33539 c33539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17604
  · exact u17605

#print axioms u33539
end Delivery.IrregularNine14.P07
