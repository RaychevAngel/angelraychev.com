import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0276
import IrregularNine14P06C0277

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33480 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 292 56 22 97 65 193 321), lower := (rows 11 134 292 56 22 32 64 128 256), losses := [] }

theorem u33480 : Upper (D 6) (R 6) [10,132,288,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33481 : Route 9 := (fun mask => (mask,id))

def c33481 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33481 : Upper (D 6) (R 6) [10,132,288,48,65] 13 := by
  apply FastRouting.sound _ _ [10,132,288,48,65] 13 (by decide) (choices 1) [1,2,4,64] r33481 c33481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16563
  · exact u16564
  · exact u16565
  · exact u16566

def r33482 : Route 9 := (fun mask => (mask,id))

def c33482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33482 : Upper (D 6) (R 6) [10,132,288,48,66] 13 := by
  apply FastRouting.sound _ _ [10,132,288,48,66] 13 (by decide) (choices 1) [1,4,64] r33482 c33482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16567
  · exact u16568
  · exact u16569

def r33483 : Route 9 := (fun mask => (mask,id))

def c33483 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33483 : Upper (D 6) (R 6) [10,132,288,48,68] 13 := by
  apply FastRouting.sound _ _ [10,132,288,48,68] 13 (by decide) (choices 1) [1,2,64] r33483 c33483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16570
  · exact u16571
  · exact u16572

def b33484 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 292 73 19 116 116 244 372), lower := (rows 11 134 292 73 19 32 64 128 256), losses := [] }

theorem u33484 : Upper (D 6) (R 6) [10,132,288,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33485 : Route 9 := (fun mask => (mask,id))

def c33485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33485 : Upper (D 6) (R 6) [10,132,288,65,5] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,5] 13 (by decide) (choices 1) [2,16,64] r33485 c33485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16573
  · exact u16574
  · exact u16575

def b33486 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 292 73 22 113 113 241 369), lower := (rows 11 134 292 73 22 32 64 128 256), losses := [] }

theorem u33486 : Upper (D 6) (R 6) [10,132,288,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33487 : Route 9 := (fun mask => (mask,id))

def c33487 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33487 : Upper (D 6) (R 6) [10,132,288,65,33] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,33] 13 (by decide) (choices 1) [2,4,16,64] r33487 c33487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16576
  · exact u16577
  · exact u16578
  · exact u16579

def r33488 : Route 9 := (fun mask => (mask,id))

def c33488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33488 : Upper (D 6) (R 6) [10,132,288,65,34] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,34] 13 (by decide) (choices 1) [1,4,16,64] r33488 c33488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16580
  · exact u16581
  · exact u16582
  · exact u16583

def b33489 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 292 73 52 115 83 211 339), lower := (rows 11 134 292 73 52 32 64 128 256), losses := [] }

theorem u33489 : Upper (D 6) (R 6) [10,132,288,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33490 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 134 292 73 81 54 118 182 310), lower := (rows 11 134 292 73 81 32 64 128 256), losses := [] }

theorem u33490 : Upper (D 6) (R 6) [10,132,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33491 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 292 73 82 53 117 181 309), lower := (rows 11 134 292 73 82 32 64 128 256), losses := [] }

theorem u33491 : Upper (D 6) (R 6) [10,132,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33492 : Route 9 := (fun mask => (mask,id))

def c33492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33492 : Upper (D 6) (R 6) [10,132,288,65,68] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,68] 13 (by decide) (choices 1) [1,2,16] r33492 c33492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16584
  · exact u16585
  · exact u16586

def r33493 : Route 9 := (fun mask => (mask,id))

def c33493 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33493 : Upper (D 6) (R 6) [10,132,288,65,96] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,96] 13 (by decide) (choices 1) [1,2,4,16] r33493 c33493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16587
  · exact u16588
  · exact u16589
  · exact u16590

def b33494 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 134 292 76 19 113 113 241 369), lower := (rows 11 134 292 76 19 32 64 128 256), losses := [] }

theorem u33494 : Upper (D 6) (R 6) [10,132,288,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33495 : Route 9 := (fun mask => (mask,id))

def c33495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33495 : Upper (D 6) (R 6) [10,132,288,68,33] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,33] 13 (by decide) (choices 1) [1,2,16,64] r33495 c33495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16591
  · exact u16592
  · exact u16593
  · exact u16594

def r33496 : Route 9 := (fun mask => (mask,id))

def c33496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33496 : Upper (D 6) (R 6) [10,132,288,68,34] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,34] 13 (by decide) (choices 1) [1,16,64] r33496 c33496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16595
  · exact u16596
  · exact u16597

def b33497 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 11 134 292 76 81 51 115 179 307), lower := (rows 11 134 292 76 81 32 64 128 256), losses := [] }

theorem u33497 : Upper (D 6) (R 6) [10,132,288,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33498 : Route 9 := (fun mask => (mask,id))

def c33498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33498 : Upper (D 6) (R 6) [10,132,288,68,66] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,66] 13 (by decide) (choices 1) [1,16] r33498 c33498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16598
  · exact u16599

def r33499 : Route 9 := (fun mask => (mask,id))

def c33499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33499 : Upper (D 6) (R 6) [10,132,288,68,96] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,96] 13 (by decide) (choices 1) [1,2,16] r33499 c33499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16600
  · exact u16601
  · exact u16602

def b33500 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 292 88 19 101 101 229 357), lower := (rows 11 134 292 88 19 32 64 128 256), losses := [] }

theorem u33500 : Upper (D 6) (R 6) [10,132,288,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33501 : Route 9 := (fun mask => (mask,id))

def c33501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33501 : Upper (D 6) (R 6) [10,132,288,80,5] 13 := by
  apply FastRouting.sound _ _ [10,132,288,80,5] 13 (by decide) (choices 1) [1,2,64] r33501 c33501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16603
  · exact u16604
  · exact u16605

def b33502 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 292 88 22 97 97 225 353), lower := (rows 11 134 292 88 22 32 64 128 256), losses := [] }

theorem u33502 : Upper (D 6) (R 6) [10,132,288,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33503 : Route 9 := (fun mask => (mask,id))

def c33503 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33503 : Upper (D 6) (R 6) [10,132,288,80,33] 13 := by
  apply FastRouting.sound _ _ [10,132,288,80,33] 13 (by decide) (choices 1) [1,2,4,64] r33503 c33503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16606
  · exact u16607
  · exact u16608
  · exact u16609

def r33504 : Route 9 := (fun mask => (mask,id))

def c33504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33504 : Upper (D 6) (R 6) [10,132,288,80,34] 13 := by
  apply FastRouting.sound _ _ [10,132,288,80,34] 13 (by decide) (choices 1) [1,4,64] r33504 c33504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16610
  · exact u16611
  · exact u16612

def b33505 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 292 88 52 99 67 195 323), lower := (rows 11 134 292 88 52 32 64 128 256), losses := [] }

theorem u33505 : Upper (D 6) (R 6) [10,132,288,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33506 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 292 88 81 39 103 167 295), lower := (rows 11 134 292 88 81 32 64 128 256), losses := [] }

theorem u33506 : Upper (D 6) (R 6) [10,132,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33507 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 292 88 82 37 101 165 293), lower := (rows 11 134 292 88 82 32 64 128 256), losses := [] }

theorem u33507 : Upper (D 6) (R 6) [10,132,288,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33508 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 292 88 84 35 99 163 291), lower := (rows 11 134 292 88 84 32 64 128 256), losses := [] }

theorem u33508 : Upper (D 6) (R 6) [10,132,288,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33509 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 292 88 112 39 71 135 263), lower := (rows 11 134 292 88 112 32 64 128 256), losses := [] }

theorem u33509 : Upper (D 6) (R 6) [10,132,288,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33510 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 292 104 19 117 85 213 341), lower := (rows 11 134 292 104 19 32 64 128 256), losses := [] }

theorem u33510 : Upper (D 6) (R 6) [10,132,288,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33511 : Route 9 := (fun mask => (mask,id))

def c33511 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33511 : Upper (D 6) (R 6) [10,132,288,96,5] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,5] 13 (by decide) (choices 1) [1,2,16,64] r33511 c33511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16613
  · exact u16614
  · exact u16615
  · exact u16616

def b33512 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 292 104 22 113 81 209 337), lower := (rows 11 134 292 104 22 32 64 128 256), losses := [] }

theorem u33512 : Upper (D 6) (R 6) [10,132,288,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33513 : Route 9 := (fun mask => (mask,id))

def c33513 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33513 : Upper (D 6) (R 6) [10,132,288,96,65] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,65] 13 (by decide) (choices 1) [1,2,4,16] r33513 c33513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16617
  · exact u16618
  · exact u16619
  · exact u16620

def r33514 : Route 9 := (fun mask => (mask,id))

def c33514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33514 : Upper (D 6) (R 6) [10,132,288,96,66] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,66] 13 (by decide) (choices 1) [1,4,16] r33514 c33514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16621
  · exact u16622
  · exact u16623

def r33515 : Route 9 := (fun mask => (mask,id))

def c33515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33515 : Upper (D 6) (R 6) [10,132,288,96,68] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,68] 13 (by decide) (choices 1) [1,2,16] r33515 c33515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16624
  · exact u16625
  · exact u16626

def b33516 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 37 73 22 356 356 484 356), lower := (rows 11 146 37 73 22 32 64 128 256), losses := [] }

theorem u33516 : Upper (D 6) (R 6) [10,144,33,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33517 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 37 73 50 356 324 452 324), lower := (rows 11 146 37 73 50 32 64 128 256), losses := [] }

theorem u33517 : Upper (D 6) (R 6) [10,144,33,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33518 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 37 73 52 358 326 454 326), lower := (rows 11 146 37 73 52 32 64 128 256), losses := [] }

theorem u33518 : Upper (D 6) (R 6) [10,144,33,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33519 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 146 37 73 82 292 356 420 292), lower := (rows 11 146 37 73 82 32 64 128 256), losses := [] }

theorem u33519 : Upper (D 6) (R 6) [10,144,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33520 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 146 37 73 84 294 358 422 294), lower := (rows 11 146 37 73 84 32 64 128 256), losses := [] }

theorem u33520 : Upper (D 6) (R 6) [10,144,33,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33521 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 146 37 73 112 294 326 390 262), lower := (rows 11 146 37 73 112 32 64 128 256), losses := [] }

theorem u33521 : Upper (D 6) (R 6) [10,144,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33522 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 108, targets := 2 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 37 73 274 100 100 228 356), lower := (rows 11 146 37 73 274 32 64 128 256), losses := [] }

theorem u33522 : Upper (D 6) (R 6) [10,144,33,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33523 : Route 9 := (fun mask => (mask,id))

def c33523 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33523 : Upper (D 6) (R 6) [10,144,33,65,260] 13 := by
  apply FastRouting.sound _ _ [10,144,33,65,260] 13 (by decide) (choices 1) [2,4,64] r33523 c33523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16627
  · exact u16628
  · exact u16629

def r33524 : Route 9 := (fun mask => (mask,id))

def c33524 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33524 : Upper (D 6) (R 6) [10,144,33,65,288] 13 := by
  apply FastRouting.sound _ _ [10,144,33,65,288] 13 (by decide) (choices 1) [2,4,64] r33524 c33524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16630
  · exact u16631
  · exact u16632

def b33525 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 146 37 73 336 38 102 166 294), lower := (rows 11 146 37 73 336 32 64 128 256), losses := [] }

theorem u33525 : Upper (D 6) (R 6) [10,144,33,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33526 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 37 76 19 356 356 484 356), lower := (rows 11 146 37 76 19 32 64 128 256), losses := [] }

theorem u33526 : Upper (D 6) (R 6) [10,144,33,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33527 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 146 37 76 21 354 354 482 354), lower := (rows 11 146 37 76 21 32 64 128 256), losses := [] }

theorem u33527 : Upper (D 6) (R 6) [10,144,33,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33528 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 146 37 76 22 353 353 481 353), lower := (rows 11 146 37 76 22 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 69 133 261), good := (rows 491 146 481 488 498 32 64 128 256) }] }

theorem u33528 : Upper (D 6) (R 6) [10,144,33,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33529 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 146 37 76 49 358 326 454 326), lower := (rows 11 146 37 76 49 32 64 128 256), losses := [] }

theorem u33529 : Upper (D 6) (R 6) [10,144,33,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33530 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 328, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 146 37 76 50 357 325 453 325), lower := (rows 11 146 37 76 50 32 64 128 256), losses := [] }

theorem u33530 : Upper (D 6) (R 6) [10,144,33,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33531 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 37 76 52 355 323 451 323), lower := (rows 11 146 37 76 52 32 64 128 256), losses := [] }

theorem u33531 : Upper (D 6) (R 6) [10,144,33,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33532 : Route 9 := (fun mask => (mask,id))

def c33532 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33532 : Upper (D 6) (R 6) [10,144,33,68,65] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68,65] 13 (by decide) (choices 1) [2,4,256] r33532 c33532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16633
  · exact u16634
  · exact u16635

def b33533 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 146 37 76 82 293 357 421 293), lower := (rows 11 146 37 76 82 32 64 128 256), losses := [] }

theorem u33533 : Upper (D 6) (R 6) [10,144,33,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33534 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 146 37 76 84 291 355 419 291), lower := (rows 11 146 37 76 84 32 64 128 256), losses := [] }

theorem u33534 : Upper (D 6) (R 6) [10,144,33,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33535 : Route 9 := (fun mask => (mask,id))

def c33535 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33535 : Upper (D 6) (R 6) [10,144,33,68,96] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68,96] 13 (by decide) (choices 1) [1,2,4,256] r33535 c33535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16636
  · exact u16637
  · exact u16638
  · exact u16639

def r33536 : Route 9 := (fun mask => (mask,id))

def c33536 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33536 : Upper (D 6) (R 6) [10,144,33,68,257] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68,257] 13 (by decide) (choices 1) [2,4,64] r33536 c33536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16640
  · exact u16641
  · exact u16642

def r33537 : Route 9 := (fun mask => (mask,id))

def c33537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33537 : Upper (D 6) (R 6) [10,144,33,68,258] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68,258] 13 (by decide) (choices 1) [1,4,64] r33537 c33537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16643
  · exact u16644
  · exact u16645

def r33538 : Route 9 := (fun mask => (mask,id))

def c33538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33538 : Upper (D 6) (R 6) [10,144,33,68,260] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68,260] 13 (by decide) (choices 1) [1,2,64] r33538 c33538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16646
  · exact u16647
  · exact u16648

def r33539 : Route 9 := (fun mask => (mask,id))

def c33539 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33539 : Upper (D 6) (R 6) [10,144,33,68,288] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68,288] 13 (by decide) (choices 1) [1,2,4,64] r33539 c33539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16649
  · exact u16650
  · exact u16651
  · exact u16652

#print axioms u33539
end Delivery.IrregularNine14.P06
