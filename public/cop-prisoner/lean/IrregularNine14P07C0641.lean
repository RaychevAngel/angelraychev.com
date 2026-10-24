import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0429
import IrregularNine14P07C0430

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38460 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 26 112 170 202 138 394), lower := (rows 37 259 69 26 112 32 64 128 256), losses := [] }

theorem u38460 : Upper (D 7) (R 7) [36,257,65,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38461 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 69 26 146 232 232 232 488), lower := (rows 37 259 69 26 146 32 64 128 256), losses := [] }

theorem u38461 : Upper (D 7) (R 7) [36,257,65,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38462 : Route 9 := (fun mask => (mask,id))

def c38462 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38462 : Upper (D 7) (R 7) [36,257,65,18,136] 13 := by
  apply FastRouting.sound _ _ [36,257,65,18,136] 13 (by decide) (choices 1) [2,64,128] r38462 c38462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25747
  · exact u25748
  · exact u25749

def r38463 : Route 9 := (fun mask => (mask,id))

def c38463 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38463 : Upper (D 7) (R 7) [36,257,65,18,160] 13 := by
  apply FastRouting.sound _ _ [36,257,65,18,160] 13 (by decide) (choices 1) [2,8,64,128] r38463 c38463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25750
  · exact u25751
  · exact u25752
  · exact u25753

def r38464 : Route 9 := (fun mask => (mask,id))

def c38464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38464 : Upper (D 7) (R 7) [36,257,65,18,192] 13 := by
  apply FastRouting.sound _ _ [36,257,65,18,192] 13 (by decide) (choices 1) [2,8,128] r38464 c38464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25754
  · exact u25755
  · exact u25756

def b38465 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 208, targets := 32 },{ cop := 4, region := 168, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,5)], upper := (rows 37 259 69 42 82 184 216 152 408), lower := (rows 37 259 69 42 82 32 64 128 256), losses := [] }

theorem u38465 : Upper (D 7) (R 7) [36,257,65,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38466 : Route 9 := (fun mask => (mask,id))

def c38466 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38466 : Upper (D 7) (R 7) [36,257,65,34,72] 13 := by
  apply FastRouting.sound _ _ [36,257,65,34,72] 13 (by decide) (choices 1) [2,16,128] r38466 c38466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25757
  · exact u25758
  · exact u25759

def r38467 : Route 9 := (fun mask => (mask,id))

def c38467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u38467 : Upper (D 7) (R 7) [36,257,65,34,130] 13 := by
  apply FastRouting.sound _ _ [36,257,65,34,130] 13 (by decide) (choices 1) [8,16,64,128] r38467 c38467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25760
  · exact u25761
  · exact u25762
  · exact u25763

def r38468 : Route 9 := (fun mask => (mask,id))

def c38468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38468 : Upper (D 7) (R 7) [36,257,65,34,136] 13 := by
  apply FastRouting.sound _ _ [36,257,65,34,136] 13 (by decide) (choices 1) [2,16,64,128] r38468 c38468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25764
  · exact u25765
  · exact u25766
  · exact u25767

def r38469 : Route 9 := (fun mask => (mask,id))

def c38469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38469 : Upper (D 7) (R 7) [36,257,65,34,192] 13 := by
  apply FastRouting.sound _ _ [36,257,65,34,192] 13 (by decide) (choices 1) [2,8,16,128] r38469 c38469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25768
  · exact u25769
  · exact u25770
  · exact u25771

def r38470 : Route 9 := (fun mask => (mask,id))

def c38470 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38470 : Upper (D 7) (R 7) [36,257,65,48,66] 13 := by
  apply FastRouting.sound _ _ [36,257,65,48,66] 13 (by decide) (choices 1) [2,8,128] r38470 c38470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25772
  · exact u25773
  · exact u25774

def b38471 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 248, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 37 259 69 56 88 162 194 130 386), lower := (rows 37 259 69 56 88 32 64 128 256), losses := [] }

theorem u38471 : Upper (D 7) (R 7) [36,257,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38472 : Route 9 := (fun mask => (mask,id))

def c38472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38472 : Upper (D 7) (R 7) [36,257,65,48,130] 13 := by
  apply FastRouting.sound _ _ [36,257,65,48,130] 13 (by decide) (choices 1) [2,8,64,128] r38472 c38472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25775
  · exact u25776
  · exact u25777
  · exact u25778

def b38473 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 248, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 37 259 69 56 152 226 194 194 450), lower := (rows 37 259 69 56 152 32 64 128 256), losses := [] }

theorem u38473 : Upper (D 7) (R 7) [36,257,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38474 : Route 9 := (fun mask => (mask,id))

def c38474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38474 : Upper (D 7) (R 7) [36,257,65,48,192] 13 := by
  apply FastRouting.sound _ _ [36,257,65,48,192] 13 (by decide) (choices 1) [2,8,128] r38474 c38474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25779
  · exact u25780
  · exact u25781

def r38475 : Route 9 := (fun mask => (mask,id))

def c38475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38475 : Upper (D 7) (R 7) [36,257,65,66,130] 13 := by
  apply FastRouting.sound _ _ [36,257,65,66,130] 13 (by decide) (choices 1) [8,16,128] r38475 c38475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25782
  · exact u25783
  · exact u25784

def r38476 : Route 9 := (fun mask => (mask,id))

def c38476 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38476 : Upper (D 7) (R 7) [36,257,65,66,136] 13 := by
  apply FastRouting.sound _ _ [36,257,65,66,136] 13 (by decide) (choices 1) [2,16,128] r38476 c38476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25785
  · exact u25786
  · exact u25787

def r38477 : Route 9 := (fun mask => (mask,id))

def c38477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38477 : Upper (D 7) (R 7) [36,257,65,66,160] 13 := by
  apply FastRouting.sound _ _ [36,257,65,66,160] 13 (by decide) (choices 1) [2,8,16,128] r38477 c38477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25788
  · exact u25789
  · exact u25790
  · exact u25791

def r38478 : Route 9 := (fun mask => (mask,id))

def c38478 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38478 : Upper (D 7) (R 7) [36,257,65,80,130] 13 := by
  apply FastRouting.sound _ _ [36,257,65,80,130] 13 (by decide) (choices 1) [2,8,128] r38478 c38478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25792
  · exact u25793
  · exact u25794

def b38479 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 37 259 69 88 152 162 226 162 418), lower := (rows 37 259 69 88 152 32 64 128 256), losses := [] }

theorem u38479 : Upper (D 7) (R 7) [36,257,65,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38480 : Route 9 := (fun mask => (mask,id))

def c38480 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38480 : Upper (D 7) (R 7) [36,257,65,80,160] 13 := by
  apply FastRouting.sound _ _ [36,257,65,80,160] 13 (by decide) (choices 1) [2,8,128] r38480 c38480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25795
  · exact u25796
  · exact u25797

def b38481 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 104 146 186 218 154 410), lower := (rows 37 259 69 104 146 32 64 128 256), losses := [] }

theorem u38481 : Upper (D 7) (R 7) [36,257,65,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38482 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 104 152 178 210 146 402), lower := (rows 37 259 69 104 152 32 64 128 256), losses := [] }

theorem u38482 : Upper (D 7) (R 7) [36,257,65,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38483 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 16, targets := 96 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 259 69 138 146 120 120 248 376), lower := (rows 37 259 69 138 146 32 64 128 256), losses := [] }

theorem u38483 : Upper (D 7) (R 7) [36,257,65,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38484 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,1),(4,5),(4,6)], upper := (rows 37 259 69 138 152 114 114 242 370), lower := (rows 37 259 69 138 152 32 64 128 256), losses := [] }

theorem u38484 : Upper (D 7) (R 7) [36,257,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38485 : Route 9 := (fun mask => (mask,id))

def c38485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38485 : Upper (D 7) (R 7) [36,257,65,130,160] 13 := by
  apply FastRouting.sound _ _ [36,257,65,130,160] 13 (by decide) (choices 1) [2,8,16,64] r38485 c38485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25798
  · exact u25799
  · exact u25800
  · exact u25801

def r38486 : Route 9 := (fun mask => (mask,id))

def c38486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38486 : Upper (D 7) (R 7) [36,257,65,130,192] 13 := by
  apply FastRouting.sound _ _ [36,257,65,130,192] 13 (by decide) (choices 1) [2,8,16] r38486 c38486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25802
  · exact u25803
  · exact u25804

def b38487 : PairBound 9 := { available := 98, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 69 152 152 98 98 226 354), lower := (rows 37 259 69 152 152 32 64 128 256), losses := [] }

theorem u38487 : Upper (D 7) (R 7) [36,257,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38488 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 69 152 176 106 74 202 330), lower := (rows 37 259 69 152 176 32 64 128 256), losses := [] }

theorem u38488 : Upper (D 7) (R 7) [36,257,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38489 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 69 152 208 42 106 170 298), lower := (rows 37 259 69 152 208 32 64 128 256), losses := [] }

theorem u38489 : Upper (D 7) (R 7) [36,257,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38490 : Route 9 := (fun mask => (mask,id))

def c38490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38490 : Upper (D 7) (R 7) [36,257,65,160,192] 13 := by
  apply FastRouting.sound _ _ [36,257,65,160,192] 13 (by decide) (choices 1) [2,8,16] r38490 c38490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25805
  · exact u25806
  · exact u25807

def b38491 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 70 11 56 240 208 208 464), lower := (rows 37 259 70 11 56 32 64 128 256), losses := [] }

theorem u38491 : Upper (D 7) (R 7) [36,257,66,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38492 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 70 11 88 176 240 176 432), lower := (rows 37 259 70 11 88 32 64 128 256), losses := [] }

theorem u38492 : Upper (D 7) (R 7) [36,257,66,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38493 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 70 11 112 184 216 152 408), lower := (rows 37 259 70 11 112 32 64 128 256), losses := [] }

theorem u38493 : Upper (D 7) (R 7) [36,257,66,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38494 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 70 11 152 240 240 240 496), lower := (rows 37 259 70 11 152 32 64 128 256), losses := [] }

theorem u38494 : Upper (D 7) (R 7) [36,257,66,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38495 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 70 11 176 248 216 216 472), lower := (rows 37 259 70 11 176 32 64 128 256), losses := [] }

theorem u38495 : Upper (D 7) (R 7) [36,257,66,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38496 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 70 11 208 184 248 184 440), lower := (rows 37 259 70 11 208 32 64 128 256), losses := [] }

theorem u38496 : Upper (D 7) (R 7) [36,257,66,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38497 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 37 259 70 25 26 224 224 224 480), lower := (rows 37 259 70 25 26 32 64 128 256), losses := [] }

theorem u38497 : Upper (D 7) (R 7) [36,257,66,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38498 : Route 9 := (fun mask => (mask,id))

def c38498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38498 : Upper (D 7) (R 7) [36,257,66,17,34] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,34] 13 (by decide) (choices 1) [8,64,128] r38498 c38498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25808
  · exact u25809
  · exact u25810

def b38499 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 259 70 25 56 226 194 194 450), lower := (rows 37 259 70 25 56 32 64 128 256), losses := [] }

theorem u38499 : Upper (D 7) (R 7) [36,257,66,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38500 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 259 70 25 82 168 232 168 424), lower := (rows 37 259 70 25 82 32 64 128 256), losses := [] }

theorem u38500 : Upper (D 7) (R 7) [36,257,66,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38501 : Route 9 := (fun mask => (mask,id))

def c38501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38501 : Upper (D 7) (R 7) [36,257,66,17,72] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,72] 13 (by decide) (choices 1) [2,128] r38501 c38501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25811
  · exact u25812

def r38502 : Route 9 := (fun mask => (mask,id))

def c38502 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38502 : Upper (D 7) (R 7) [36,257,66,17,96] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,96] 13 (by decide) (choices 1) [2,8,128] r38502 c38502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25813
  · exact u25814
  · exact u25815

def r38503 : Route 9 := (fun mask => (mask,id))

def c38503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38503 : Upper (D 7) (R 7) [36,257,66,17,130] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,130] 13 (by decide) (choices 1) [8,64,128] r38503 c38503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25816
  · exact u25817
  · exact u25818

def r38504 : Route 9 := (fun mask => (mask,id))

def c38504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38504 : Upper (D 7) (R 7) [36,257,66,17,136] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,136] 13 (by decide) (choices 1) [2,64,128] r38504 c38504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25819
  · exact u25820
  · exact u25821

def r38505 : Route 9 := (fun mask => (mask,id))

def c38505 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38505 : Upper (D 7) (R 7) [36,257,66,17,160] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,160] 13 (by decide) (choices 1) [2,8,64,128] r38505 c38505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25822
  · exact u25823
  · exact u25824
  · exact u25825

def r38506 : Route 9 := (fun mask => (mask,id))

def c38506 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38506 : Upper (D 7) (R 7) [36,257,66,17,192] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,192] 13 (by decide) (choices 1) [2,8,128] r38506 c38506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25826
  · exact u25827
  · exact u25828

def b38507 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 259 70 26 49 232 200 200 456), lower := (rows 37 259 70 26 49 32 64 128 256), losses := [] }

theorem u38507 : Upper (D 7) (R 7) [36,257,66,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38508 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(4,1)], upper := (rows 37 259 70 26 56 225 193 193 449), lower := (rows 37 259 70 26 56 32 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 24 39 71 135 263), good := (rows 485 481 485 504 56 32 64 128 256) }] }

theorem u38508 : Upper (D 7) (R 7) [36,257,66,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38509 : Route 9 := (fun mask => (mask,id))

def c38509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38509 : Upper (D 7) (R 7) [36,257,66,18,65] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,65] 13 (by decide) (choices 1) [8,128] r38509 c38509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25829
  · exact u25830

def b38510 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 259 70 26 88 161 225 161 417), lower := (rows 37 259 70 26 88 32 64 128 256), losses := [] }

theorem u38510 : Upper (D 7) (R 7) [36,257,66,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38511 : Route 9 := (fun mask => (mask,id))

def c38511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38511 : Upper (D 7) (R 7) [36,257,66,18,96] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,96] 13 (by decide) (choices 1) [1,8,128] r38511 c38511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25831
  · exact u25832
  · exact u25833

def r38512 : Route 9 := (fun mask => (mask,id))

def c38512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38512 : Upper (D 7) (R 7) [36,257,66,18,129] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,129] 13 (by decide) (choices 1) [8,64,128] r38512 c38512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25834
  · exact u25835
  · exact u25836

def r38513 : Route 9 := (fun mask => (mask,id))

def c38513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38513 : Upper (D 7) (R 7) [36,257,66,18,136] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,136] 13 (by decide) (choices 1) [1,64,128] r38513 c38513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25837
  · exact u25838
  · exact u25839

def r38514 : Route 9 := (fun mask => (mask,id))

def c38514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38514 : Upper (D 7) (R 7) [36,257,66,18,160] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,160] 13 (by decide) (choices 1) [1,8,64,128] r38514 c38514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25840
  · exact u25841
  · exact u25842
  · exact u25843

def r38515 : Route 9 := (fun mask => (mask,id))

def c38515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38515 : Upper (D 7) (R 7) [36,257,66,18,192] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,192] 13 (by decide) (choices 1) [1,8,128] r38515 c38515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25844
  · exact u25845
  · exact u25846

def b38516 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 70 41 88 178 210 146 402), lower := (rows 37 259 70 41 88 32 64 128 256), losses := [] }

theorem u38516 : Upper (D 7) (R 7) [36,257,66,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38517 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 70 41 146 248 216 216 472), lower := (rows 37 259 70 41 146 32 64 128 256), losses := [] }

theorem u38517 : Upper (D 7) (R 7) [36,257,66,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38518 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 70 41 152 242 210 210 466), lower := (rows 37 259 70 41 152 32 64 128 256), losses := [] }

theorem u38518 : Upper (D 7) (R 7) [36,257,66,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38519 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 70 41 208 186 218 154 410), lower := (rows 37 259 70 41 208 32 64 128 256), losses := [] }

theorem u38519 : Upper (D 7) (R 7) [36,257,66,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u38519
end Delivery.IrregularNine14.P07
