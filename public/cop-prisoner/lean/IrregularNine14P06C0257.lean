import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0060

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15420 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 104 336 48 69 133 261), lower := (rows 11 131 38 104 336 48 64 128 256), losses := [] }

theorem u15420 : Upper (D 6) (R 6) [10,129,34,96,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15420 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15421 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 11 131 38 268 49 36 80 208 336), lower := (rows 11 131 38 268 49 36 64 128 256), losses := [] }

theorem u15421 : Upper (D 6) (R 6) [10,129,34,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15422 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 268 49 48 68 196 324), lower := (rows 11 131 38 268 49 48 64 128 256), losses := [] }

theorem u15422 : Upper (D 6) (R 6) [10,129,34,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15422 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15423 : Route 9 := (fun mask => (mask,id))

def c15423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15423 : Upper (D 6) (R 6) [10,129,34,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260,33,64] 13 (by decide) (choices 1) [4,16] r15423 c15423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3604
  · exact u3605

def b15424 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 268 81 36 112 240 368), lower := (rows 11 131 38 268 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 80 144 272), good := (rows 46 166 38 300 508 36 64 128 256) }] }

theorem u15424 : Upper (D 6) (R 6) [10,129,34,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15425 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 268 81 48 100 228 356), lower := (rows 11 131 38 268 81 48 64 128 256), losses := [] }

theorem u15425 : Upper (D 6) (R 6) [10,129,34,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15425 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15426 : Route 9 := (fun mask => (mask,id))

def c15426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15426 : Upper (D 6) (R 6) [10,129,34,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260,65,64] 13 (by decide) (choices 1) [4,16,32] r15426 c15426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3606
  · exact u3607
  · exact u3608

def b15427 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 268 84 33 112 240 368), lower := (rows 11 131 38 268 84 33 64 128 256), losses := [] }

theorem u15427 : Upper (D 6) (R 6) [10,129,34,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15428 : Route 9 := (fun mask => (mask,id))

def c15428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15428 : Upper (D 6) (R 6) [10,129,34,260,68,16] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260,68,16] 13 (by decide) (choices 1) [1,32] r15428 c15428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3609
  · exact u3610

def r15429 : Route 9 := (fun mask => (mask,id))

def c15429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15429 : Upper (D 6) (R 6) [10,129,34,260,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260,68,64] 13 (by decide) (choices 1) [1,16,32] r15429 c15429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3611
  · exact u3612
  · exact u3613

def b15430 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 268 112 33 84 212 340), lower := (rows 11 131 38 268 112 33 64 128 256), losses := [] }

theorem u15430 : Upper (D 6) (R 6) [10,129,34,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15431 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,1)], upper := (rows 11 131 38 268 112 36 81 209 337), lower := (rows 11 131 38 268 112 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 21 44 67 131 259), good := (rows 505 465 508 316 112 60 64 128 256) }] }

theorem u15431 : Upper (D 6) (R 6) [10,129,34,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15432 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 268 112 48 69 197 325), lower := (rows 11 131 38 268 112 48 64 128 256), losses := [] }

theorem u15432 : Upper (D 6) (R 6) [10,129,34,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15432 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15433 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 268 112 96 85 149 277), lower := (rows 11 131 38 268 112 96 64 128 256), losses := [] }

theorem u15433 : Upper (D 6) (R 6) [10,129,34,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15434 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 0, region := 36, targets := 1 }], pairs := [(2,0),(2,6),(4,6)], upper := (rows 11 131 38 280 49 36 68 196 324), lower := (rows 11 131 38 280 49 36 64 128 256), losses := [] }

theorem u15434 : Upper (D 6) (R 6) [10,129,34,272,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15435 : Route 9 := (fun mask => (mask,id))

def c15435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15435 : Upper (D 6) (R 6) [10,129,34,272,33,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,33,64] 13 (by decide) (choices 1) [4] r15435 c15435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u3614

def b15436 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 36, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 280 81 36 100 228 356), lower := (rows 11 131 38 280 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) }] }

theorem u15436 : Upper (D 6) (R 6) [10,129,34,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15437 : Route 9 := (fun mask => (mask,id))

def c15437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15437 : Upper (D 6) (R 6) [10,129,34,272,65,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,65,64] 13 (by decide) (choices 1) [4,32] r15437 c15437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3615
  · exact u3616

def b15438 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 280 84 33 100 228 356), lower := (rows 11 131 38 280 84 33 64 128 256), losses := [] }

theorem u15438 : Upper (D 6) (R 6) [10,129,34,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15439 : Route 9 := (fun mask => (mask,id))

def c15439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15439 : Upper (D 6) (R 6) [10,129,34,272,68,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,68,4] 13 (by decide) (choices 1) [1,32] r15439 c15439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3617
  · exact u3618

def r15440 : Route 9 := (fun mask => (mask,id))

def c15440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15440 : Upper (D 6) (R 6) [10,129,34,272,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,68,64] 13 (by decide) (choices 1) [1,4,32] r15440 c15440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3619
  · exact u3620
  · exact u3621

def b15441 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 280 112 33 68 196 324), lower := (rows 11 131 38 280 112 33 64 128 256), losses := [] }

theorem u15441 : Upper (D 6) (R 6) [10,129,34,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15442 : Route 9 := (fun mask => (mask,id))

def c15442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15442 : Upper (D 6) (R 6) [10,129,34,272,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,96,4] 13 (by decide) (choices 1) [1,4] r15442 c15442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3622
  · exact u3623

def b15443 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 280 112 96 69 133 261), lower := (rows 11 131 38 280 112 96 64 128 256), losses := [] }

theorem u15443 : Upper (D 6) (R 6) [10,129,34,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15444 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 296 81 36 84 212 340), lower := (rows 11 131 38 296 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 80 144 272), good := (rows 46 166 38 296 508 36 64 128 256) }] }

theorem u15444 : Upper (D 6) (R 6) [10,129,34,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15445 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 296 81 48 68 196 324), lower := (rows 11 131 38 296 81 48 64 128 256), losses := [] }

theorem u15445 : Upper (D 6) (R 6) [10,129,34,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15445 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15446 : Route 9 := (fun mask => (mask,id))

def c15446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15446 : Upper (D 6) (R 6) [10,129,34,288,65,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,288,65,64] 13 (by decide) (choices 1) [4,16] r15446 c15446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3624
  · exact u3625

def b15447 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 296 84 33 84 212 340), lower := (rows 11 131 38 296 84 33 64 128 256), losses := [] }

theorem u15447 : Upper (D 6) (R 6) [10,129,34,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15448 : Route 9 := (fun mask => (mask,id))

def c15448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15448 : Upper (D 6) (R 6) [10,129,34,288,68,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,288,68,4] 13 (by decide) (choices 1) [1,16] r15448 c15448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3626
  · exact u3627

def r15449 : Route 9 := (fun mask => (mask,id))

def c15449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15449 : Upper (D 6) (R 6) [10,129,34,288,68,16] 13 := by
  apply FastRouting.sound _ _ [10,129,34,288,68,16] 13 (by decide) (choices 1) [1,4] r15449 c15449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3628
  · exact u3629

def r15450 : Route 9 := (fun mask => (mask,id))

def c15450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15450 : Upper (D 6) (R 6) [10,129,34,288,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,288,68,64] 13 (by decide) (choices 1) [1,4,16] r15450 c15450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3630
  · exact u3631
  · exact u3632

def b15451 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 360, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 38 328 21 36 112 240 368), lower := (rows 11 131 38 328 21 36 64 128 256), losses := [] }

theorem u15451 : Upper (D 6) (R 6) [10,129,34,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15452 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 131 38 328 21 48 100 228 356), lower := (rows 11 131 38 328 21 48 64 128 256), losses := [] }

theorem u15452 : Upper (D 6) (R 6) [10,129,34,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15452 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15453 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 360, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 38 328 21 96 116 180 308), lower := (rows 11 131 38 328 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 24 16 120 80 144 272), good := (rows 46 134 38 360 508 96 96 128 256) }] }

theorem u15453 : Upper (D 6) (R 6) [10,129,34,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15454 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 0, region := 36, targets := 1 }], pairs := [(2,0),(2,6),(4,6)], upper := (rows 11 131 38 328 49 36 84 212 340), lower := (rows 11 131 38 328 49 36 64 128 256), losses := [] }

theorem u15454 : Upper (D 6) (R 6) [10,129,34,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15455 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 328 49 48 68 196 324), lower := (rows 11 131 38 328 49 48 64 128 256), losses := [] }

theorem u15455 : Upper (D 6) (R 6) [10,129,34,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15455 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15456 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 134, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 38 328 49 96 84 148 276), lower := (rows 11 131 38 328 49 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 24 16 120 80 144 272), good := (rows 46 134 38 360 508 96 96 128 256) }] }

theorem u15456 : Upper (D 6) (R 6) [10,129,34,320,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15457 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 38 328 81 36 116 180 308), lower := (rows 11 131 38 328 81 36 64 128 256), losses := [] }

theorem u15457 : Upper (D 6) (R 6) [10,129,34,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15458 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 328 81 48 100 164 292), lower := (rows 11 131 38 328 81 48 64 128 256), losses := [] }

theorem u15458 : Upper (D 6) (R 6) [10,129,34,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15458 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15459 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 328 84 33 116 180 308), lower := (rows 11 131 38 328 84 33 64 128 256), losses := [] }

theorem u15459 : Upper (D 6) (R 6) [10,129,34,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15460 : Route 9 := (fun mask => (mask,id))

def c15460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15460 : Upper (D 6) (R 6) [10,129,34,320,68,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320,68,4] 13 (by decide) (choices 1) [1,16,32] r15460 c15460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3633
  · exact u3634
  · exact u3635

def r15461 : Route 9 := (fun mask => (mask,id))

def c15461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15461 : Upper (D 6) (R 6) [10,129,34,320,68,16] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320,68,16] 13 (by decide) (choices 1) [1,4,32] r15461 c15461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3636
  · exact u3637
  · exact u3638

def b15462 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 328 112 33 84 148 276), lower := (rows 11 131 38 328 112 33 64 128 256), losses := [] }

theorem u15462 : Upper (D 6) (R 6) [10,129,34,320,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15463 : Route 9 := (fun mask => (mask,id))

def c15463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15463 : Upper (D 6) (R 6) [10,129,34,320,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320,96,4] 13 (by decide) (choices 1) [1,4,16] r15463 c15463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3639
  · exact u3640
  · exact u3641

def b15464 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 328 112 48 69 133 261), lower := (rows 11 131 38 328 112 48 64 128 256), losses := [] }

theorem u15464 : Upper (D 6) (R 6) [10,129,34,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15464 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15465 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 13 336 34 100 228 356), lower := (rows 11 131 52 13 336 34 64 128 256), losses := [] }

theorem u15465 : Upper (D 6) (R 6) [10,129,48,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15466 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 13 336 36 98 226 354), lower := (rows 11 131 52 13 336 36 64 128 256), losses := [] }

theorem u15466 : Upper (D 6) (R 6) [10,129,48,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15467 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 52 13 336 96 102 166 294), lower := (rows 11 131 52 13 336 96 64 128 256), losses := [] }

theorem u15467 : Upper (D 6) (R 6) [10,129,48,5,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15468 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 52 41 84 34 324 452 324), lower := (rows 11 131 52 41 84 34 64 128 256), losses := [] }

theorem u15468 : Upper (D 6) (R 6) [10,129,48,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15469 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 52 41 84 36 322 450 322), lower := (rows 11 131 52 41 84 36 64 128 256), losses := [] }

theorem u15469 : Upper (D 6) (R 6) [10,129,48,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15470 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 41 84 96 326 390 262), lower := (rows 11 131 52 41 84 96 64 128 256), losses := [] }

theorem u15470 : Upper (D 6) (R 6) [10,129,48,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15471 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 131 52 41 84 288 70 198 326), lower := (rows 11 131 52 41 84 288 64 128 256), losses := [] }

theorem u15471 : Upper (D 6) (R 6) [10,129,48,33,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15471 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15472 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 52 41 276 34 68 196 324), lower := (rows 11 131 52 41 276 34 64 128 256), losses := [] }

theorem u15472 : Upper (D 6) (R 6) [10,129,48,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15473 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 41 276 36 66 194 322), lower := (rows 11 131 52 41 276 36 64 128 256), losses := [] }

theorem u15473 : Upper (D 6) (R 6) [10,129,48,33,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15474 : Route 9 := (fun mask => (mask,id))

def c15474 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15474 : Upper (D 6) (R 6) [10,129,48,33,260,64] 13 := by
  apply FastRouting.sound _ _ [10,129,48,33,260,64] 13 (by decide) (choices 1) [2,4] r15474 c15474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3642
  · exact u3643

def b15475 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 52 41 336 34 68 196 324), lower := (rows 11 131 52 41 336 34 64 128 256), losses := [] }

theorem u15475 : Upper (D 6) (R 6) [10,129,48,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15476 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 41 336 36 70 198 326), lower := (rows 11 131 52 41 336 36 64 128 256), losses := [] }

theorem u15476 : Upper (D 6) (R 6) [10,129,48,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15477 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 52 41 336 96 70 134 262), lower := (rows 11 131 52 41 336 96 64 128 256), losses := [] }

theorem u15477 : Upper (D 6) (R 6) [10,129,48,33,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15478 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 73 84 34 356 420 292), lower := (rows 11 131 52 73 84 34 64 128 256), losses := [] }

theorem u15478 : Upper (D 6) (R 6) [10,129,48,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15479 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 73 84 36 354 418 290), lower := (rows 11 131 52 73 84 36 64 128 256), losses := [] }

theorem u15479 : Upper (D 6) (R 6) [10,129,48,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15479
end Delivery.IrregularNine14.P06
