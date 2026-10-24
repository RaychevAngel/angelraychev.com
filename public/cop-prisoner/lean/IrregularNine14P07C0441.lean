import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0158
import IrregularNine14P07C0159

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26460 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 266 70 56 145 160 67 195 323), lower := (rows 37 266 70 56 145 160 64 128 256), losses := [] }

theorem u26460 : Upper (D 7) (R 7) [36,264,66,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26461 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 70 56 146 33 193 193 449), lower := (rows 37 266 70 56 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 97 161 289), good := (rows 453 286 70 478 146 449 64 128 256) }] }

theorem u26461 : Upper (D 7) (R 7) [36,264,66,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26462 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 56 146 96 193 129 385), lower := (rows 37 266 70 56 146 96 64 128 256), losses := [] }

theorem u26462 : Upper (D 7) (R 7) [36,264,66,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26463 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 266 70 56 146 160 65 193 321), lower := (rows 37 266 70 56 146 160 64 128 256), losses := [] }

theorem u26463 : Upper (D 7) (R 7) [36,264,66,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26464 : Route 9 := (fun mask => (mask,id))

def c26464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26464 : Upper (D 7) (R 7) [36,264,66,48,192,1] 13 := by
  apply FastRouting.sound _ _ [36,264,66,48,192,1] 13 (by decide) (choices 1) [1,2,128] r26464 c26464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9523
  · exact u9524
  · exact u9525

def b26465 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 208, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,5)], upper := (rows 37 266 70 56 208 34 193 129 385), lower := (rows 37 266 70 56 208 34 64 128 256), losses := [] }

theorem u26465 : Upper (D 7) (R 7) [36,264,66,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26466 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 266 70 56 208 160 67 131 259), lower := (rows 37 266 70 56 208 160 64 128 256), losses := [] }

theorem u26466 : Upper (D 7) (R 7) [36,264,66,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26467 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,7)], upper := (rows 37 266 70 73 50 33 208 144 400), lower := (rows 37 266 70 73 50 33 64 128 256), losses := [] }

theorem u26467 : Upper (D 7) (R 7) [36,264,66,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26468 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 73 50 48 193 129 385), lower := (rows 37 266 70 73 50 48 64 128 256), losses := [] }

theorem u26468 : Upper (D 7) (R 7) [36,264,66,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26468 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26469 : Route 9 := (fun mask => (mask,id))

def c26469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26469 : Upper (D 7) (R 7) [36,264,66,65,34,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,65,34,128] 13 (by decide) (choices 1) [1,16,128] r26469 c26469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9526
  · exact u9527
  · exact u9528

def b26470 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 266 70 73 145 34 240 176 432), lower := (rows 37 266 70 73 145 34 64 128 256), losses := [] }

theorem u26470 : Upper (D 7) (R 7) [36,264,66,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26471 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 434, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 37 266 70 73 145 48 226 162 418), lower := (rows 37 266 70 73 145 48 64 128 256), losses := [] }

theorem u26471 : Upper (D 7) (R 7) [36,264,66,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26471 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26472 : Route 9 := (fun mask => (mask,id))

def c26472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26472 : Upper (D 7) (R 7) [36,264,66,65,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,65,129,128] 13 (by decide) (choices 1) [2,16,32] r26472 c26472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9529
  · exact u9530
  · exact u9531

def b26473 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 70 73 146 33 240 176 432), lower := (rows 37 266 70 73 146 33 64 128 256), losses := [] }

theorem u26473 : Upper (D 7) (R 7) [36,264,66,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26474 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 37 266 70 73 146 48 225 161 417), lower := (rows 37 266 70 73 146 48 64 128 256), losses := [] }

theorem u26474 : Upper (D 7) (R 7) [36,264,66,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26474 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26475 : Route 9 := (fun mask => (mask,id))

def c26475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26475 : Upper (D 7) (R 7) [36,264,66,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,65,130,128] 13 (by decide) (choices 1) [1,16,32] r26475 c26475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9532
  · exact u9533
  · exact u9534

def b26476 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 70 73 176 33 210 146 402), lower := (rows 37 266 70 73 176 33 64 128 256), losses := [] }

theorem u26476 : Upper (D 7) (R 7) [36,264,66,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26477 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 266 70 73 176 34 209 145 401), lower := (rows 37 266 70 73 176 34 64 128 256), losses := [] }

theorem u26477 : Upper (D 7) (R 7) [36,264,66,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26478 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 73 176 48 195 131 387), lower := (rows 37 266 70 73 176 48 64 128 256), losses := [] }

theorem u26478 : Upper (D 7) (R 7) [36,264,66,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26478 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26479 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 70 73 176 160 83 147 275), lower := (rows 37 266 70 73 176 160 64 128 256), losses := [] }

theorem u26479 : Upper (D 7) (R 7) [36,264,66,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26480 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,7)], upper := (rows 37 266 70 88 50 33 193 129 385), lower := (rows 37 266 70 88 50 33 64 128 256), losses := [] }

theorem u26480 : Upper (D 7) (R 7) [36,264,66,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26481 : Route 9 := (fun mask => (mask,id))

def c26481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26481 : Upper (D 7) (R 7) [36,264,66,80,34,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,80,34,128] 13 (by decide) (choices 1) [1,128] r26481 c26481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9535
  · exact u9536

def b26482 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 266 70 88 145 33 226 162 418), lower := (rows 37 266 70 88 145 33 64 128 256), losses := [] }

theorem u26482 : Upper (D 7) (R 7) [36,264,66,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26483 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 266 70 88 145 34 225 161 417), lower := (rows 37 266 70 88 145 34 64 128 256), losses := [] }

theorem u26483 : Upper (D 7) (R 7) [36,264,66,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26484 : Route 9 := (fun mask => (mask,id))

def c26484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26484 : Upper (D 7) (R 7) [36,264,66,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,80,129,128] 13 (by decide) (choices 1) [1,2,32] r26484 c26484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9537
  · exact u9538
  · exact u9539

def b26485 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 266 70 88 146 33 225 161 417), lower := (rows 37 266 70 88 146 33 64 128 256), losses := [] }

theorem u26485 : Upper (D 7) (R 7) [36,264,66,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26486 : Route 9 := (fun mask => (mask,id))

def c26486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26486 : Upper (D 7) (R 7) [36,264,66,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,80,130,128] 13 (by decide) (choices 1) [1,32] r26486 c26486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9540
  · exact u9541

def b26487 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 266 70 88 176 33 195 131 387), lower := (rows 37 266 70 88 176 33 64 128 256), losses := [] }

theorem u26487 : Upper (D 7) (R 7) [36,264,66,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26488 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 266 70 88 176 34 193 129 385), lower := (rows 37 266 70 88 176 34 64 128 256), losses := [] }

theorem u26488 : Upper (D 7) (R 7) [36,264,66,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26489 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 70 88 176 160 67 131 259), lower := (rows 37 266 70 88 176 160 64 128 256), losses := [] }

theorem u26489 : Upper (D 7) (R 7) [36,264,66,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26490 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 70 104 145 33 210 146 402), lower := (rows 37 266 70 104 145 33 64 128 256), losses := [] }

theorem u26490 : Upper (D 7) (R 7) [36,264,66,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26491 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 266 70 104 145 34 209 145 401), lower := (rows 37 266 70 104 145 34 64 128 256), losses := [] }

theorem u26491 : Upper (D 7) (R 7) [36,264,66,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26492 : Route 9 := (fun mask => (mask,id))

def c26492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26492 : Upper (D 7) (R 7) [36,264,66,96,129,16] 13 := by
  apply FastRouting.sound _ _ [36,264,66,96,129,16] 13 (by decide) (choices 1) [1,2,128] r26492 c26492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9542
  · exact u9543
  · exact u9544

def r26493 : Route 9 := (fun mask => (mask,id))

def c26493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26493 : Upper (D 7) (R 7) [36,264,66,96,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,96,129,128] 13 (by decide) (choices 1) [1,2,16] r26493 c26493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9545
  · exact u9546
  · exact u9547

def b26494 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 70 104 146 33 209 145 401), lower := (rows 37 266 70 104 146 33 64 128 256), losses := [] }

theorem u26494 : Upper (D 7) (R 7) [36,264,66,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26495 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 37 266 70 104 146 48 193 129 385), lower := (rows 37 266 70 104 146 48 64 128 256), losses := [] }

theorem u26495 : Upper (D 7) (R 7) [36,264,66,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26495 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26496 : Route 9 := (fun mask => (mask,id))

def c26496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26496 : Upper (D 7) (R 7) [36,264,66,96,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,96,130,128] 13 (by decide) (choices 1) [1,16] r26496 c26496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9548
  · exact u9549

def b26497 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 266 70 137 19 48 224 224 480), lower := (rows 37 266 70 137 19 48 64 128 256), losses := [] }

theorem u26497 : Upper (D 7) (R 7) [36,264,66,129,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26497 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26498 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 137 19 96 240 176 432), lower := (rows 37 266 70 137 19 96 64 128 256), losses := [] }

theorem u26498 : Upper (D 7) (R 7) [36,264,66,129,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26499 : Route 9 := (fun mask => (mask,id))

def c26499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26499 : Upper (D 7) (R 7) [36,264,66,129,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,3,128] 13 (by decide) (choices 1) [16,32] r26499 c26499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9550
  · exact u9551

def b26500 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 266 70 137 50 33 208 208 464), lower := (rows 37 266 70 137 50 33 64 128 256), losses := [] }

theorem u26500 : Upper (D 7) (R 7) [36,264,66,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26501 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 266 70 137 50 48 193 193 449), lower := (rows 37 266 70 137 50 48 64 128 256), losses := [] }

theorem u26501 : Upper (D 7) (R 7) [36,264,66,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26501 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26502 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 137 50 96 209 145 401), lower := (rows 37 266 70 137 50 96 64 128 256), losses := [] }

theorem u26502 : Upper (D 7) (R 7) [36,264,66,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26503 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,6)], upper := (rows 37 266 70 137 50 160 81 209 337), lower := (rows 37 266 70 137 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 36 314 86 168 50 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 18 168 0 128 256), good := (rows 37 314 22 169 50 160 0 160 256) }] }

theorem u26503 : Upper (D 7) (R 7) [36,264,66,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26504 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 37 266 70 137 81 34 240 176 432), lower := (rows 37 266 70 137 81 34 64 128 256), losses := [] }

theorem u26504 : Upper (D 7) (R 7) [36,264,66,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26505 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 266 70 137 81 48 226 162 418), lower := (rows 37 266 70 137 81 48 64 128 256), losses := [] }

theorem u26505 : Upper (D 7) (R 7) [36,264,66,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26505 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26506 : Route 9 := (fun mask => (mask,id))

def c26506 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26506 : Upper (D 7) (R 7) [36,264,66,129,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,65,128] 13 (by decide) (choices 1) [2,16,32] r26506 c26506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9552
  · exact u9553
  · exact u9554

def b26507 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 70 137 112 33 210 146 402), lower := (rows 37 266 70 137 112 33 64 128 256), losses := [] }

theorem u26507 : Upper (D 7) (R 7) [36,264,66,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26508 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 37 266 70 137 112 34 209 145 401), lower := (rows 37 266 70 137 112 34 64 128 256), losses := [] }

theorem u26508 : Upper (D 7) (R 7) [36,264,66,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26509 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 266 70 137 112 48 195 131 387), lower := (rows 37 266 70 137 112 48 64 128 256), losses := [] }

theorem u26509 : Upper (D 7) (R 7) [36,264,66,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26509 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26510 : Route 9 := (fun mask => (mask,id))

def c26510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26510 : Upper (D 7) (R 7) [36,264,66,129,96,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,96,128] 13 (by decide) (choices 1) [1,2,16] r26510 c26510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9555
  · exact u9556
  · exact u9557

def b26511 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 266 70 137 146 33 112 240 368), lower := (rows 37 266 70 137 146 33 64 128 256), losses := [] }

theorem u26511 : Upper (D 7) (R 7) [36,264,66,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26512 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 37 266 70 137 146 48 97 225 353), lower := (rows 37 266 70 137 146 48 64 128 256), losses := [] }

theorem u26512 : Upper (D 7) (R 7) [36,264,66,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26512 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26513 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 137 146 96 113 177 305), lower := (rows 37 266 70 137 146 96 64 128 256), losses := [] }

theorem u26513 : Upper (D 7) (R 7) [36,264,66,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26514 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 48, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 266 70 137 176 33 82 210 338), lower := (rows 37 266 70 137 176 33 64 128 256), losses := [] }

theorem u26514 : Upper (D 7) (R 7) [36,264,66,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26515 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 70 137 176 34 81 209 337), lower := (rows 37 266 70 137 176 34 64 128 256), losses := [] }

theorem u26515 : Upper (D 7) (R 7) [36,264,66,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26516 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 137 176 48 67 195 323), lower := (rows 37 266 70 137 176 48 64 128 256), losses := [] }

theorem u26516 : Upper (D 7) (R 7) [36,264,66,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26516 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26517 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 137 176 96 83 147 275), lower := (rows 37 266 70 137 176 96 64 128 256), losses := [] }

theorem u26517 : Upper (D 7) (R 7) [36,264,66,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26518 : Route 9 := (fun mask => (mask,id))

def c26518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26518 : Upper (D 7) (R 7) [36,264,66,129,192,1] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,192,1] 13 (by decide) (choices 1) [2,16,32] r26518 c26518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9558
  · exact u9559
  · exact u9560

def b26519 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 70 137 208 34 113 177 305), lower := (rows 37 266 70 137 208 34 64 128 256), losses := [] }

theorem u26519 : Upper (D 7) (R 7) [36,264,66,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26519
end Delivery.IrregularNine14.P07
