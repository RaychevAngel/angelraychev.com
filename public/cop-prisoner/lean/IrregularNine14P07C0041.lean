import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0002

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2460 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 268 168 81 33 80 130 386), lower := (rows 7 98 268 168 81 33 80 128 256), losses := [] }

theorem u2460 : Upper (D 7) (R 7) [6,96,264,160,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2460 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2461 : Route 9 := (fun mask => (mask,id))

def c2461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2461 : Upper (D 7) (R 7) [6,96,264,160,65,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,65,1,128] 13 (by decide) (choices 1) [2,16] r2461 c2461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u156
  · exact u157

def b2462 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 268 168 146 33 65 208 336), lower := (rows 7 98 268 168 146 33 65 128 256), losses := [] }

theorem u2462 : Upper (D 7) (R 7) [6,96,264,160,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2463 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 82, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 7 98 268 168 146 33 80 193 321), lower := (rows 7 98 268 168 146 33 80 128 256), losses := [] }

theorem u2463 : Upper (D 7) (R 7) [6,96,264,160,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2463 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2464 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 268 168 208 33 65 146 274), lower := (rows 7 98 268 168 208 33 65 128 256), losses := [] }

theorem u2464 : Upper (D 7) (R 7) [6,96,264,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2465 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 82, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 7 98 268 168 208 33 66 145 273), lower := (rows 7 98 268 168 208 33 66 128 256), losses := [] }

theorem u2465 : Upper (D 7) (R 7) [6,96,264,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2466 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 268 168 208 33 80 131 259), lower := (rows 7 98 268 168 208 33 80 128 256), losses := [] }

theorem u2466 : Upper (D 7) (R 7) [6,96,264,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2466 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2467 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 388, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 292 25 146 33 72 192 448), lower := (rows 7 98 292 25 146 33 72 128 256), losses := [] }

theorem u2467 : Upper (D 7) (R 7) [6,96,288,17,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2467 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2468 : Route 9 := (fun mask => (mask,id))

def c2468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2468 : Upper (D 7) (R 7) [6,96,288,17,130,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,130,1,128] 13 (by decide) (choices 1) [8,64] r2468 c2468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u158
  · exact u159

def b2469 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 292 25 146 160 65 200 328), lower := (rows 7 98 292 25 146 160 65 128 256), losses := [] }

theorem u2469 : Upper (D 7) (R 7) [6,96,288,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2470 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 292 25 146 160 72 193 321), lower := (rows 7 98 292 25 146 160 72 128 256), losses := [] }

theorem u2470 : Upper (D 7) (R 7) [6,96,288,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2470 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2471 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 292 25 208 33 66 136 392), lower := (rows 7 98 292 25 208 33 66 128 256), losses := [] }

theorem u2471 : Upper (D 7) (R 7) [6,96,288,17,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2472 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 388, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 292 25 208 33 72 130 386), lower := (rows 7 98 292 25 208 33 72 128 256), losses := [] }

theorem u2472 : Upper (D 7) (R 7) [6,96,288,17,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2472 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2473 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 292 25 208 33 192 138 266), lower := (rows 7 98 292 25 208 33 192 128 256), losses := [] }

theorem u2473 : Upper (D 7) (R 7) [6,96,288,17,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2474 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 292 25 208 160 65 138 266), lower := (rows 7 98 292 25 208 160 65 128 256), losses := [] }

theorem u2474 : Upper (D 7) (R 7) [6,96,288,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2475 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 292 25 208 160 66 137 265), lower := (rows 7 98 292 25 208 160 66 128 256), losses := [] }

theorem u2475 : Upper (D 7) (R 7) [6,96,288,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 261, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 292 25 208 160 72 131 259), lower := (rows 7 98 292 25 208 160 72 128 256), losses := [] }

theorem u2476 : Upper (D 7) (R 7) [6,96,288,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2476 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2477 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(3,5),(4,5)], upper := (rows 7 98 292 26 145 33 72 192 448), lower := (rows 7 98 292 26 145 33 72 128 256), losses := [] }

theorem u2477 : Upper (D 7) (R 7) [6,96,288,18,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2477 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2478 : Route 9 := (fun mask => (mask,id))

def c2478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2478 : Upper (D 7) (R 7) [6,96,288,18,129,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,18,129,1,128] 13 (by decide) (choices 1) [8,64] r2478 c2478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u160
  · exact u161

def b2479 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 292 26 145 160 65 200 328), lower := (rows 7 98 292 26 145 160 65 128 256), losses := [] }

theorem u2479 : Upper (D 7) (R 7) [6,96,288,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2480 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 292 26 145 160 72 193 321), lower := (rows 7 98 292 26 145 160 72 128 256), losses := [] }

theorem u2480 : Upper (D 7) (R 7) [6,96,288,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2480 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2481 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 292 26 152 33 65 192 448), lower := (rows 7 98 292 26 152 33 65 128 256), losses := [] }

theorem u2481 : Upper (D 7) (R 7) [6,96,288,18,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2482 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 295, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 292 26 152 33 192 193 321), lower := (rows 7 98 292 26 152 33 192 128 256), losses := [] }

theorem u2482 : Upper (D 7) (R 7) [6,96,288,18,136,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2483 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 7 98 292 73 145 48 66 136 392), lower := (rows 7 98 292 73 145 48 66 128 256), losses := [] }

theorem u2483 : Upper (D 7) (R 7) [6,96,288,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2483 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2484 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 292 73 145 48 72 130 386), lower := (rows 7 98 292 73 145 48 72 128 256), losses := [] }

theorem u2484 : Upper (D 7) (R 7) [6,96,288,65,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2484 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2485 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 292 73 145 48 192 138 266), lower := (rows 7 98 292 73 145 48 192 128 256), losses := [] }

theorem u2485 : Upper (D 7) (R 7) [6,96,288,65,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2485 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2486 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 7 98 292 73 145 160 66 152 280), lower := (rows 7 98 292 73 145 160 66 128 256), losses := [] }

theorem u2486 : Upper (D 7) (R 7) [6,96,288,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2487 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 73 145 160 72 146 274), lower := (rows 7 98 292 73 145 160 72 128 256), losses := [] }

theorem u2487 : Upper (D 7) (R 7) [6,96,288,65,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2487 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2488 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 292 73 145 160 80 138 266), lower := (rows 7 98 292 73 145 160 80 128 256), losses := [] }

theorem u2488 : Upper (D 7) (R 7) [6,96,288,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2488 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2489 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 111, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 292 73 146 33 72 144 400), lower := (rows 7 98 292 73 146 33 72 128 256), losses := [] }

theorem u2489 : Upper (D 7) (R 7) [6,96,288,65,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2489 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2490 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 420, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 292 73 146 33 80 136 392), lower := (rows 7 98 292 73 146 33 80 128 256), losses := [] }

theorem u2490 : Upper (D 7) (R 7) [6,96,288,65,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2490 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2491 : Route 9 := (fun mask => (mask,id))

def c2491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2491 : Upper (D 7) (R 7) [6,96,288,65,130,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,130,1,128] 13 (by decide) (choices 1) [8,16] r2491 c2491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u162
  · exact u163

def b2492 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 3, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 7 98 292 73 146 160 65 152 280), lower := (rows 7 98 292 73 146 160 65 128 256), losses := [] }

theorem u2492 : Upper (D 7) (R 7) [6,96,288,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2493 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 73 146 160 72 145 273), lower := (rows 7 98 292 73 146 160 72 128 256), losses := [] }

theorem u2493 : Upper (D 7) (R 7) [6,96,288,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2493 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2494 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 292 73 146 160 80 137 265), lower := (rows 7 98 292 73 146 160 80 128 256), losses := [] }

theorem u2494 : Upper (D 7) (R 7) [6,96,288,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2494 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2495 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 7 98 292 73 152 33 66 144 400), lower := (rows 7 98 292 73 152 33 66 128 256), losses := [] }

theorem u2495 : Upper (D 7) (R 7) [6,96,288,65,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2496 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 292 73 152 33 80 130 386), lower := (rows 7 98 292 73 152 33 80 128 256), losses := [] }

theorem u2496 : Upper (D 7) (R 7) [6,96,288,65,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2496 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2497 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 292 73 152 33 192 146 274), lower := (rows 7 98 292 73 152 33 192 128 256), losses := [{ target := 7, region := (rows 17 10 20 8 16 57 64 0 272), good := (rows 39 98 292 107 319 33 64 0 256) }] }

theorem u2497 : Upper (D 7) (R 7) [6,96,288,65,136,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2498 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 3, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 7 98 292 73 152 160 65 146 274), lower := (rows 7 98 292 73 152 160 65 128 256), losses := [] }

theorem u2498 : Upper (D 7) (R 7) [6,96,288,65,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2499 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 7 98 292 73 152 160 66 145 273), lower := (rows 7 98 292 73 152 160 66 128 256), losses := [] }

theorem u2499 : Upper (D 7) (R 7) [6,96,288,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2500 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 292 73 152 160 80 131 259), lower := (rows 7 98 292 73 152 160 80 128 256), losses := [] }

theorem u2500 : Upper (D 7) (R 7) [6,96,288,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2500 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2501 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 292 88 145 33 66 136 392), lower := (rows 7 98 292 88 145 33 66 128 256), losses := [] }

theorem u2501 : Upper (D 7) (R 7) [6,96,288,80,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2502 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 88 145 33 72 130 386), lower := (rows 7 98 292 88 145 33 72 128 256), losses := [] }

theorem u2502 : Upper (D 7) (R 7) [6,96,288,80,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2502 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2503 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 292 88 145 33 192 138 266), lower := (rows 7 98 292 88 145 33 192 128 256), losses := [] }

theorem u2503 : Upper (D 7) (R 7) [6,96,288,80,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2504 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 292 88 145 160 65 138 266), lower := (rows 7 98 292 88 145 160 65 128 256), losses := [] }

theorem u2504 : Upper (D 7) (R 7) [6,96,288,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2505 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 292 88 145 160 66 137 265), lower := (rows 7 98 292 88 145 160 66 128 256), losses := [] }

theorem u2505 : Upper (D 7) (R 7) [6,96,288,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2506 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 88 145 160 72 131 259), lower := (rows 7 98 292 88 145 160 72 128 256), losses := [] }

theorem u2506 : Upper (D 7) (R 7) [6,96,288,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2506 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2507 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 292 88 146 33 65 136 392), lower := (rows 7 98 292 88 146 33 65 128 256), losses := [] }

theorem u2507 : Upper (D 7) (R 7) [6,96,288,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2508 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 98 292 88 146 33 72 129 385), lower := (rows 7 98 292 88 146 33 72 128 256), losses := [] }

theorem u2508 : Upper (D 7) (R 7) [6,96,288,80,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2508 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2509 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 98 292 88 146 33 192 137 265), lower := (rows 7 98 292 88 146 33 192 128 256), losses := [] }

theorem u2509 : Upper (D 7) (R 7) [6,96,288,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2510 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 292 88 146 160 65 137 265), lower := (rows 7 98 292 88 146 160 65 128 256), losses := [] }

theorem u2510 : Upper (D 7) (R 7) [6,96,288,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2511 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 88 146 160 72 129 257), lower := (rows 7 98 292 88 146 160 72 128 256), losses := [] }

theorem u2511 : Upper (D 7) (R 7) [6,96,288,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2511 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2512 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 404, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 292 137 146 33 72 208 336), lower := (rows 7 98 292 137 146 33 72 128 256), losses := [] }

theorem u2512 : Upper (D 7) (R 7) [6,96,288,129,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2512 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2513 : Route 9 := (fun mask => (mask,id))

def c2513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2513 : Upper (D 7) (R 7) [6,96,288,129,130,1,16] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,130,1,16] 13 (by decide) (choices 1) [8,64] r2513 c2513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u164
  · exact u165

def b2514 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 404, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 292 137 146 40 65 208 336), lower := (rows 7 98 292 137 146 40 65 128 256), losses := [] }

theorem u2514 : Upper (D 7) (R 7) [6,96,288,129,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2514 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2515 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 292 137 146 40 80 193 321), lower := (rows 7 98 292 137 146 40 80 128 256), losses := [] }

theorem u2515 : Upper (D 7) (R 7) [6,96,288,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2515 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2516 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 292 137 208 33 66 152 280), lower := (rows 7 98 292 137 208 33 66 128 256), losses := [] }

theorem u2516 : Upper (D 7) (R 7) [6,96,288,129,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2517 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 292 137 208 33 72 146 274), lower := (rows 7 98 292 137 208 33 72 128 256), losses := [] }

theorem u2517 : Upper (D 7) (R 7) [6,96,288,129,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2517 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2518 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 292 137 208 33 80 138 266), lower := (rows 7 98 292 137 208 33 80 128 256), losses := [] }

theorem u2518 : Upper (D 7) (R 7) [6,96,288,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2518 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2519 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 404, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 292 137 208 40 65 146 274), lower := (rows 7 98 292 137 208 40 65 128 256), losses := [] }

theorem u2519 : Upper (D 7) (R 7) [6,96,288,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2519 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P07
