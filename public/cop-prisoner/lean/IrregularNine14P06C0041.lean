import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0002

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2460 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 1, region := 80, targets := 2 },{ cop := 1, region := 80, targets := 4 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 35 134 280 112 36 65 196 324), lower := (rows 11 35 134 280 112 36 65 128 256), losses := [] }

theorem u2460 : Upper (D 6) (R 6) [10,33,130,272,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2461 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 134 280 112 36 68 193 321), lower := (rows 11 35 134 280 112 36 68 128 256), losses := [] }

theorem u2461 : Upper (D 6) (R 6) [10,33,130,272,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2462 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 11 35 134 328 81 36 68 176 304), lower := (rows 11 35 134 328 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 144 272), good := (rows 10 98 230 360 504 100 100 128 256) }] }

theorem u2462 : Upper (D 6) (R 6) [10,33,130,320,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2463 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 35 134 328 81 36 80 164 292), lower := (rows 11 35 134 328 81 36 80 128 256), losses := [] }

theorem u2463 : Upper (D 6) (R 6) [10,33,130,320,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2463 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2464 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 1, region := 80, targets := 2 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 35 134 328 81 36 96 148 276), lower := (rows 11 35 134 328 81 36 96 128 256), losses := [] }

theorem u2464 : Upper (D 6) (R 6) [10,33,130,320,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2465 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 134 328 84 36 65 176 304), lower := (rows 11 35 134 328 84 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 5 88 80 119 64 216 344), good := (rows 430 38 166 504 508 36 508 128 256) }] }

theorem u2465 : Upper (D 6) (R 6) [10,33,130,320,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2466 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 134 328 84 36 80 161 289), lower := (rows 11 35 134 328 84 36 80 128 256), losses := [] }

theorem u2466 : Upper (D 6) (R 6) [10,33,130,320,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2466 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2467 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 11 35 134 328 84 36 96 145 273), lower := (rows 11 35 134 328 84 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 15 52 52 118 130 258), good := (rows 457 505 508 328 124 124 112 128 256) }] }

theorem u2467 : Upper (D 6) (R 6) [10,33,130,320,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2468 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 11 35 134 328 84 48 65 164 292), lower := (rows 11 35 134 328 84 48 65 128 256), losses := [] }

theorem u2468 : Upper (D 6) (R 6) [10,33,130,320,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2468 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2469 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 134 328 84 48 68 161 289), lower := (rows 11 35 134 328 84 48 68 128 256), losses := [] }

theorem u2469 : Upper (D 6) (R 6) [10,33,130,320,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2469 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2470 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 11 35 134 328 84 48 96 133 261), lower := (rows 11 35 134 328 84 48 96 128 256), losses := [] }

theorem u2470 : Upper (D 6) (R 6) [10,33,130,320,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2470 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2471 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 80, targets := 2 },{ cop := 1, region := 80, targets := 4 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 11 35 134 328 112 36 65 148 276), lower := (rows 11 35 134 328 112 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 88 88 103 64 193 321), good := (rows 446 422 166 504 504 36 508 128 256) }] }

theorem u2471 : Upper (D 6) (R 6) [10,33,130,320,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2472 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 134 328 112 36 68 145 273), lower := (rows 11 35 134 328 112 36 68 128 256), losses := [] }

theorem u2472 : Upper (D 6) (R 6) [10,33,130,320,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2473 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 134 328 112 36 80 133 261), lower := (rows 11 35 134 328 112 36 80 128 256), losses := [] }

theorem u2473 : Upper (D 6) (R 6) [10,33,130,320,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2473 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2474 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 13 304 96 66 196 324), lower := (rows 11 35 148 13 304 96 66 128 256), losses := [] }

theorem u2474 : Upper (D 6) (R 6) [10,33,144,5,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2475 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 11 35 148 13 304 96 68 194 322), lower := (rows 11 35 148 13 304 96 68 128 256), losses := [{ target := 6, region := (rows 37 50 4 76 16 32 0 128 256), good := (rows 11 35 159 13 307 43 13 128 256) }] }

theorem u2475 : Upper (D 6) (R 6) [10,33,144,5,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 13 336 96 66 164 292), lower := (rows 11 35 148 13 336 96 66 128 256), losses := [] }

theorem u2476 : Upper (D 6) (R 6) [10,33,144,5,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2477 : Route 9 := (fun mask => (mask,id))

def c2477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2477 : Upper (D 6) (R 6) [10,33,144,5,320,64,4] 13 := by
  apply FastRouting.sound _ _ [10,33,144,5,320,64,4] 13 (by decide) (choices 1) [2,32] r2477 c2477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u148
  · exact u149

def b2478 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 35 148 13 336 96 96 134 262), lower := (rows 11 35 148 13 336 96 96 128 256), losses := [] }

theorem u2478 : Upper (D 6) (R 6) [10,33,144,5,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2479 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 148 73 304 36 66 196 324), lower := (rows 11 35 148 73 304 36 66 128 256), losses := [] }

theorem u2479 : Upper (D 6) (R 6) [10,33,144,65,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2480 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 11 35 148 73 304 36 68 194 322), lower := (rows 11 35 148 73 304 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 16 100 100 128 256), good := (rows 9 105 244 105 368 100 100 128 256) }] }

theorem u2480 : Upper (D 6) (R 6) [10,33,144,65,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2481 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 148 73 336 36 66 164 292), lower := (rows 11 35 148 73 336 36 66 128 256), losses := [] }

theorem u2481 : Upper (D 6) (R 6) [10,33,144,65,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2482 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 11 35 148 73 336 36 68 162 290), lower := (rows 11 35 148 73 336 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 16 100 100 128 256), good := (rows 9 105 244 105 368 100 100 128 256) }] }

theorem u2482 : Upper (D 6) (R 6) [10,33,144,65,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2483 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 73 336 36 96 134 262), lower := (rows 11 35 148 73 336 36 96 128 256), losses := [] }

theorem u2483 : Upper (D 6) (R 6) [10,33,144,65,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2484 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 265 52 96 66 196 324), lower := (rows 11 35 148 265 52 96 66 128 256), losses := [] }

theorem u2484 : Upper (D 6) (R 6) [10,33,144,257,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2485 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 265 52 96 68 194 322), lower := (rows 11 35 148 265 52 96 68 128 256), losses := [] }

theorem u2485 : Upper (D 6) (R 6) [10,33,144,257,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2486 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 265 84 96 66 164 292), lower := (rows 11 35 148 265 84 96 66 128 256), losses := [] }

theorem u2486 : Upper (D 6) (R 6) [10,33,144,257,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2487 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 267, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 265 84 96 68 162 290), lower := (rows 11 35 148 265 84 96 68 128 256), losses := [] }

theorem u2487 : Upper (D 6) (R 6) [10,33,144,257,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2488 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 265 84 96 96 134 262), lower := (rows 11 35 148 265 84 96 96 128 256), losses := [] }

theorem u2488 : Upper (D 6) (R 6) [10,33,144,257,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2489 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 265 112 36 66 196 324), lower := (rows 11 35 148 265 112 36 66 128 256), losses := [] }

theorem u2489 : Upper (D 6) (R 6) [10,33,144,257,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2490 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 265 112 36 68 194 322), lower := (rows 11 35 148 265 112 36 68 128 256), losses := [] }

theorem u2490 : Upper (D 6) (R 6) [10,33,144,257,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2491 : Route 9 := (fun mask => (mask,id))

def c2491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2491 : Upper (D 6) (R 6) [10,33,144,260,36,64,1] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,36,64,1] 13 (by decide) (choices 1) [2,64] r2491 c2491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u150
  · exact u151

def r2492 : Route 9 := (fun mask => (mask,id))

def c2492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2492 : Upper (D 6) (R 6) [10,33,144,260,36,64,2] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,36,64,2] 13 (by decide) (choices 1) [1,64] r2492 c2492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u152
  · exact u153

def b2493 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 148 268 81 96 66 164 292), lower := (rows 11 35 148 268 81 96 66 128 256), losses := [] }

theorem u2493 : Upper (D 6) (R 6) [10,33,144,260,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2494 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 35 148 268 81 96 68 162 290), lower := (rows 11 35 148 268 81 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 125 92 131 259), good := (rows 490 418 252 364 508 96 100 128 256) }] }

theorem u2494 : Upper (D 6) (R 6) [10,33,144,260,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2495 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 115, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 35 148 268 81 96 96 134 262), lower := (rows 11 35 148 268 81 96 96 128 256), losses := [] }

theorem u2495 : Upper (D 6) (R 6) [10,33,144,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2496 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 148 268 82 96 65 164 292), lower := (rows 11 35 148 268 82 96 65 128 256), losses := [] }

theorem u2496 : Upper (D 6) (R 6) [10,33,144,260,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2497 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(3,1),(4,0)], upper := (rows 11 35 148 268 82 96 68 161 289), lower := (rows 11 35 148 268 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 125 76 128 256), good := (rows 122 50 244 364 114 96 100 128 256) },{ target := 1, region := (rows 1 0 20 24 16 125 92 131 259), good := (rows 489 417 252 364 508 96 100 128 256) }] }

theorem u2497 : Upper (D 6) (R 6) [10,33,144,260,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2498 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 11 35 148 268 82 96 96 133 261), lower := (rows 11 35 148 268 82 96 96 128 256), losses := [] }

theorem u2498 : Upper (D 6) (R 6) [10,33,144,260,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2499 : Route 9 := (fun mask => (mask,id))

def c2499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2499 : Upper (D 6) (R 6) [10,33,144,260,68,64,1] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,68,64,1] 13 (by decide) (choices 1) [2,32] r2499 c2499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u154
  · exact u155

def b2500 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 148 268 84 96 66 161 289), lower := (rows 11 35 148 268 84 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 70 75 112 112 64 130 258), good := (rows 397 445 180 268 124 124 508 128 256) }] }

theorem u2500 : Upper (D 6) (R 6) [10,33,144,260,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2501 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 268 84 96 96 131 259), lower := (rows 11 35 148 268 84 96 96 128 256), losses := [] }

theorem u2501 : Upper (D 6) (R 6) [10,33,144,260,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2502 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 148 328 81 36 66 164 292), lower := (rows 11 35 148 328 81 36 66 128 256), losses := [] }

theorem u2502 : Upper (D 6) (R 6) [10,33,144,320,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2503 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 11 35 148 328 81 36 68 162 290), lower := (rows 11 35 148 328 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 100 100 130 258), good := (rows 394 490 244 360 112 100 100 128 256) }] }

theorem u2503 : Upper (D 6) (R 6) [10,33,144,320,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2504 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 1, region := 80, targets := 2 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 35 148 328 81 36 96 134 262), lower := (rows 11 35 148 328 81 36 96 128 256), losses := [] }

theorem u2504 : Upper (D 6) (R 6) [10,33,144,320,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2505 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 148 328 82 36 65 164 292), lower := (rows 11 35 148 328 82 36 65 128 256), losses := [] }

theorem u2505 : Upper (D 6) (R 6) [10,33,144,320,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2506 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(3,1),(4,0)], upper := (rows 11 35 148 328 82 36 68 161 289), lower := (rows 11 35 148 328 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 100 100 128 256), good := (rows 26 114 244 360 114 100 100 128 256) },{ target := 1, region := (rows 1 0 20 26 16 116 116 130 258), good := (rows 393 489 252 360 508 100 100 128 256) }] }

theorem u2506 : Upper (D 6) (R 6) [10,33,144,320,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2507 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 148 328 82 36 96 133 261), lower := (rows 11 35 148 328 82 36 96 128 256), losses := [] }

theorem u2507 : Upper (D 6) (R 6) [10,33,144,320,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2508 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 80, targets := 2 },{ cop := 1, region := 80, targets := 4 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 11 35 148 328 112 36 65 134 262), lower := (rows 11 35 148 328 112 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 72 88 127 64 131 259), good := (rows 446 422 180 380 124 36 508 128 256) }] }

theorem u2508 : Upper (D 6) (R 6) [10,33,144,320,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2509 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 11 35 148 328 112 36 66 133 261), lower := (rows 11 35 148 328 112 36 66 128 256), losses := [{ target := 1, region := (rows 1 0 69 72 88 127 64 131 259), good := (rows 445 421 180 380 124 36 508 128 256) }] }

theorem u2509 : Upper (D 6) (R 6) [10,33,144,320,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2510 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 148 328 112 36 68 131 259), lower := (rows 11 35 148 328 112 36 68 128 256), losses := [] }

theorem u2510 : Upper (D 6) (R 6) [10,33,144,320,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2511 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 164 25 276 96 66 196 324), lower := (rows 11 35 164 25 276 96 66 128 256), losses := [] }

theorem u2511 : Upper (D 6) (R 6) [10,33,160,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2512 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 164 25 276 96 68 194 322), lower := (rows 11 35 164 25 276 96 68 128 256), losses := [] }

theorem u2512 : Upper (D 6) (R 6) [10,33,160,17,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2513 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 5, region := 132, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 164 28 273 96 66 196 324), lower := (rows 11 35 164 28 273 96 66 128 256), losses := [] }

theorem u2513 : Upper (D 6) (R 6) [10,33,160,20,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2514 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 28 273 96 68 194 322), lower := (rows 11 35 164 28 273 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 151 24 16 255 223 131 259), good := (rows 494 486 228 124 508 96 100 228 256) }] }

theorem u2514 : Upper (D 6) (R 6) [10,33,160,20,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2515 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 5, region := 132, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 164 28 274 96 65 196 324), lower := (rows 11 35 164 28 274 96 65 128 256), losses := [] }

theorem u2515 : Upper (D 6) (R 6) [10,33,160,20,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2516 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 35 164 28 274 96 68 193 321), lower := (rows 11 35 164 28 274 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 151 24 16 255 223 131 259), good := (rows 493 485 228 124 508 96 100 228 256) }] }

theorem u2516 : Upper (D 6) (R 6) [10,33,160,20,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2517 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 11 35 164 76 21 288 66 208 336), lower := (rows 11 35 164 76 21 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 304 67 144 272), good := (rows 74 98 164 76 508 288 66 128 288) }] }

theorem u2517 : Upper (D 6) (R 6) [10,33,160,68,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2517 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2518 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 11 35 164 76 21 288 80 194 322), lower := (rows 11 35 164 76 21 288 80 128 256), losses := [] }

theorem u2518 : Upper (D 6) (R 6) [10,33,160,68,5,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2518 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2519 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 164 76 82 288 65 148 276), lower := (rows 11 35 164 76 82 288 65 128 256), losses := [] }

theorem u2519 : Upper (D 6) (R 6) [10,33,160,68,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2519 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P06
