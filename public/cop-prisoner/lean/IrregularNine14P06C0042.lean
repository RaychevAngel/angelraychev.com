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

def b2520 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 164 76 82 288 68 145 273), lower := (rows 11 35 164 76 82 288 68 128 256), losses := [] }

theorem u2520 : Upper (D 6) (R 6) [10,33,160,68,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2520 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2521 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 11 35 164 76 82 288 80 133 261), lower := (rows 11 35 164 76 82 288 80 128 256), losses := [] }

theorem u2521 : Upper (D 6) (R 6) [10,33,160,68,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2521 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2522 : Route 9 := (fun mask => (mask,id))

def c2522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2522 : Upper (D 6) (R 6) [10,33,160,68,260,16,1] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,260,16,1] 13 (by decide) (choices 1) [2,64] r2522 c2522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u156
  · exact u157

def r2523 : Route 9 := (fun mask => (mask,id))

def c2523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2523 : Upper (D 6) (R 6) [10,33,160,68,260,16,2] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,260,16,2] 13 (by decide) (choices 1) [1,64] r2523 c2523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u158
  · exact u159

def b2524 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 11 35 164 76 336 48 65 134 262), lower := (rows 11 35 164 76 336 48 65 128 256), losses := [] }

theorem u2524 : Upper (D 6) (R 6) [10,33,160,68,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2524 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2525 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 132, targets := 2 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,1),(2,6)], upper := (rows 11 35 164 76 336 48 66 133 261), lower := (rows 11 35 164 76 336 48 66 128 256), losses := [] }

theorem u2525 : Upper (D 6) (R 6) [10,33,160,68,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2525 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2526 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 164 76 336 48 68 131 259), lower := (rows 11 35 164 76 336 48 68 128 256), losses := [] }

theorem u2526 : Upper (D 6) (R 6) [10,33,160,68,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2526 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2527 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 164 265 84 96 66 148 276), lower := (rows 11 35 164 265 84 96 66 128 256), losses := [] }

theorem u2527 : Upper (D 6) (R 6) [10,33,160,257,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2528 : PairBound 9 := { available := 18, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 164 265 84 96 68 146 274), lower := (rows 11 35 164 265 84 96 68 128 256), losses := [] }

theorem u2528 : Upper (D 6) (R 6) [10,33,160,257,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2529 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 265 84 96 80 134 262), lower := (rows 11 35 164 265 84 96 80 128 256), losses := [] }

theorem u2529 : Upper (D 6) (R 6) [10,33,160,257,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2529 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2530 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 164 268 21 96 66 208 336), lower := (rows 11 35 164 268 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 115 67 144 272), good := (rows 106 98 164 268 508 96 98 128 256) }] }

theorem u2530 : Upper (D 6) (R 6) [10,33,160,260,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2531 : Route 9 := (fun mask => (mask,id))

def c2531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2531 : Upper (D 6) (R 6) [10,33,160,260,5,64,16] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,5,64,16] 13 (by decide) (choices 1) [2,64] r2531 c2531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u160
  · exact u161

def b2532 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 35 164 268 22 96 65 208 336), lower := (rows 11 35 164 268 22 96 65 128 256), losses := [] }

theorem u2532 : Upper (D 6) (R 6) [10,33,160,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2533 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 164 268 22 96 80 193 321), lower := (rows 11 35 164 268 22 96 80 128 256), losses := [] }

theorem u2533 : Upper (D 6) (R 6) [10,33,160,260,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2533 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2534 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 268 81 96 66 148 276), lower := (rows 11 35 164 268 81 96 66 128 256), losses := [] }

theorem u2534 : Upper (D 6) (R 6) [10,33,160,260,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2535 : PairBound 9 := { available := 18, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 11 35 164 268 81 96 68 146 274), lower := (rows 11 35 164 268 81 96 68 128 256), losses := [] }

theorem u2535 : Upper (D 6) (R 6) [10,33,160,260,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2536 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 268 81 96 80 134 262), lower := (rows 11 35 164 268 81 96 80 128 256), losses := [] }

theorem u2536 : Upper (D 6) (R 6) [10,33,160,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2536 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2537 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 268 82 96 65 148 276), lower := (rows 11 35 164 268 82 96 65 128 256), losses := [] }

theorem u2537 : Upper (D 6) (R 6) [10,33,160,260,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 164 268 82 96 68 145 273), lower := (rows 11 35 164 268 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 132 8 17 253 204 128 256), good := (rows 122 50 228 364 114 96 100 228 256) }] }

theorem u2538 : Upper (D 6) (R 6) [10,33,160,260,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2539 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 268 82 96 80 133 261), lower := (rows 11 35 164 268 82 96 80 128 256), losses := [] }

theorem u2539 : Upper (D 6) (R 6) [10,33,160,260,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2539 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2540 : Route 9 := (fun mask => (mask,id))

def c2540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2540 : Upper (D 6) (R 6) [10,33,160,260,68,16,1] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,68,16,1] 13 (by decide) (choices 1) [2,64] r2540 c2540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u162
  · exact u163

def r2541 : Route 9 := (fun mask => (mask,id))

def c2541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2541 : Upper (D 6) (R 6) [10,33,160,260,68,16,2] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,68,16,2] 13 (by decide) (choices 1) [1,64] r2541 c2541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u164
  · exact u165

def r2542 : Route 9 := (fun mask => (mask,id))

def c2542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2542 : Upper (D 6) (R 6) [10,33,160,260,68,64,1] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,68,64,1] 13 (by decide) (choices 1) [2,16] r2542 c2542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u166
  · exact u167

def b2543 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 164 268 84 96 66 145 273), lower := (rows 11 35 164 268 84 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 70 75 112 112 64 130 258), good := (rows 397 445 180 268 124 124 508 128 256) }] }

theorem u2543 : Upper (D 6) (R 6) [10,33,160,260,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2544 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 268 84 96 80 131 259), lower := (rows 11 35 164 268 84 96 80 128 256), losses := [] }

theorem u2544 : Upper (D 6) (R 6) [10,33,160,260,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2544 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2545 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 5, region := 132, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 164 280 21 96 66 196 324), lower := (rows 11 35 164 280 21 96 66 128 256), losses := [] }

theorem u2545 : Upper (D 6) (R 6) [10,33,160,272,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2546 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 280 21 96 68 194 322), lower := (rows 11 35 164 280 21 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 151 24 16 255 223 131 259), good := (rows 494 486 228 380 508 96 100 228 256) }] }

theorem u2546 : Upper (D 6) (R 6) [10,33,160,272,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2547 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 11 35 164 328 84 48 65 134 262), lower := (rows 11 35 164 328 84 48 65 128 256), losses := [] }

theorem u2547 : Upper (D 6) (R 6) [10,33,160,320,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2547 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2548 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 132, targets := 2 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,1),(2,6)], upper := (rows 11 35 164 328 84 48 66 133 261), lower := (rows 11 35 164 328 84 48 66 128 256), losses := [] }

theorem u2548 : Upper (D 6) (R 6) [10,33,160,320,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2548 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2549 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 164 328 84 48 68 131 259), lower := (rows 11 35 164 328 84 48 68 128 256), losses := [] }

theorem u2549 : Upper (D 6) (R 6) [10,33,160,320,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2549 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2550 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 25 336 36 66 164 292), lower := (rows 11 35 196 25 336 36 66 128 256), losses := [] }

theorem u2550 : Upper (D 6) (R 6) [10,33,192,17,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2551 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 25 336 36 68 162 290), lower := (rows 11 35 196 25 336 36 68 128 256), losses := [] }

theorem u2551 : Upper (D 6) (R 6) [10,33,192,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2552 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 196 25 336 36 96 134 262), lower := (rows 11 35 196 25 336 36 96 128 256), losses := [] }

theorem u2552 : Upper (D 6) (R 6) [10,33,192,17,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2553 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 196 73 276 36 66 176 304), lower := (rows 11 35 196 73 276 36 66 128 256), losses := [] }

theorem u2553 : Upper (D 6) (R 6) [10,33,192,65,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2554 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 196 73 276 36 80 162 290), lower := (rows 11 35 196 73 276 36 80 128 256), losses := [] }

theorem u2554 : Upper (D 6) (R 6) [10,33,192,65,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2554 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2555 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 196 73 276 36 96 146 274), lower := (rows 11 35 196 73 276 36 96 128 256), losses := [] }

theorem u2555 : Upper (D 6) (R 6) [10,33,192,65,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2556 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 196 73 304 36 66 148 276), lower := (rows 11 35 196 73 304 36 66 128 256), losses := [] }

theorem u2556 : Upper (D 6) (R 6) [10,33,192,65,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2557 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 1, region := 272, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 11 35 196 73 304 36 68 146 274), lower := (rows 11 35 196 73 304 36 68 128 256), losses := [] }

theorem u2557 : Upper (D 6) (R 6) [10,33,192,65,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2558 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 196 73 304 36 80 134 262), lower := (rows 11 35 196 73 304 36 80 128 256), losses := [] }

theorem u2558 : Upper (D 6) (R 6) [10,33,192,65,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2558 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2559 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 196 88 52 288 65 134 262), lower := (rows 11 35 196 88 52 288 65 128 256), losses := [] }

theorem u2559 : Upper (D 6) (R 6) [10,33,192,80,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2559 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2560 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 196 88 52 288 66 133 261), lower := (rows 11 35 196 88 52 288 66 128 256), losses := [] }

theorem u2560 : Upper (D 6) (R 6) [10,33,192,80,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2560 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2561 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 291, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 35 196 88 52 288 68 131 259), lower := (rows 11 35 196 88 52 288 68 128 256), losses := [] }

theorem u2561 : Upper (D 6) (R 6) [10,33,192,80,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2561 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2562 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 88 273 36 66 164 292), lower := (rows 11 35 196 88 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 95 24 16 127 67 255 383), good := (rows 494 486 484 508 508 420 486 128 256) }] }

theorem u2562 : Upper (D 6) (R 6) [10,33,192,80,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2563 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 7, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 196 88 273 36 68 162 290), lower := (rows 11 35 196 88 273 36 68 128 256), losses := [] }

theorem u2563 : Upper (D 6) (R 6) [10,33,192,80,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2564 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 88 273 36 96 134 262), lower := (rows 11 35 196 88 273 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 151 24 16 191 255 131 259), good := (rows 494 486 228 124 508 100 96 228 256) }] }

theorem u2564 : Upper (D 6) (R 6) [10,33,192,80,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2565 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 196 88 274 36 65 164 292), lower := (rows 11 35 196 88 274 36 65 128 256), losses := [] }

theorem u2565 : Upper (D 6) (R 6) [10,33,192,80,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2566 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 7, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 196 88 274 36 68 161 289), lower := (rows 11 35 196 88 274 36 68 128 256), losses := [] }

theorem u2566 : Upper (D 6) (R 6) [10,33,192,80,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2567 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 88 274 36 96 133 261), lower := (rows 11 35 196 88 274 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 132 24 16 164 230 128 256), good := (rows 74 98 228 88 346 100 96 228 256) }] }

theorem u2567 : Upper (D 6) (R 6) [10,33,192,80,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2568 : PairBound 9 := { available := 34, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 196 88 276 36 65 162 290), lower := (rows 11 35 196 88 276 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 76 80 124 64 131 259), good := (rows 426 418 252 124 316 44 508 128 256) }] }

theorem u2568 : Upper (D 6) (R 6) [10,33,192,80,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2569 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 196 88 276 36 66 161 289), lower := (rows 11 35 196 88 276 36 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 76 80 124 64 131 259), good := (rows 425 417 252 124 316 44 508 128 256) }] }

theorem u2569 : Upper (D 6) (R 6) [10,33,192,80,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2570 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 196 88 276 36 96 131 259), lower := (rows 11 35 196 88 276 36 96 128 256), losses := [] }

theorem u2570 : Upper (D 6) (R 6) [10,33,192,80,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 196 88 304 36 65 134 262), lower := (rows 11 35 196 88 304 36 65 128 256), losses := [] }

theorem u2571 : Upper (D 6) (R 6) [10,33,192,80,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2572 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 196 88 304 36 66 133 261), lower := (rows 11 35 196 88 304 36 66 128 256), losses := [] }

theorem u2572 : Upper (D 6) (R 6) [10,33,192,80,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2573 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 7, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 196 88 304 36 68 131 259), lower := (rows 11 35 196 88 304 36 68 128 256), losses := [] }

theorem u2573 : Upper (D 6) (R 6) [10,33,192,80,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2574 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 196 268 21 96 66 176 304), lower := (rows 11 35 196 268 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 119 67 144 272), good := (rows 106 98 228 300 508 96 98 128 256) }] }

theorem u2574 : Upper (D 6) (R 6) [10,33,192,260,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2575 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 196 268 21 96 80 162 290), lower := (rows 11 35 196 268 21 96 80 128 256), losses := [{ target := 2, region := (rows 9 26 0 8 16 116 80 218 346), good := (rows 395 419 480 427 499 480 498 128 256) }] }

theorem u2575 : Upper (D 6) (R 6) [10,33,192,260,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2575 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2576 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 7, region := 100, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 196 268 21 96 96 146 274), lower := (rows 11 35 196 268 21 96 96 128 256), losses := [] }

theorem u2576 : Upper (D 6) (R 6) [10,33,192,260,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2577 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 35 196 268 22 96 65 176 304), lower := (rows 11 35 196 268 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 144 272), good := (rows 10 34 228 300 446 96 96 128 256) }] }

theorem u2577 : Upper (D 6) (R 6) [10,33,192,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2578 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(3,1)], upper := (rows 11 35 196 268 22 96 80 161 289), lower := (rows 11 35 196 268 22 96 80 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 116 80 130 258), good := (rows 393 417 228 300 508 96 124 128 256) }] }

theorem u2578 : Upper (D 6) (R 6) [10,33,192,260,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2578 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2579 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 196 268 22 96 96 145 273), lower := (rows 11 35 196 268 22 96 96 128 256), losses := [] }

theorem u2579 : Upper (D 6) (R 6) [10,33,192,260,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2579
end Delivery.IrregularNine14.P06
