import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0004
import IrregularNine14P08C0005

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2460 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 56 208 33 224 224 480), lower := (rows 35 262 13 56 208 33 64 128 256), losses := [] }

theorem u2460 : Upper (D 8) (R 8) [34,260,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2461 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 56 208 96 225 161 417), lower := (rows 35 262 13 56 208 96 64 128 256), losses := [] }

theorem u2461 : Upper (D 8) (R 8) [34,260,9,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2462 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 88 176 33 224 224 480), lower := (rows 35 262 13 88 176 33 64 128 256), losses := [] }

theorem u2462 : Upper (D 8) (R 8) [34,260,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2463 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 13 88 176 96 225 161 417), lower := (rows 35 262 13 88 176 96 64 128 256), losses := [] }

theorem u2463 : Upper (D 8) (R 8) [34,260,9,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2464 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 13 88 176 160 97 225 353), lower := (rows 35 262 13 88 176 160 64 128 256), losses := [] }

theorem u2464 : Upper (D 8) (R 8) [34,260,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2465 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 104 176 33 208 208 464), lower := (rows 35 262 13 104 176 33 64 128 256), losses := [] }

theorem u2465 : Upper (D 8) (R 8) [34,260,9,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2466 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 262 13 104 176 48 193 193 449), lower := (rows 35 262 13 104 176 48 64 128 256), losses := [] }

theorem u2466 : Upper (D 8) (R 8) [34,260,9,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2466 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2467 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 104 176 96 209 145 401), lower := (rows 35 262 13 104 176 96 64 128 256), losses := [] }

theorem u2467 : Upper (D 8) (R 8) [34,260,9,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2468 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 13 104 176 160 81 209 337), lower := (rows 35 262 13 104 176 160 64 128 256), losses := [] }

theorem u2468 : Upper (D 8) (R 8) [34,260,9,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2469 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 104 208 33 240 176 432), lower := (rows 35 262 13 104 208 33 64 128 256), losses := [] }

theorem u2469 : Upper (D 8) (R 8) [34,260,9,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2470 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 13 104 208 48 225 161 417), lower := (rows 35 262 13 104 208 48 64 128 256), losses := [] }

theorem u2470 : Upper (D 8) (R 8) [34,260,9,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2470 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2471 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 104 208 160 113 177 305), lower := (rows 35 262 13 104 208 160 64 128 256), losses := [] }

theorem u2471 : Upper (D 8) (R 8) [34,260,9,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2472 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 200 112 33 240 176 432), lower := (rows 35 262 13 200 112 33 64 128 256), losses := [] }

theorem u2472 : Upper (D 8) (R 8) [34,260,9,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2473 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 13 200 112 48 225 161 417), lower := (rows 35 262 13 200 112 48 64 128 256), losses := [] }

theorem u2473 : Upper (D 8) (R 8) [34,260,9,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2473 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2474 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 262 13 200 112 160 113 177 305), lower := (rows 35 262 13 200 112 160 64 128 256), losses := [] }

theorem u2474 : Upper (D 8) (R 8) [34,260,9,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2475 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 73 176 33 224 224 480), lower := (rows 35 262 28 73 176 33 64 128 256), losses := [] }

theorem u2475 : Upper (D 8) (R 8) [34,260,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 28 73 176 96 225 161 417), lower := (rows 35 262 28 73 176 96 64 128 256), losses := [] }

theorem u2476 : Upper (D 8) (R 8) [34,260,24,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2477 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 28 73 176 160 97 225 353), lower := (rows 35 262 28 73 176 160 64 128 256), losses := [] }

theorem u2477 : Upper (D 8) (R 8) [34,260,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2478 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 104 176 33 193 193 449), lower := (rows 35 262 28 104 176 33 64 128 256), losses := [] }

theorem u2478 : Upper (D 8) (R 8) [34,260,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2479 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 104 176 96 193 129 385), lower := (rows 35 262 28 104 176 96 64 128 256), losses := [] }

theorem u2479 : Upper (D 8) (R 8) [34,260,24,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2480 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 25 208 33 224 224 480), lower := (rows 35 262 44 25 208 33 64 128 256), losses := [] }

theorem u2480 : Upper (D 8) (R 8) [34,260,40,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2481 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 25 208 96 225 161 417), lower := (rows 35 262 44 25 208 96 64 128 256), losses := [] }

theorem u2481 : Upper (D 8) (R 8) [34,260,40,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2482 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 73 112 33 208 144 400), lower := (rows 35 262 44 73 112 33 64 128 256), losses := [] }

theorem u2482 : Upper (D 8) (R 8) [34,260,40,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2483 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 44 73 112 48 193 129 385), lower := (rows 35 262 44 73 112 48 64 128 256), losses := [] }

theorem u2483 : Upper (D 8) (R 8) [34,260,40,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2483 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2484 : Route 9 := (fun mask => (mask,id))

def c2484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2484 : Upper (D 8) (R 8) [34,260,40,65,96,128] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,96,128] 13 (by decide) (choices 1) [1,16,128] r2484 c2484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u298
  · exact u299
  · exact u300

def b2485 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 262 44 73 145 48 224 224 480), lower := (rows 35 262 44 73 145 48 64 128 256), losses := [] }

theorem u2485 : Upper (D 8) (R 8) [34,260,40,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2485 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2486 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 73 145 96 240 176 432), lower := (rows 35 262 44 73 145 96 64 128 256), losses := [] }

theorem u2486 : Upper (D 8) (R 8) [34,260,40,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2487 : Route 9 := (fun mask => (mask,id))

def c2487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2487 : Upper (D 8) (R 8) [34,260,40,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,129,128] 13 (by decide) (choices 1) [16,32] r2487 c2487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u301
  · exact u302

def b2488 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 73 176 33 208 208 464), lower := (rows 35 262 44 73 176 33 64 128 256), losses := [] }

theorem u2488 : Upper (D 8) (R 8) [34,260,40,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2489 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 262 44 73 176 48 193 193 449), lower := (rows 35 262 44 73 176 48 64 128 256), losses := [] }

theorem u2489 : Upper (D 8) (R 8) [34,260,40,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2489 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2490 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 73 176 96 209 145 401), lower := (rows 35 262 44 73 176 96 64 128 256), losses := [] }

theorem u2490 : Upper (D 8) (R 8) [34,260,40,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2491 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 44 73 176 160 81 209 337), lower := (rows 35 262 44 73 176 160 64 128 256), losses := [] }

theorem u2491 : Upper (D 8) (R 8) [34,260,40,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2492 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 73 208 33 240 176 432), lower := (rows 35 262 44 73 208 33 64 128 256), losses := [] }

theorem u2492 : Upper (D 8) (R 8) [34,260,40,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2493 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 44 73 208 48 225 161 417), lower := (rows 35 262 44 73 208 48 64 128 256), losses := [] }

theorem u2493 : Upper (D 8) (R 8) [34,260,40,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2493 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2494 : Route 9 := (fun mask => (mask,id))

def c2494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2494 : Upper (D 8) (R 8) [34,260,40,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,192,128] 13 (by decide) (choices 1) [1,16,32] r2494 c2494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u303
  · exact u304
  · exact u305

def b2495 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 88 145 33 224 224 480), lower := (rows 35 262 44 88 145 33 64 128 256), losses := [] }

theorem u2495 : Upper (D 8) (R 8) [34,260,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2496 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 88 145 96 225 161 417), lower := (rows 35 262 44 88 145 96 64 128 256), losses := [] }

theorem u2496 : Upper (D 8) (R 8) [34,260,40,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2497 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 44 88 145 160 97 225 353), lower := (rows 35 262 44 88 145 160 64 128 256), losses := [] }

theorem u2497 : Upper (D 8) (R 8) [34,260,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2498 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 88 176 33 193 193 449), lower := (rows 35 262 44 88 176 33 64 128 256), losses := [] }

theorem u2498 : Upper (D 8) (R 8) [34,260,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2499 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 88 176 96 193 129 385), lower := (rows 35 262 44 88 176 96 64 128 256), losses := [] }

theorem u2499 : Upper (D 8) (R 8) [34,260,40,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2500 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 44 88 176 160 65 193 321), lower := (rows 35 262 44 88 176 160 64 128 256), losses := [] }

theorem u2500 : Upper (D 8) (R 8) [34,260,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2501 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 200 81 33 240 176 432), lower := (rows 35 262 44 200 81 33 64 128 256), losses := [] }

theorem u2501 : Upper (D 8) (R 8) [34,260,40,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2502 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 44 200 81 48 225 161 417), lower := (rows 35 262 44 200 81 48 64 128 256), losses := [] }

theorem u2502 : Upper (D 8) (R 8) [34,260,40,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2502 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2503 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 44 200 81 160 113 177 305), lower := (rows 35 262 44 200 81 160 64 128 256), losses := [] }

theorem u2503 : Upper (D 8) (R 8) [34,260,40,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2504 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 200 112 33 209 145 401), lower := (rows 35 262 44 200 112 33 64 128 256), losses := [] }

theorem u2504 : Upper (D 8) (R 8) [34,260,40,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2505 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 44 200 112 48 193 129 385), lower := (rows 35 262 44 200 112 48 64 128 256), losses := [] }

theorem u2505 : Upper (D 8) (R 8) [34,260,40,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2505 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2506 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 44 200 112 160 81 145 273), lower := (rows 35 262 44 200 112 160 64 128 256), losses := [] }

theorem u2506 : Upper (D 8) (R 8) [34,260,40,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2507 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 56 152 33 224 224 480), lower := (rows 35 262 69 56 152 33 64 128 256), losses := [] }

theorem u2507 : Upper (D 8) (R 8) [34,260,65,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2508 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 56 152 96 225 161 417), lower := (rows 35 262 69 56 152 96 64 128 256), losses := [] }

theorem u2508 : Upper (D 8) (R 8) [34,260,65,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2509 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 56 152 160 97 225 353), lower := (rows 35 262 69 56 152 160 64 128 256), losses := [] }

theorem u2509 : Upper (D 8) (R 8) [34,260,65,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2510 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 56 208 33 232 168 424), lower := (rows 35 262 69 56 208 33 64 128 256), losses := [] }

theorem u2510 : Upper (D 8) (R 8) [34,260,65,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2511 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 69 56 208 40 225 161 417), lower := (rows 35 262 69 56 208 40 64 128 256), losses := [] }

theorem u2511 : Upper (D 8) (R 8) [34,260,65,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2511 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2512 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 56 208 160 105 169 297), lower := (rows 35 262 69 56 208 160 64 128 256), losses := [] }

theorem u2512 : Upper (D 8) (R 8) [34,260,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2513 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 88 176 33 232 168 424), lower := (rows 35 262 69 88 176 33 64 128 256), losses := [] }

theorem u2513 : Upper (D 8) (R 8) [34,260,65,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2514 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 69 88 176 40 225 161 417), lower := (rows 35 262 69 88 176 40 64 128 256), losses := [] }

theorem u2514 : Upper (D 8) (R 8) [34,260,65,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2514 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2515 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 88 176 160 105 169 297), lower := (rows 35 262 69 88 176 160 64 128 256), losses := [] }

theorem u2515 : Upper (D 8) (R 8) [34,260,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2516 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 104 152 33 240 176 432), lower := (rows 35 262 69 104 152 33 64 128 256), losses := [] }

theorem u2516 : Upper (D 8) (R 8) [34,260,65,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2517 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 69 104 152 48 225 161 417), lower := (rows 35 262 69 104 152 48 64 128 256), losses := [] }

theorem u2517 : Upper (D 8) (R 8) [34,260,65,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2517 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2518 : Route 9 := (fun mask => (mask,id))

def c2518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2518 : Upper (D 8) (R 8) [34,260,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,136,128] 13 (by decide) (choices 1) [1,16,32] r2518 c2518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u306
  · exact u307
  · exact u308

def b2519 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 104 176 33 216 152 408), lower := (rows 35 262 69 104 176 33 64 128 256), losses := [] }

theorem u2519 : Upper (D 8) (R 8) [34,260,65,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P08
