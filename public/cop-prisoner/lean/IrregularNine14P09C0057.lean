import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0009
import IrregularNine14P09C0010

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3420 : Route 9 := (fun mask => (mask,id))

def c3420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3420 : Upper (D 9) (R 9) [6,40,192,257,65,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,65,128] 13 (by decide) (choices 1) [16,32,256] r3420 c3420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u541
  · exact u542
  · exact u543

def b3421 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 196 265 81 288 240 176 432), lower := (rows 7 42 196 265 81 288 64 128 256), losses := [] }

theorem u3421 : Upper (D 9) (R 9) [6,40,192,257,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3421 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3422 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0),(4,0)], upper := (rows 7 42 196 265 112 33 464 400 400), lower := (rows 7 42 196 265 112 33 64 128 256), losses := [] }

theorem u3422 : Upper (D 9) (R 9) [6,40,192,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3422 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3423 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 196 265 112 48 449 385 385), lower := (rows 7 42 196 265 112 48 64 128 256), losses := [] }

theorem u3423 : Upper (D 9) (R 9) [6,40,192,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3423 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3424 : Route 9 := (fun mask => (mask,id))

def c3424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3424 : Upper (D 9) (R 9) [6,40,192,257,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96,128] 13 (by decide) (choices 1) [1,16,256] r3424 c3424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u544
  · exact u545
  · exact u546

def b3425 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 196 265 112 288 209 145 401), lower := (rows 7 42 196 265 112 288 64 128 256), losses := [] }

theorem u3425 : Upper (D 9) (R 9) [6,40,192,257,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3425 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3426 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 50, targets := 192 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,6),(4,7)], upper := (rows 7 42 196 265 304 33 208 208 464), lower := (rows 7 42 196 265 304 33 64 128 256), losses := [] }

theorem u3426 : Upper (D 9) (R 9) [6,40,192,257,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3426 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3427 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 50, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 196 265 304 48 193 193 449), lower := (rows 7 42 196 265 304 48 64 128 256), losses := [] }

theorem u3427 : Upper (D 9) (R 9) [6,40,192,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3427 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3428 : Route 9 := (fun mask => (mask,id))

def c3428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3428 : Upper (D 9) (R 9) [6,40,192,257,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,288,64] 13 (by decide) (choices 1) [1,16,128] r3428 c3428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u547
  · exact u548
  · exact u549

def b3429 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0),(4,0)], upper := (rows 7 42 196 265 336 33 240 176 432), lower := (rows 7 42 196 265 336 33 64 128 256), losses := [] }

theorem u3429 : Upper (D 9) (R 9) [6,40,192,257,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3429 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3430 : Route 9 := (fun mask => (mask,id))

def c3430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3430 : Upper (D 9) (R 9) [6,40,192,257,320,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,320,16] 13 (by decide) (choices 1) [1,32,128] r3430 c3430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u550
  · exact u551
  · exact u552

def r3431 : Route 9 := (fun mask => (mask,id))

def c3431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3431 : Upper (D 9) (R 9) [6,40,192,257,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,320,128] 13 (by decide) (choices 1) [1,16,32] r3431 c3431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u553
  · exact u554
  · exact u555

def b3432 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 48, targets := 448 },{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(4,6),(4,7),(4,8)], upper := (rows 7 42 196 280 49 33 448 448 448), lower := (rows 7 42 196 280 49 33 64 128 256), losses := [] }

theorem u3432 : Upper (D 9) (R 9) [6,40,192,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3432 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3433 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 4, region := 394, targets := 64 },{ cop := 4, region := 392, targets := 32 }], pairs := [(0,5),(1,6),(2,5),(3,5),(3,6)], upper := (rows 7 42 196 280 49 96 449 385 385), lower := (rows 7 42 196 280 49 96 64 128 256), losses := [] }

theorem u3433 : Upper (D 9) (R 9) [6,40,192,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3433 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3434 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 196 280 49 288 193 193 449), lower := (rows 7 42 196 280 49 288 64 128 256), losses := [] }

theorem u3434 : Upper (D 9) (R 9) [6,40,192,272,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3434 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3435 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0),(3,6)], upper := (rows 7 42 196 280 81 33 480 416 416), lower := (rows 7 42 196 280 81 33 64 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 16 49 64 0 256), good := (rows 39 42 68 314 113 33 64 0 256) },{ target := 8, region := (rows 1 10 4 8 16 49 64 128 0), good := (rows 39 42 196 58 113 33 64 128 0) }] }

theorem u3435 : Upper (D 9) (R 9) [6,40,192,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3435 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3436 : Route 9 := (fun mask => (mask,id))

def c3436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3436 : Upper (D 9) (R 9) [6,40,192,272,65,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,65,128] 13 (by decide) (choices 1) [1,32,256] r3436 c3436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u556
  · exact u557
  · exact u558

def b3437 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 196 280 81 288 225 161 417), lower := (rows 7 42 196 280 81 288 64 128 256), losses := [] }

theorem u3437 : Upper (D 9) (R 9) [6,40,192,272,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3437 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3438 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(1,6),(2,5),(3,5),(3,6)], upper := (rows 7 42 196 280 112 33 449 385 385), lower := (rows 7 42 196 280 112 33 64 128 256), losses := [{ target := 5, region := (rows 3 2 55 24 16 0 99 163 291), good := (rows 455 463 196 284 476 453 64 128 256) },{ target := 6, region := (rows 1 18 4 24 16 33 0 161 289), good := (rows 423 426 132 282 442 417 0 128 256) }] }

theorem u3438 : Upper (D 9) (R 9) [6,40,192,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3438 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3439 : Route 9 := (fun mask => (mask,id))

def c3439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3439 : Upper (D 9) (R 9) [6,40,192,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96,128] 13 (by decide) (choices 1) [1,256] r3439 c3439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u559
  · exact u560

def b3440 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 196 280 112 288 193 129 385), lower := (rows 7 42 196 280 112 288 64 128 256), losses := [] }

theorem u3440 : Upper (D 9) (R 9) [6,40,192,272,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3440 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3441 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 48, targets := 384 }], pairs := [(1,0),(2,0),(3,0),(4,7),(4,8)], upper := (rows 7 42 196 328 49 33 464 400 400), lower := (rows 7 42 196 328 49 33 64 128 256), losses := [] }

theorem u3441 : Upper (D 9) (R 9) [6,40,192,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3441 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3442 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 48, targets := 128 }], pairs := [(0,5),(2,5),(3,5),(4,7)], upper := (rows 7 42 196 328 49 48 449 385 385), lower := (rows 7 42 196 328 49 48 64 128 256), losses := [] }

theorem u3442 : Upper (D 9) (R 9) [6,40,192,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3442 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3443 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 330, targets := 128 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,7),(2,5),(3,5),(3,7),(4,6)], upper := (rows 7 42 196 328 49 160 337 401 273), lower := (rows 7 42 196 328 49 160 64 128 256), losses := [] }

theorem u3443 : Upper (D 9) (R 9) [6,40,192,320,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3443 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3444 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 196 328 49 288 209 145 401), lower := (rows 7 42 196 328 49 288 64 128 256), losses := [] }

theorem u3444 : Upper (D 9) (R 9) [6,40,192,320,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3444 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3445 : Route 9 := (fun mask => (mask,id))

def c3445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3445 : Upper (D 9) (R 9) [6,40,192,320,129,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,129,1] 13 (by decide) (choices 1) [16,32,256] r3445 c3445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u561
  · exact u562
  · exact u563

def r3446 : Route 9 := (fun mask => (mask,id))

def c3446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3446 : Upper (D 9) (R 9) [6,40,192,320,129,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,129,16] 13 (by decide) (choices 1) [1,32,256] r3446 c3446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u564
  · exact u565
  · exact u566

def b3447 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 196 328 145 288 113 177 305), lower := (rows 7 42 196 328 145 288 64 128 256), losses := [] }

theorem u3447 : Upper (D 9) (R 9) [6,40,192,320,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3447 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3448 : Route 9 := (fun mask => (mask,id))

def c3448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3448 : Upper (D 9) (R 9) [6,40,192,320,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,160,1] 13 (by decide) (choices 1) [1,16,256] r3448 c3448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u567
  · exact u568
  · exact u569

def b3449 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 196 328 176 48 321 385 257), lower := (rows 7 42 196 328 176 48 64 128 256), losses := [] }

theorem u3449 : Upper (D 9) (R 9) [6,40,192,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3449 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3450 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 196 328 176 288 81 145 273), lower := (rows 7 42 196 328 176 288 64 128 256), losses := [] }

theorem u3450 : Upper (D 9) (R 9) [6,40,192,320,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3450 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3451 : Route 9 := (fun mask => (mask,id))

def c3451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3451 : Upper (D 9) (R 9) [6,40,192,320,257,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,257,1] 13 (by decide) (choices 1) [16,32,128] r3451 c3451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u570
  · exact u571
  · exact u572

def r3452 : Route 9 := (fun mask => (mask,id))

def c3452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3452 : Upper (D 9) (R 9) [6,40,192,320,257,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,257,16] 13 (by decide) (choices 1) [1,32,128] r3452 c3452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u573
  · exact u574
  · exact u575

def r3453 : Route 9 := (fun mask => (mask,id))

def c3453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3453 : Upper (D 9) (R 9) [6,40,192,320,257,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,257,128] 13 (by decide) (choices 1) [1,16,32] r3453 c3453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u576
  · exact u577
  · exact u578

def r3454 : Route 9 := (fun mask => (mask,id))

def c3454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3454 : Upper (D 9) (R 9) [6,40,192,320,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,288,1] 13 (by decide) (choices 1) [1,16,128] r3454 c3454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u579
  · exact u580
  · exact u581

def b3455 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 50, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 196 328 304 48 193 129 385), lower := (rows 7 42 196 328 304 48 64 128 256), losses := [] }

theorem u3455 : Upper (D 9) (R 9) [6,40,192,320,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3455 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3456 : Route 9 := (fun mask => (mask,id))

def c3456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3456 : Upper (D 9) (R 9) [6,40,192,320,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,288,128] 13 (by decide) (choices 1) [1,16] r3456 c3456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u582
  · exact u583

def r3457 : Route 9 := (fun mask => (mask,id))

def c3457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3457 : Upper (D 9) (R 9) [6,40,192,320,384,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,384,1] 13 (by decide) (choices 1) [1,16,32] r3457 c3457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u584
  · exact u585
  · exact u586

def r3458 : Route 9 := (fun mask => (mask,id))

def c3458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3458 : Upper (D 9) (R 9) [6,40,192,320,384,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,384,16] 13 (by decide) (choices 1) [1,32] r3458 c3458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u587
  · exact u588

def b3459 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 389, targets := 64 },{ cop := 5, region := 450, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 25 88 33 448 384 384), lower := (rows 7 98 164 25 88 33 64 128 256), losses := [] }

theorem u3459 : Upper (D 9) (R 9) [6,96,160,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3459 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3460 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 98 164 25 88 160 321 385 257), lower := (rows 7 98 164 25 88 160 64 128 256), losses := [] }

theorem u3460 : Upper (D 9) (R 9) [6,96,160,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3461 : Route 9 := (fun mask => (mask,id))

def c3461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3461 : Upper (D 9) (R 9) [6,96,160,17,72,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,72,256] 13 (by decide) (choices 1) [1,128,256] r3461 c3461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u589
  · exact u590
  · exact u591

def b3462 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(3,8)], upper := (rows 7 98 164 25 208 33 328 392 264), lower := (rows 7 98 164 25 208 33 64 128 256), losses := [] }

theorem u3462 : Upper (D 9) (R 9) [6,96,160,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3462 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3463 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 98 164 25 208 40 321 385 257), lower := (rows 7 98 164 25 208 40 64 128 256), losses := [] }

theorem u3463 : Upper (D 9) (R 9) [6,96,160,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3463 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3464 : Route 9 := (fun mask => (mask,id))

def c3464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3464 : Upper (D 9) (R 9) [6,96,160,17,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,192,256] 13 (by decide) (choices 1) [1,8,256] r3464 c3464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u592
  · exact u593
  · exact u594

def b3465 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 5, region := 454, targets := 1 },{ cop := 3, region := 464, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 98 164 25 280 33 448 448 448), lower := (rows 7 98 164 25 280 33 64 128 256), losses := [] }

theorem u3465 : Upper (D 9) (R 9) [6,96,160,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3465 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3466 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 },{ cop := 5, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 25 280 96 449 385 385), lower := (rows 7 98 164 25 280 96 64 128 256), losses := [] }

theorem u3466 : Upper (D 9) (R 9) [6,96,160,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3466 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3467 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 7 98 164 25 280 288 193 193 449), lower := (rows 7 98 164 25 280 288 64 128 256), losses := [] }

theorem u3467 : Upper (D 9) (R 9) [6,96,160,17,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3467 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3468 : Route 9 := (fun mask => (mask,id))

def c3468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3468 : Upper (D 9) (R 9) [6,96,160,17,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,320,1] 13 (by decide) (choices 1) [8,128,256] r3468 c3468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u595
  · exact u596
  · exact u597

def b3469 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 25 336 40 449 385 385), lower := (rows 7 98 164 25 336 40 64 128 256), losses := [] }

theorem u3469 : Upper (D 9) (R 9) [6,96,160,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3469 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3470 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 98 164 25 336 160 329 393 265), lower := (rows 7 98 164 25 336 160 64 128 256), losses := [] }

theorem u3470 : Upper (D 9) (R 9) [6,96,160,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3470 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3471 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 34, targets := 129 },{ cop := 3, region := 420, targets := 64 }], pairs := [(1,0),(1,7),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 25 336 288 201 137 393), lower := (rows 7 98 164 25 336 288 64 128 256), losses := [] }

theorem u3471 : Upper (D 9) (R 9) [6,96,160,17,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3471 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3472 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(2,6),(3,5),(4,5),(4,6)], upper := (rows 7 98 164 73 152 33 336 400 272), lower := (rows 7 98 164 73 152 33 64 128 256), losses := [] }

theorem u3472 : Upper (D 9) (R 9) [6,96,160,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3472 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3473 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 98 164 73 152 48 321 385 257), lower := (rows 7 98 164 73 152 48 64 128 256), losses := [] }

theorem u3473 : Upper (D 9) (R 9) [6,96,160,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3473 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3474 : Route 9 := (fun mask => (mask,id))

def c3474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3474 : Upper (D 9) (R 9) [6,96,160,65,136,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,136,256] 13 (by decide) (choices 1) [1,16,256] r3474 c3474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u598
  · exact u599
  · exact u600

def b3475 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 98 164 73 273 40 464 400 400), lower := (rows 7 98 164 73 273 40 64 128 256), losses := [] }

theorem u3475 : Upper (D 9) (R 9) [6,96,160,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3475 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3476 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 7 98 164 73 273 48 456 392 392), lower := (rows 7 98 164 73 273 48 64 128 256), losses := [] }

theorem u3476 : Upper (D 9) (R 9) [6,96,160,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3476 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3477 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 98 164 73 273 160 344 408 280), lower := (rows 7 98 164 73 273 160 64 128 256), losses := [] }

theorem u3477 : Upper (D 9) (R 9) [6,96,160,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3477 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3478 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 200, targets := 256 }], pairs := [(2,6),(3,5),(3,8),(4,5),(4,6)], upper := (rows 7 98 164 73 273 288 216 152 408), lower := (rows 7 98 164 73 273 288 64 128 256), losses := [] }

theorem u3478 : Upper (D 9) (R 9) [6,96,160,65,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3478 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3479 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(2,6),(3,5),(4,5),(4,6)], upper := (rows 7 98 164 73 280 33 464 400 400), lower := (rows 7 98 164 73 280 33 64 128 256), losses := [] }

theorem u3479 : Upper (D 9) (R 9) [6,96,160,65,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3479 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3479
end Delivery.IrregularNine14.P09
