import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0055

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15540 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(3,0),(3,7),(4,0)], upper := (rows 13 35 21 328 146 160 98 226 354), lower := (rows 13 35 21 328 146 160 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 176 0 128 256), good := (rows 15 35 55 264 178 160 0 160 256) }] }

theorem u15540 : Upper (D 7) (R 7) [12,33,17,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15541 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 328 176 34 194 194 450), lower := (rows 13 35 21 328 176 34 64 128 256), losses := [] }

theorem u15541 : Upper (D 7) (R 7) [12,33,17,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15542 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 148, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 328 176 96 194 130 386), lower := (rows 13 35 21 328 176 96 64 128 256), losses := [] }

theorem u15542 : Upper (D 7) (R 7) [12,33,17,320,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15543 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 21 328 176 160 66 194 322), lower := (rows 13 35 21 328 176 160 64 128 256), losses := [] }

theorem u15543 : Upper (D 7) (R 7) [12,33,17,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15544 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 328 208 34 226 162 418), lower := (rows 13 35 21 328 208 34 64 128 256), losses := [] }

theorem u15544 : Upper (D 7) (R 7) [12,33,17,320,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15545 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(3,0),(3,7),(4,0)], upper := (rows 13 35 21 328 208 160 98 162 290), lower := (rows 13 35 21 328 208 160 64 128 256), losses := [] }

theorem u15545 : Upper (D 7) (R 7) [12,33,17,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15546 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 73 208 34 480 416 416), lower := (rows 13 35 22 73 208 34 64 128 256), losses := [] }

theorem u15546 : Upper (D 7) (R 7) [12,33,18,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15547 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 0, region := 418, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(2,0),(3,7),(4,0)], upper := (rows 13 35 22 73 208 160 354 418 290), lower := (rows 13 35 22 73 208 160 64 128 256), losses := [] }

theorem u15547 : Upper (D 7) (R 7) [12,33,18,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15548 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 13 35 22 73 208 288 226 162 418), lower := (rows 13 35 22 73 208 288 64 128 256), losses := [] }

theorem u15548 : Upper (D 7) (R 7) [12,33,18,65,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15548 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15549 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 73 336 34 224 160 416), lower := (rows 13 35 22 73 336 34 64 128 256), losses := [] }

theorem u15549 : Upper (D 7) (R 7) [12,33,18,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15550 : Route 9 := (fun mask => (mask,id))

def c15550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15550 : Upper (D 7) (R 7) [12,33,18,65,320,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,65,320,128] 13 (by decide) (choices 1) [2,32,128] r15550 c15550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3302
  · exact u3303
  · exact u3304

def b15551 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 22 73 400 34 224 224 480), lower := (rows 13 35 22 73 400 34 64 128 256), losses := [] }

theorem u15551 : Upper (D 7) (R 7) [12,33,18,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15552 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 404, targets := 1 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 13 35 22 73 400 96 226 162 418), lower := (rows 13 35 22 73 400 96 64 128 256), losses := [] }

theorem u15552 : Upper (D 7) (R 7) [12,33,18,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15553 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 72, targets := 128 }], pairs := [(0,7),(2,0),(3,7),(4,0)], upper := (rows 13 35 22 73 400 160 98 226 354), lower := (rows 13 35 22 73 400 160 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 14 16 32 66 0 258), good := (rows 13 363 351 73 272 32 64 0 256) }] }

theorem u15553 : Upper (D 7) (R 7) [12,33,18,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15554 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 456, targets := 1 }], pairs := [(2,6),(3,0),(4,1),(4,6)], upper := (rows 13 35 22 74 145 96 480 416 416), lower := (rows 13 35 22 74 145 96 64 128 256), losses := [] }

theorem u15554 : Upper (D 7) (R 7) [12,33,18,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15555 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 38, targets := 64 },{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 328, targets := 1 }], pairs := [(1,6),(2,6),(3,0),(4,1)], upper := (rows 13 35 22 74 145 160 352 480 352), lower := (rows 13 35 22 74 145 160 64 128 256), losses := [] }

theorem u15555 : Upper (D 7) (R 7) [12,33,18,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15556 : Route 9 := (fun mask => (mask,id))

def c15556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15556 : Upper (D 7) (R 7) [12,33,18,66,129,256] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,129,256] 13 (by decide) (choices 1) [32,128] r15556 c15556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3305
  · exact u3306

def b15557 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 74 176 33 448 448 448), lower := (rows 13 35 22 74 176 33 64 128 256), losses := [] }

theorem u15557 : Upper (D 7) (R 7) [12,33,18,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15558 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,6),(3,5),(4,6)], upper := (rows 13 35 22 74 176 96 449 385 385), lower := (rows 13 35 22 74 176 96 64 128 256), losses := [] }

theorem u15558 : Upper (D 7) (R 7) [12,33,18,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15559 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 74 176 160 321 449 321), lower := (rows 13 35 22 74 176 160 64 128 256), losses := [] }

theorem u15559 : Upper (D 7) (R 7) [12,33,18,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15560 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 13 35 22 74 176 288 193 193 449), lower := (rows 13 35 22 74 176 288 64 128 256), losses := [] }

theorem u15560 : Upper (D 7) (R 7) [12,33,18,66,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15560 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15561 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 74 208 33 480 416 416), lower := (rows 13 35 22 74 208 33 64 128 256), losses := [] }

theorem u15561 : Upper (D 7) (R 7) [12,33,18,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15562 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 418, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(0,7),(1,6),(3,7),(4,1)], upper := (rows 13 35 22 74 208 160 353 417 289), lower := (rows 13 35 22 74 208 160 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 14 16 32 66 0 258), good := (rows 13 363 351 330 80 32 64 0 256) }] }

theorem u15562 : Upper (D 7) (R 7) [12,33,18,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15563 : Route 9 := (fun mask => (mask,id))

def c15563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15563 : Upper (D 7) (R 7) [12,33,18,66,192,256] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,192,256] 13 (by decide) (choices 1) [1,32,128] r15563 c15563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3307
  · exact u3308
  · exact u3309

def b15564 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 200, targets := 1 }], pairs := [(2,6),(3,0),(4,1),(4,6)], upper := (rows 13 35 22 74 273 96 224 160 416), lower := (rows 13 35 22 74 273 96 64 128 256), losses := [] }

theorem u15564 : Upper (D 7) (R 7) [12,33,18,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15565 : Route 9 := (fun mask => (mask,id))

def c15565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15565 : Upper (D 7) (R 7) [12,33,18,66,257,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,257,128] 13 (by decide) (choices 1) [32,128] r15565 c15565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3310
  · exact u3311

def b15566 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 74 304 33 192 192 448), lower := (rows 13 35 22 74 304 33 64 128 256), losses := [] }

theorem u15566 : Upper (D 7) (R 7) [12,33,18,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15567 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(2,6),(3,5),(4,6)], upper := (rows 13 35 22 74 304 96 193 129 385), lower := (rows 13 35 22 74 304 96 64 128 256), losses := [] }

theorem u15567 : Upper (D 7) (R 7) [12,33,18,66,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15568 : Route 9 := (fun mask => (mask,id))

def c15568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15568 : Upper (D 7) (R 7) [12,33,18,66,288,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,288,128] 13 (by decide) (choices 1) [1,128] r15568 c15568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3312
  · exact u3313

def b15569 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 74 336 33 224 160 416), lower := (rows 13 35 22 74 336 33 64 128 256), losses := [] }

theorem u15569 : Upper (D 7) (R 7) [12,33,18,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15570 : Route 9 := (fun mask => (mask,id))

def c15570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15570 : Upper (D 7) (R 7) [12,33,18,66,320,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,320,128] 13 (by decide) (choices 1) [1,32,128] r15570 c15570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3314
  · exact u3315
  · exact u3316

def b15571 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 74 400 33 224 224 480), lower := (rows 13 35 22 74 400 33 64 128 256), losses := [] }

theorem u15571 : Upper (D 7) (R 7) [12,33,18,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15572 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(2,6),(4,1),(4,6)], upper := (rows 13 35 22 74 400 96 225 161 417), lower := (rows 13 35 22 74 400 96 64 128 256), losses := [{ target := 6, region := (rows 9 2 14 8 30 32 0 130 258), good := (rows 29 439 406 415 400 32 0 128 256) }] }

theorem u15572 : Upper (D 7) (R 7) [12,33,18,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15573 : Route 9 := (fun mask => (mask,id))

def c15573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15573 : Upper (D 7) (R 7) [12,33,18,66,384,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,384,128] 13 (by decide) (choices 1) [1,32] r15573 c15573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3317
  · exact u3318

def b15574 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 22 104 145 34 448 448 448), lower := (rows 13 35 22 104 145 34 64 128 256), losses := [] }

theorem u15574 : Upper (D 7) (R 7) [12,33,18,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15575 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 35 22 104 145 96 450 386 386), lower := (rows 13 35 22 104 145 96 64 128 256), losses := [] }

theorem u15575 : Upper (D 7) (R 7) [12,33,18,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15576 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(2,5),(2,6),(4,5)], upper := (rows 13 35 22 104 145 160 322 450 322), lower := (rows 13 35 22 104 145 160 64 128 256), losses := [] }

theorem u15576 : Upper (D 7) (R 7) [12,33,18,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15577 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 200, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 13 35 22 104 145 288 194 194 450), lower := (rows 13 35 22 104 145 288 64 128 256), losses := [] }

theorem u15577 : Upper (D 7) (R 7) [12,33,18,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15577 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15578 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 104 208 33 450 386 386), lower := (rows 13 35 22 104 208 33 64 128 256), losses := [] }

theorem u15578 : Upper (D 7) (R 7) [12,33,18,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15579 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 104 208 34 449 385 385), lower := (rows 13 35 22 104 208 34 64 128 256), losses := [] }

theorem u15579 : Upper (D 7) (R 7) [12,33,18,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15580 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 4, region := 40, targets := 3 }], pairs := [(2,5),(3,0),(3,1),(4,5)], upper := (rows 13 35 22 104 208 160 323 387 259), lower := (rows 13 35 22 104 208 160 64 128 256), losses := [] }

theorem u15580 : Upper (D 7) (R 7) [12,33,18,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15581 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 13 35 22 104 208 288 195 131 387), lower := (rows 13 35 22 104 208 288 64 128 256), losses := [] }

theorem u15581 : Upper (D 7) (R 7) [12,33,18,96,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15581 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15582 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 22 104 273 34 192 192 448), lower := (rows 13 35 22 104 273 34 64 128 256), losses := [] }

theorem u15582 : Upper (D 7) (R 7) [12,33,18,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15583 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 35 22 104 273 96 194 130 386), lower := (rows 13 35 22 104 273 96 64 128 256), losses := [] }

theorem u15583 : Upper (D 7) (R 7) [12,33,18,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15584 : Route 9 := (fun mask => (mask,id))

def c15584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15584 : Upper (D 7) (R 7) [12,33,18,96,257,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,96,257,128] 13 (by decide) (choices 1) [2,128] r15584 c15584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3319
  · exact u3320

def b15585 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 104 336 33 194 130 386), lower := (rows 13 35 22 104 336 33 64 128 256), losses := [] }

theorem u15585 : Upper (D 7) (R 7) [12,33,18,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15586 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 104 336 34 193 129 385), lower := (rows 13 35 22 104 336 34 64 128 256), losses := [] }

theorem u15586 : Upper (D 7) (R 7) [12,33,18,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15587 : Route 9 := (fun mask => (mask,id))

def c15587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15587 : Upper (D 7) (R 7) [12,33,18,96,320,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,96,320,128] 13 (by decide) (choices 1) [1,2,128] r15587 c15587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3321
  · exact u3322
  · exact u3323

def b15588 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 104 400 33 194 194 450), lower := (rows 13 35 22 104 400 33 64 128 256), losses := [] }

theorem u15588 : Upper (D 7) (R 7) [12,33,18,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15589 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 22 104 400 34 193 193 449), lower := (rows 13 35 22 104 400 34 64 128 256), losses := [] }

theorem u15589 : Upper (D 7) (R 7) [12,33,18,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15590 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 35 22 104 400 96 195 131 387), lower := (rows 13 35 22 104 400 96 64 128 256), losses := [] }

theorem u15590 : Upper (D 7) (R 7) [12,33,18,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15591 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(0,7),(2,5),(3,7),(4,5)], upper := (rows 13 35 22 104 400 160 67 195 323), lower := (rows 13 35 22 104 400 160 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 10 16 32 70 0 262), good := (rows 333 363 351 104 272 32 64 0 256) }] }

theorem u15591 : Upper (D 7) (R 7) [12,33,18,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15592 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 200 81 34 480 416 416), lower := (rows 13 35 22 200 81 34 64 128 256), losses := [] }

theorem u15592 : Upper (D 7) (R 7) [12,33,18,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15593 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(2,7),(4,7)], upper := (rows 13 35 22 200 81 160 354 418 290), lower := (rows 13 35 22 200 81 160 64 128 256), losses := [] }

theorem u15593 : Upper (D 7) (R 7) [12,33,18,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15594 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 1, region := 200, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 13 35 22 200 81 288 226 162 418), lower := (rows 13 35 22 200 81 288 64 128 256), losses := [] }

theorem u15594 : Upper (D 7) (R 7) [12,33,18,192,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15594 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15595 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 200 112 33 450 386 386), lower := (rows 13 35 22 200 112 33 64 128 256), losses := [] }

theorem u15595 : Upper (D 7) (R 7) [12,33,18,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15596 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 35 22 200 112 34 449 385 385), lower := (rows 13 35 22 200 112 34 64 128 256), losses := [] }

theorem u15596 : Upper (D 7) (R 7) [12,33,18,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15597 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,7),(3,5),(4,7)], upper := (rows 13 35 22 200 112 160 323 387 259), lower := (rows 13 35 22 200 112 160 64 128 256), losses := [] }

theorem u15597 : Upper (D 7) (R 7) [12,33,18,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15598 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 13 35 22 200 112 288 195 131 387), lower := (rows 13 35 22 200 112 288 64 128 256), losses := [] }

theorem u15598 : Upper (D 7) (R 7) [12,33,18,192,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15598 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15599 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 22 200 273 34 224 224 480), lower := (rows 13 35 22 200 273 34 64 128 256), losses := [] }

theorem u15599 : Upper (D 7) (R 7) [12,33,18,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15599
end Delivery.IrregularNine14.P07
