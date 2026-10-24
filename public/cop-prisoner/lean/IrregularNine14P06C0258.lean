import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0060
import IrregularNine14P06C0061

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15480 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 131 52 73 84 288 102 166 294), lower := (rows 11 131 52 73 84 288 64 128 256), losses := [] }

theorem u15480 : Upper (D 6) (R 6) [10,129,48,65,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15480 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15481 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 73 276 34 100 228 356), lower := (rows 11 131 52 73 276 34 64 128 256), losses := [] }

theorem u15481 : Upper (D 6) (R 6) [10,129,48,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15482 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 73 276 36 98 226 354), lower := (rows 11 131 52 73 276 36 64 128 256), losses := [] }

theorem u15482 : Upper (D 6) (R 6) [10,129,48,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15483 : Route 9 := (fun mask => (mask,id))

def c15483 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15483 : Upper (D 6) (R 6) [10,129,48,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,129,48,65,260,64] 13 (by decide) (choices 1) [2,4,32] r15483 c15483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3644
  · exact u3645
  · exact u3646

def b15484 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 73 336 34 100 164 292), lower := (rows 11 131 52 73 336 34 64 128 256), losses := [] }

theorem u15484 : Upper (D 6) (R 6) [10,129,48,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15485 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 73 336 36 102 166 294), lower := (rows 11 131 52 73 336 36 64 128 256), losses := [] }

theorem u15485 : Upper (D 6) (R 6) [10,129,48,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15486 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 11 131 52 76 82 33 356 420 292), lower := (rows 11 131 52 76 82 33 64 128 256), losses := [] }

theorem u15486 : Upper (D 6) (R 6) [10,129,48,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15487 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 76 82 36 353 417 289), lower := (rows 11 131 52 76 82 36 64 128 256), losses := [] }

theorem u15487 : Upper (D 6) (R 6) [10,129,48,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15488 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 52 76 82 288 101 165 293), lower := (rows 11 131 52 76 82 288 64 128 256), losses := [] }

theorem u15488 : Upper (D 6) (R 6) [10,129,48,68,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15488 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15489 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 52 76 273 34 100 228 356), lower := (rows 11 131 52 76 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 16 35 84 148 276), good := (rows 42 162 508 460 508 34 64 128 256) }] }

theorem u15489 : Upper (D 6) (R 6) [10,129,48,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15490 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 76 273 36 98 226 354), lower := (rows 11 131 52 76 273 36 64 128 256), losses := [] }

theorem u15490 : Upper (D 6) (R 6) [10,129,48,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15491 : Route 9 := (fun mask => (mask,id))

def c15491 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15491 : Upper (D 6) (R 6) [10,129,48,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,257,64] 13 (by decide) (choices 1) [2,4,32] r15491 c15491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3647
  · exact u3648
  · exact u3649

def b15492 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 52 76 274 33 100 228 356), lower := (rows 11 131 52 76 274 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 28 16 35 84 148 276), good := (rows 41 161 508 460 508 33 64 128 256) }] }

theorem u15492 : Upper (D 6) (R 6) [10,129,48,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15493 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 76 274 36 97 225 353), lower := (rows 11 131 52 76 274 36 64 128 256), losses := [] }

theorem u15493 : Upper (D 6) (R 6) [10,129,48,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15494 : Route 9 := (fun mask => (mask,id))

def c15494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15494 : Upper (D 6) (R 6) [10,129,48,68,258,64] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,258,64] 13 (by decide) (choices 1) [1,4,32] r15494 c15494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3650
  · exact u3651
  · exact u3652

def r15495 : Route 9 := (fun mask => (mask,id))

def c15495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15495 : Upper (D 6) (R 6) [10,129,48,68,260,1] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,260,1] 13 (by decide) (choices 1) [2,32] r15495 c15495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3653
  · exact u3654

def r15496 : Route 9 := (fun mask => (mask,id))

def c15496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15496 : Upper (D 6) (R 6) [10,129,48,68,260,2] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,260,2] 13 (by decide) (choices 1) [1,32] r15496 c15496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3655
  · exact u3656

def r15497 : Route 9 := (fun mask => (mask,id))

def c15497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15497 : Upper (D 6) (R 6) [10,129,48,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,260,64] 13 (by decide) (choices 1) [1,2,32] r15497 c15497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3657
  · exact u3658
  · exact u3659

def r15498 : Route 9 := (fun mask => (mask,id))

def c15498 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15498 : Upper (D 6) (R 6) [10,129,48,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,320,1] 13 (by decide) (choices 1) [2,4,32] r15498 c15498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3660
  · exact u3661
  · exact u3662

def r15499 : Route 9 := (fun mask => (mask,id))

def c15499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15499 : Upper (D 6) (R 6) [10,129,48,68,320,2] 13 := by
  apply FastRouting.sound _ _ [10,129,48,68,320,2] 13 (by decide) (choices 1) [1,4,32] r15499 c15499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3663
  · exact u3664
  · exact u3665

def b15500 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 76 336 36 99 163 291), lower := (rows 11 131 52 76 336 36 64 128 256), losses := [] }

theorem u15500 : Upper (D 6) (R 6) [10,129,48,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15501 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 52 104 21 34 324 452 324), lower := (rows 11 131 52 104 21 34 64 128 256), losses := [] }

theorem u15501 : Upper (D 6) (R 6) [10,129,48,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15502 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 131 52 104 21 36 322 450 322), lower := (rows 11 131 52 104 21 36 64 128 256), losses := [] }

theorem u15502 : Upper (D 6) (R 6) [10,129,48,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15503 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 52 104 21 96 326 390 262), lower := (rows 11 131 52 104 21 96 64 128 256), losses := [] }

theorem u15503 : Upper (D 6) (R 6) [10,129,48,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15504 : Route 9 := (fun mask => (mask,id))

def c15504 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15504 : Upper (D 6) (R 6) [10,129,48,96,5,256] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,5,256] 13 (by decide) (choices 1) [2,4] r15504 c15504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3666
  · exact u3667

def b15505 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 52 104 22 33 324 452 324), lower := (rows 11 131 52 104 22 33 64 128 256), losses := [] }

theorem u15505 : Upper (D 6) (R 6) [10,129,48,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15506 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 131 52 104 22 36 321 449 321), lower := (rows 11 131 52 104 22 36 64 128 256), losses := [] }

theorem u15506 : Upper (D 6) (R 6) [10,129,48,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15507 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 52 104 22 96 325 389 261), lower := (rows 11 131 52 104 22 96 64 128 256), losses := [] }

theorem u15507 : Upper (D 6) (R 6) [10,129,48,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15508 : Route 9 := (fun mask => (mask,id))

def c15508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15508 : Upper (D 6) (R 6) [10,129,48,96,6,256] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,6,256] 13 (by decide) (choices 1) [1,4] r15508 c15508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3668
  · exact u3669

def b15509 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 131 52 104 81 34 324 388 260), lower := (rows 11 131 52 104 81 34 64 128 256), losses := [] }

theorem u15509 : Upper (D 6) (R 6) [10,129,48,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15510 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 104 81 36 326 390 262), lower := (rows 11 131 52 104 81 36 64 128 256), losses := [] }

theorem u15510 : Upper (D 6) (R 6) [10,129,48,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15511 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 131 52 104 81 288 70 134 262), lower := (rows 11 131 52 104 81 288 64 128 256), losses := [] }

theorem u15511 : Upper (D 6) (R 6) [10,129,48,96,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15511 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15512 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 11 131 52 104 82 33 324 388 260), lower := (rows 11 131 52 104 82 33 64 128 256), losses := [] }

theorem u15512 : Upper (D 6) (R 6) [10,129,48,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15513 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 104 82 36 325 389 261), lower := (rows 11 131 52 104 82 36 64 128 256), losses := [] }

theorem u15513 : Upper (D 6) (R 6) [10,129,48,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15514 : Route 9 := (fun mask => (mask,id))

def c15514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15514 : Upper (D 6) (R 6) [10,129,48,96,66,256] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,66,256] 13 (by decide) (choices 1) [1,4] r15514 c15514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3670
  · exact u3671

def b15515 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 52 104 273 34 68 196 324), lower := (rows 11 131 52 104 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 16 35 84 148 276), good := (rows 42 162 508 104 508 34 64 128 256) }] }

theorem u15515 : Upper (D 6) (R 6) [10,129,48,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15516 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 104 273 36 70 198 326), lower := (rows 11 131 52 104 273 36 64 128 256), losses := [] }

theorem u15516 : Upper (D 6) (R 6) [10,129,48,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15517 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 52 104 273 96 70 134 262), lower := (rows 11 131 52 104 273 96 64 128 256), losses := [] }

theorem u15517 : Upper (D 6) (R 6) [10,129,48,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15518 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 52 104 274 33 68 196 324), lower := (rows 11 131 52 104 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 17 32 108 172 300), good := (rows 474 146 508 492 274 508 64 128 256) }] }

theorem u15518 : Upper (D 6) (R 6) [10,129,48,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15519 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 104 274 36 69 197 325), lower := (rows 11 131 52 104 274 36 64 128 256), losses := [] }

theorem u15519 : Upper (D 6) (R 6) [10,129,48,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15520 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 52 104 274 96 69 133 261), lower := (rows 11 131 52 104 274 96 64 128 256), losses := [] }

theorem u15520 : Upper (D 6) (R 6) [10,129,48,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15521 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 52 104 276 33 70 198 326), lower := (rows 11 131 52 104 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 49 32 65 129 257), good := (rows 478 466 60 124 276 508 64 128 256) }] }

theorem u15521 : Upper (D 6) (R 6) [10,129,48,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15522 : Route 9 := (fun mask => (mask,id))

def c15522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15522 : Upper (D 6) (R 6) [10,129,48,96,260,2] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,260,2] 13 (by decide) (choices 1) [1,4] r15522 c15522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3672
  · exact u3673

def b15523 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 104 276 36 67 195 323), lower := (rows 11 131 52 104 276 36 64 128 256), losses := [] }

theorem u15523 : Upper (D 6) (R 6) [10,129,48,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15524 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 52 104 276 96 71 135 263), lower := (rows 11 131 52 104 276 96 64 128 256), losses := [] }

theorem u15524 : Upper (D 6) (R 6) [10,129,48,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15525 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 52 104 336 33 70 134 262), lower := (rows 11 131 52 104 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 51 32 65 129 257), good := (rows 478 466 60 124 336 508 64 128 256) }] }

theorem u15525 : Upper (D 6) (R 6) [10,129,48,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15526 : Route 9 := (fun mask => (mask,id))

def c15526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15526 : Upper (D 6) (R 6) [10,129,48,96,320,2] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,320,2] 13 (by decide) (choices 1) [1,4] r15526 c15526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3674
  · exact u3675

def b15527 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 104 336 36 71 135 263), lower := (rows 11 131 52 104 336 36 64 128 256), losses := [] }

theorem u15527 : Upper (D 6) (R 6) [10,129,48,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15528 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 265 84 34 100 228 356), lower := (rows 11 131 52 265 84 34 64 128 256), losses := [] }

theorem u15528 : Upper (D 6) (R 6) [10,129,48,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15529 : PairBound 9 := { available := 98, camps := [{ cop := 6, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 265 84 36 98 226 354), lower := (rows 11 131 52 265 84 36 64 128 256), losses := [] }

theorem u15529 : Upper (D 6) (R 6) [10,129,48,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15530 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 265 84 96 102 166 294), lower := (rows 11 131 52 265 84 96 64 128 256), losses := [] }

theorem u15530 : Upper (D 6) (R 6) [10,129,48,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15531 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 52 268 81 34 100 228 356), lower := (rows 11 131 52 268 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 16 35 84 148 276), good := (rows 42 162 508 460 508 34 64 128 256) }] }

theorem u15531 : Upper (D 6) (R 6) [10,129,48,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15532 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 268 81 36 98 226 354), lower := (rows 11 131 52 268 81 36 64 128 256), losses := [] }

theorem u15532 : Upper (D 6) (R 6) [10,129,48,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15533 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 52 268 81 96 102 166 294), lower := (rows 11 131 52 268 81 96 64 128 256), losses := [] }

theorem u15533 : Upper (D 6) (R 6) [10,129,48,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15534 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 52 268 82 33 100 228 356), lower := (rows 11 131 52 268 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 28 16 35 84 148 276), good := (rows 41 161 508 460 508 33 64 128 256) }] }

theorem u15534 : Upper (D 6) (R 6) [10,129,48,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15535 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 268 82 36 97 225 353), lower := (rows 11 131 52 268 82 36 64 128 256), losses := [] }

theorem u15535 : Upper (D 6) (R 6) [10,129,48,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15536 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 52 268 82 96 101 165 293), lower := (rows 11 131 52 268 82 96 64 128 256), losses := [] }

theorem u15536 : Upper (D 6) (R 6) [10,129,48,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15537 : Route 9 := (fun mask => (mask,id))

def c15537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15537 : Upper (D 6) (R 6) [10,129,48,260,68,1] 13 := by
  apply FastRouting.sound _ _ [10,129,48,260,68,1] 13 (by decide) (choices 1) [2,32] r15537 c15537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3676
  · exact u3677

def r15538 : Route 9 := (fun mask => (mask,id))

def c15538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15538 : Upper (D 6) (R 6) [10,129,48,260,68,2] 13 := by
  apply FastRouting.sound _ _ [10,129,48,260,68,2] 13 (by decide) (choices 1) [1,32] r15538 c15538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3678
  · exact u3679

def b15539 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 268 84 96 99 163 291), lower := (rows 11 131 52 268 84 96 64 128 256), losses := [] }

theorem u15539 : Upper (D 6) (R 6) [10,129,48,260,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15539
end Delivery.IrregularNine14.P06
