import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0345
import IrregularNine14P06C0346
import IrregularNine14P06C0347

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36360 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 388 28 88 35 99 163 291), lower := (rows 35 70 388 28 88 32 64 128 256), losses := [] }

theorem u36360 : Upper (D 6) (R 6) [34,68,384,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36361 : Route 9 := (fun mask => (mask,id))

def c36361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36361 : Upper (D 6) (R 6) [34,68,384,20,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,20,96] 13 (by decide) (choices 1) [1,2,8] r36361 c36361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20747
  · exact u20748
  · exact u20749

def b36362 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 388 41 81 62 94 158 286), lower := (rows 35 70 388 41 81 32 64 128 256), losses := [] }

theorem u36362 : Upper (D 6) (R 6) [34,68,384,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36363 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 388 41 88 55 87 151 279), lower := (rows 35 70 388 41 88 32 64 128 256), losses := [] }

theorem u36363 : Upper (D 6) (R 6) [34,68,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36364 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 388 42 81 61 93 157 285), lower := (rows 35 70 388 42 81 32 64 128 256), losses := [] }

theorem u36364 : Upper (D 6) (R 6) [34,68,384,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36365 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 388 42 88 53 85 149 277), lower := (rows 35 70 388 42 88 32 64 128 256), losses := [] }

theorem u36365 : Upper (D 6) (R 6) [34,68,384,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36366 : Route 9 := (fun mask => (mask,id))

def c36366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36366 : Upper (D 6) (R 6) [34,68,384,36,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,36,65] 13 (by decide) (choices 1) [1,2,8,16] r36366 c36366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20750
  · exact u20751
  · exact u20752
  · exact u20753

def b36367 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 388 44 82 57 89 153 281), lower := (rows 35 70 388 44 82 32 64 128 256), losses := [] }

theorem u36367 : Upper (D 6) (R 6) [34,68,384,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36368 : Route 9 := (fun mask => (mask,id))

def c36368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36368 : Upper (D 6) (R 6) [34,68,384,36,72] 13 := by
  apply FastRouting.sound _ _ [34,68,384,36,72] 13 (by decide) (choices 1) [1,2,16] r36368 c36368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20754
  · exact u20755
  · exact u20756

def r36369 : Route 9 := (fun mask => (mask,id))

def c36369 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36369 : Upper (D 6) (R 6) [34,68,384,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,65] 13 (by decide) (choices 1) [1,2,4,8] r36369 c36369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20757
  · exact u20758
  · exact u20759
  · exact u20760

def b36370 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 388 56 82 45 77 141 269), lower := (rows 35 70 388 56 82 32 64 128 256), losses := [] }

theorem u36370 : Upper (D 6) (R 6) [34,68,384,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36371 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 388 56 84 43 75 139 267), lower := (rows 35 70 388 56 84 32 64 128 256), losses := [] }

theorem u36371 : Upper (D 6) (R 6) [34,68,384,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36372 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 70 388 56 88 39 71 135 263), lower := (rows 35 70 388 56 88 32 64 128 256), losses := [] }

theorem u36372 : Upper (D 6) (R 6) [34,68,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36373 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 13 19 484 452 452 452), lower := (rows 35 74 52 13 19 32 64 128 256), losses := [] }

theorem u36373 : Upper (D 6) (R 6) [34,72,48,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36374 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 74 52 13 21 482 450 450 450), lower := (rows 35 74 52 13 21 32 64 128 256), losses := [] }

theorem u36374 : Upper (D 6) (R 6) [34,72,48,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36375 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 13 22 481 449 449 449), lower := (rows 35 74 52 13 22 32 64 128 256), losses := [] }

theorem u36375 : Upper (D 6) (R 6) [34,72,48,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36376 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 74 52 13 81 422 454 390 390), lower := (rows 35 74 52 13 81 32 64 128 256), losses := [] }

theorem u36376 : Upper (D 6) (R 6) [34,72,48,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36377 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 52 13 82 421 453 389 389), lower := (rows 35 74 52 13 82 32 64 128 256), losses := [] }

theorem u36377 : Upper (D 6) (R 6) [34,72,48,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36378 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 483, targets := 4 },{ cop := 3, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 74 52 13 84 419 451 387 387), lower := (rows 35 74 52 13 84 32 64 128 256), losses := [] }

theorem u36378 : Upper (D 6) (R 6) [34,72,48,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36379 : PairBound 9 := { available := 326, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 3, region := 322, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 74 52 13 145 358 326 454 326), lower := (rows 35 74 52 13 145 32 64 128 256), losses := [] }

theorem u36379 : Upper (D 6) (R 6) [34,72,48,5,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36380 : Route 9 := (fun mask => (mask,id))

def c36380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36380 : Upper (D 6) (R 6) [34,72,48,5,130] 13 := by
  apply FastRouting.sound _ _ [34,72,48,5,130] 13 (by decide) (choices 1) [1,4,64,256] r36380 c36380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20761
  · exact u20762
  · exact u20763
  · exact u20764

def b36381 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 3, region := 322, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 74 52 13 148 355 323 451 323), lower := (rows 35 74 52 13 148 32 64 128 256), losses := [] }

theorem u36381 : Upper (D 6) (R 6) [34,72,48,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36382 : Route 9 := (fun mask => (mask,id))

def c36382 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36382 : Upper (D 6) (R 6) [34,72,48,5,192] 13 := by
  apply FastRouting.sound _ _ [34,72,48,5,192] 13 (by decide) (choices 1) [1,2,4,256] r36382 c36382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20765
  · exact u20766
  · exact u20767
  · exact u20768

def r36383 : Route 9 := (fun mask => (mask,id))

def c36383 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36383 : Upper (D 6) (R 6) [34,72,48,5,384] 13 := by
  apply FastRouting.sound _ _ [34,72,48,5,384] 13 (by decide) (choices 1) [1,2,4,64] r36383 c36383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20769
  · exact u20770
  · exact u20771
  · exact u20772

def b36384 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 14 21 481 449 449 449), lower := (rows 35 74 52 14 21 32 64 128 256), losses := [] }

theorem u36384 : Upper (D 6) (R 6) [34,72,48,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36385 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 52 14 81 421 453 389 389), lower := (rows 35 74 52 14 81 32 64 128 256), losses := [] }

theorem u36385 : Upper (D 6) (R 6) [34,72,48,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36386 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 52 14 84 417 449 385 385), lower := (rows 35 74 52 14 84 32 64 128 256), losses := [] }

theorem u36386 : Upper (D 6) (R 6) [34,72,48,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36387 : Route 9 := (fun mask => (mask,id))

def c36387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36387 : Upper (D 6) (R 6) [34,72,48,6,129] 13 := by
  apply FastRouting.sound _ _ [34,72,48,6,129] 13 (by decide) (choices 1) [1,4,64,256] r36387 c36387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20773
  · exact u20774
  · exact u20775
  · exact u20776

def b36388 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 353, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 52 14 148 353 321 449 321), lower := (rows 35 74 52 14 148 32 64 128 256), losses := [] }

theorem u36388 : Upper (D 6) (R 6) [34,72,48,6,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36389 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 289, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 52 14 208 293 325 389 261), lower := (rows 35 74 52 14 208 32 64 128 256), losses := [] }

theorem u36389 : Upper (D 6) (R 6) [34,72,48,6,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36390 : Route 9 := (fun mask => (mask,id))

def c36390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36390 : Upper (D 6) (R 6) [34,72,48,6,384] 13 := by
  apply FastRouting.sound _ _ [34,72,48,6,384] 13 (by decide) (choices 1) [1,4,64] r36390 c36390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20777
  · exact u20778
  · exact u20779

def b36391 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 35 74 52 137 19 356 324 452 324), lower := (rows 35 74 52 137 19 32 64 128 256), losses := [] }

theorem u36391 : Upper (D 6) (R 6) [34,72,48,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36392 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 52 137 21 358 326 454 326), lower := (rows 35 74 52 137 21 32 64 128 256), losses := [] }

theorem u36392 : Upper (D 6) (R 6) [34,72,48,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36393 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 20, targets := 1 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 35 74 52 137 22 357 325 453 325), lower := (rows 35 74 52 137 22 32 64 128 256), losses := [] }

theorem u36393 : Upper (D 6) (R 6) [34,72,48,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36394 : Route 9 := (fun mask => (mask,id))

def c36394 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36394 : Upper (D 6) (R 6) [34,72,48,129,65] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129,65] 13 (by decide) (choices 1) [2,4,256] r36394 c36394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20780
  · exact u20781
  · exact u20782

def b36395 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 52 137 82 293 325 389 261), lower := (rows 35 74 52 137 82 32 64 128 256), losses := [] }

theorem u36395 : Upper (D 6) (R 6) [34,72,48,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36396 : Route 9 := (fun mask => (mask,id))

def c36396 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36396 : Upper (D 6) (R 6) [34,72,48,129,68] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129,68] 13 (by decide) (choices 1) [1,2,4,256] r36396 c36396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20783
  · exact u20784
  · exact u20785
  · exact u20786

def r36397 : Route 9 := (fun mask => (mask,id))

def c36397 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36397 : Upper (D 6) (R 6) [34,72,48,129,257] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129,257] 13 (by decide) (choices 1) [2,4,64] r36397 c36397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20787
  · exact u20788
  · exact u20789

def r36398 : Route 9 := (fun mask => (mask,id))

def c36398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36398 : Upper (D 6) (R 6) [34,72,48,129,258] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129,258] 13 (by decide) (choices 1) [1,4,64] r36398 c36398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20790
  · exact u20791
  · exact u20792

def r36399 : Route 9 := (fun mask => (mask,id))

def c36399 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36399 : Upper (D 6) (R 6) [34,72,48,129,260] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129,260] 13 (by decide) (choices 1) [1,2,4,64] r36399 c36399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20793
  · exact u20794
  · exact u20795
  · exact u20796

def r36400 : Route 9 := (fun mask => (mask,id))

def c36400 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36400 : Upper (D 6) (R 6) [34,72,48,129,320] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129,320] 13 (by decide) (choices 1) [1,2,4] r36400 c36400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20797
  · exact u20798
  · exact u20799

def b36401 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 20, targets := 2 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 52 138 21 357 325 453 325), lower := (rows 35 74 52 138 21 32 64 128 256), losses := [] }

theorem u36401 : Upper (D 6) (R 6) [34,72,48,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36402 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 52 138 81 293 325 389 261), lower := (rows 35 74 52 138 81 32 64 128 256), losses := [] }

theorem u36402 : Upper (D 6) (R 6) [34,72,48,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36403 : Route 9 := (fun mask => (mask,id))

def c36403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36403 : Upper (D 6) (R 6) [34,72,48,130,68] 13 := by
  apply FastRouting.sound _ _ [34,72,48,130,68] 13 (by decide) (choices 1) [1,4,256] r36403 c36403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20800
  · exact u20801
  · exact u20802

def r36404 : Route 9 := (fun mask => (mask,id))

def c36404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36404 : Upper (D 6) (R 6) [34,72,48,130,257] 13 := by
  apply FastRouting.sound _ _ [34,72,48,130,257] 13 (by decide) (choices 1) [1,4,64] r36404 c36404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20803
  · exact u20804
  · exact u20805

def r36405 : Route 9 := (fun mask => (mask,id))

def c36405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36405 : Upper (D 6) (R 6) [34,72,48,130,260] 13 := by
  apply FastRouting.sound _ _ [34,72,48,130,260] 13 (by decide) (choices 1) [1,4,64] r36405 c36405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20806
  · exact u20807
  · exact u20808

def r36406 : Route 9 := (fun mask => (mask,id))

def c36406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36406 : Upper (D 6) (R 6) [34,72,48,130,320] 13 := by
  apply FastRouting.sound _ _ [34,72,48,130,320] 13 (by decide) (choices 1) [1,4] r36406 c36406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20809
  · exact u20810

def b36407 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 35 74 52 140 19 357 325 453 325), lower := (rows 35 74 52 140 19 32 64 128 256), losses := [] }

theorem u36407 : Upper (D 6) (R 6) [34,72,48,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36408 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 52 140 21 355 323 451 323), lower := (rows 35 74 52 140 21 32 64 128 256), losses := [] }

theorem u36408 : Upper (D 6) (R 6) [34,72,48,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36409 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 20, targets := 1 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 35 74 52 140 22 353 321 449 321), lower := (rows 35 74 52 140 22 32 64 128 256), losses := [] }

theorem u36409 : Upper (D 6) (R 6) [34,72,48,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36410 : Route 9 := (fun mask => (mask,id))

def c36410 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36410 : Upper (D 6) (R 6) [34,72,48,132,65] 13 := by
  apply FastRouting.sound _ _ [34,72,48,132,65] 13 (by decide) (choices 1) [1,2,4,256] r36410 c36410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20811
  · exact u20812
  · exact u20813
  · exact u20814

def b36411 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 52 140 82 293 325 389 261), lower := (rows 35 74 52 140 82 32 64 128 256), losses := [] }

theorem u36411 : Upper (D 6) (R 6) [34,72,48,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36412 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 52 140 84 291 323 387 259), lower := (rows 35 74 52 140 84 32 64 128 256), losses := [] }

theorem u36412 : Upper (D 6) (R 6) [34,72,48,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36413 : Route 9 := (fun mask => (mask,id))

def c36413 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36413 : Upper (D 6) (R 6) [34,72,48,132,257] 13 := by
  apply FastRouting.sound _ _ [34,72,48,132,257] 13 (by decide) (choices 1) [1,2,4,64] r36413 c36413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20815
  · exact u20816
  · exact u20817
  · exact u20818

def r36414 : Route 9 := (fun mask => (mask,id))

def c36414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36414 : Upper (D 6) (R 6) [34,72,48,132,258] 13 := by
  apply FastRouting.sound _ _ [34,72,48,132,258] 13 (by decide) (choices 1) [1,4,64] r36414 c36414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20819
  · exact u20820
  · exact u20821

def r36415 : Route 9 := (fun mask => (mask,id))

def c36415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36415 : Upper (D 6) (R 6) [34,72,48,132,260] 13 := by
  apply FastRouting.sound _ _ [34,72,48,132,260] 13 (by decide) (choices 1) [1,2,64] r36415 c36415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20822
  · exact u20823
  · exact u20824

def r36416 : Route 9 := (fun mask => (mask,id))

def c36416 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36416 : Upper (D 6) (R 6) [34,72,48,132,320] 13 := by
  apply FastRouting.sound _ _ [34,72,48,132,320] 13 (by decide) (choices 1) [1,2,4] r36416 c36416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20825
  · exact u20826
  · exact u20827

def b36417 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 35 74 52 392 19 101 69 197 325), lower := (rows 35 74 52 392 19 32 64 128 256), losses := [] }

theorem u36417 : Upper (D 6) (R 6) [34,72,48,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36418 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 52 392 21 103 71 199 327), lower := (rows 35 74 52 392 21 32 64 128 256), losses := [] }

theorem u36418 : Upper (D 6) (R 6) [34,72,48,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36419 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 20, targets := 1 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 35 74 52 392 22 101 69 197 325), lower := (rows 35 74 52 392 22 32 64 128 256), losses := [] }

theorem u36419 : Upper (D 6) (R 6) [34,72,48,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36419
end Delivery.IrregularNine14.P06
