import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0040

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12480 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 268 112 34 84 212 340), lower := (rows 11 35 133 268 112 34 64 128 256), losses := [] }

theorem u12480 : Upper (D 6) (R 6) [10,33,129,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12481 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 133 268 112 36 82 210 338), lower := (rows 11 35 133 268 112 36 64 128 256), losses := [] }

theorem u12481 : Upper (D 6) (R 6) [10,33,129,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12482 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 133 268 112 48 70 198 326), lower := (rows 11 35 133 268 112 48 64 128 256), losses := [] }

theorem u12482 : Upper (D 6) (R 6) [10,33,129,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12482 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12483 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 133 268 112 96 86 150 278), lower := (rows 11 35 133 268 112 96 64 128 256), losses := [] }

theorem u12483 : Upper (D 6) (R 6) [10,33,129,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12484 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 280 52 34 68 196 324), lower := (rows 11 35 133 280 52 34 64 128 256), losses := [] }

theorem u12484 : Upper (D 6) (R 6) [10,33,129,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12485 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 133 280 52 36 66 194 322), lower := (rows 11 35 133 280 52 36 64 128 256), losses := [] }

theorem u12485 : Upper (D 6) (R 6) [10,33,129,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12486 : Route 9 := (fun mask => (mask,id))

def c12486 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12486 : Upper (D 6) (R 6) [10,33,129,272,36,64] 13 := by
  apply FastRouting.sound _ _ [10,33,129,272,36,64] 13 (by decide) (choices 1) [2,4] r12486 c12486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2416
  · exact u2417

def b12487 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,1),(3,0)], upper := (rows 11 35 133 280 82 36 100 228 356), lower := (rows 11 35 133 280 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 36 100 164 292), good := (rows 26 506 484 280 90 484 64 128 256) }] }

theorem u12487 : Upper (D 6) (R 6) [10,33,129,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12488 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 35 133 280 82 96 100 164 292), lower := (rows 11 35 133 280 82 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 127 87 151 279), good := (rows 493 485 485 504 508 96 96 128 256) }] }

theorem u12488 : Upper (D 6) (R 6) [10,33,129,272,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12489 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 280 84 34 100 228 356), lower := (rows 11 35 133 280 84 34 64 128 256), losses := [] }

theorem u12489 : Upper (D 6) (R 6) [10,33,129,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12490 : Route 9 := (fun mask => (mask,id))

def c12490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12490 : Upper (D 6) (R 6) [10,33,129,272,68,4] 13 := by
  apply FastRouting.sound _ _ [10,33,129,272,68,4] 13 (by decide) (choices 1) [2,32] r12490 c12490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2418
  · exact u2419

def b12491 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 132, targets := 64 }], pairs := [(0,2),(1,2),(2,6)], upper := (rows 11 35 133 280 84 96 102 166 294), lower := (rows 11 35 133 280 84 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 112 64 128 256), good := (rows 11 35 129 315 112 96 96 128 256) }] }

theorem u12491 : Upper (D 6) (R 6) [10,33,129,272,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12492 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 280 112 34 68 196 324), lower := (rows 11 35 133 280 112 34 64 128 256), losses := [] }

theorem u12492 : Upper (D 6) (R 6) [10,33,129,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12493 : Route 9 := (fun mask => (mask,id))

def c12493 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12493 : Upper (D 6) (R 6) [10,33,129,272,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,129,272,96,4] 13 (by decide) (choices 1) [2,4] r12493 c12493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2420
  · exact u2421

def b12494 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 133 280 112 96 70 134 262), lower := (rows 11 35 133 280 112 96 64 128 256), losses := [] }

theorem u12494 : Upper (D 6) (R 6) [10,33,129,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12495 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 50, targets := 64 },{ cop := 4, region := 360, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 35 133 328 22 36 112 240 368), lower := (rows 11 35 133 328 22 36 64 128 256), losses := [] }

theorem u12495 : Upper (D 6) (R 6) [10,33,129,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12496 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 133 328 22 48 100 228 356), lower := (rows 11 35 133 328 22 48 64 128 256), losses := [] }

theorem u12496 : Upper (D 6) (R 6) [10,33,129,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12496 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12497 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 328 22 96 116 180 308), lower := (rows 11 35 133 328 22 96 64 128 256), losses := [] }

theorem u12497 : Upper (D 6) (R 6) [10,33,129,320,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12498 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 328 52 34 84 212 340), lower := (rows 11 35 133 328 52 34 64 128 256), losses := [] }

theorem u12498 : Upper (D 6) (R 6) [10,33,129,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12499 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 133 328 52 36 82 210 338), lower := (rows 11 35 133 328 52 36 64 128 256), losses := [] }

theorem u12499 : Upper (D 6) (R 6) [10,33,129,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12500 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 133 328 52 48 70 198 326), lower := (rows 11 35 133 328 52 48 64 128 256), losses := [] }

theorem u12500 : Upper (D 6) (R 6) [10,33,129,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12500 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12501 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 133 328 52 96 86 150 278), lower := (rows 11 35 133 328 52 96 64 128 256), losses := [] }

theorem u12501 : Upper (D 6) (R 6) [10,33,129,320,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12502 : Route 9 := (fun mask => (mask,id))

def c12502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12502 : Upper (D 6) (R 6) [10,33,129,320,66,4] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,66,4] 13 (by decide) (choices 1) [4,16,32] r12502 c12502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2422
  · exact u2423
  · exact u2424

def b12503 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 133 328 82 48 100 164 292), lower := (rows 11 35 133 328 82 48 64 128 256), losses := [] }

theorem u12503 : Upper (D 6) (R 6) [10,33,129,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12503 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12504 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 328 84 34 116 180 308), lower := (rows 11 35 133 328 84 34 64 128 256), losses := [] }

theorem u12504 : Upper (D 6) (R 6) [10,33,129,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12505 : Route 9 := (fun mask => (mask,id))

def c12505 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12505 : Upper (D 6) (R 6) [10,33,129,320,68,4] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,68,4] 13 (by decide) (choices 1) [2,16,32] r12505 c12505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2425
  · exact u2426
  · exact u2427

def r12506 : Route 9 := (fun mask => (mask,id))

def c12506 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12506 : Upper (D 6) (R 6) [10,33,129,320,68,16] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,68,16] 13 (by decide) (choices 1) [2,4,32] r12506 c12506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2428
  · exact u2429
  · exact u2430

def b12507 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 133 328 112 34 84 148 276), lower := (rows 11 35 133 328 112 34 64 128 256), losses := [] }

theorem u12507 : Upper (D 6) (R 6) [10,33,129,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12508 : Route 9 := (fun mask => (mask,id))

def c12508 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12508 : Upper (D 6) (R 6) [10,33,129,320,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,96,4] 13 (by decide) (choices 1) [2,4,16] r12508 c12508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2431
  · exact u2432
  · exact u2433

def b12509 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 133 328 112 48 70 134 262), lower := (rows 11 35 133 328 112 48 64 128 256), losses := [] }

theorem u12509 : Upper (D 6) (R 6) [10,33,129,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12509 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12510 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 28 112 33 324 452 324), lower := (rows 11 35 134 28 112 33 64 128 256), losses := [] }

theorem u12510 : Upper (D 6) (R 6) [10,33,130,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12511 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 35 134 28 112 36 321 449 321), lower := (rows 11 35 134 28 112 36 64 128 256), losses := [] }

theorem u12511 : Upper (D 6) (R 6) [10,33,130,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12512 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 134 28 112 96 325 389 261), lower := (rows 11 35 134 28 112 96 64 128 256), losses := [] }

theorem u12512 : Upper (D 6) (R 6) [10,33,130,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12513 : Route 9 := (fun mask => (mask,id))

def c12513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12513 : Upper (D 6) (R 6) [10,33,130,20,96,256] 13 := by
  apply FastRouting.sound _ _ [10,33,130,20,96,256] 13 (by decide) (choices 1) [1,4] r12513 c12513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2434
  · exact u2435

def b12514 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 28 304 33 68 196 324), lower := (rows 11 35 134 28 304 33 64 128 256), losses := [] }

theorem u12514 : Upper (D 6) (R 6) [10,33,130,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12515 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 35 134 28 304 36 65 193 321), lower := (rows 11 35 134 28 304 36 64 128 256), losses := [] }

theorem u12515 : Upper (D 6) (R 6) [10,33,130,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12516 : Route 9 := (fun mask => (mask,id))

def c12516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12516 : Upper (D 6) (R 6) [10,33,130,20,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,130,20,288,64] 13 (by decide) (choices 1) [1,4] r12516 c12516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2436
  · exact u2437

def b12517 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 28 336 33 100 228 356), lower := (rows 11 35 134 28 336 33 64 128 256), losses := [] }

theorem u12517 : Upper (D 6) (R 6) [10,33,130,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12518 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 134 28 336 36 97 225 353), lower := (rows 11 35 134 28 336 36 64 128 256), losses := [] }

theorem u12518 : Upper (D 6) (R 6) [10,33,130,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12519 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 132, targets := 64 }], pairs := [(0,2),(1,2),(2,6)], upper := (rows 11 35 134 28 336 96 101 165 293), lower := (rows 11 35 134 28 336 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 112 64 128 256), good := (rows 11 35 130 59 368 96 96 128 256) }] }

theorem u12519 : Upper (D 6) (R 6) [10,33,130,20,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12520 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 134 76 52 33 336 464 336), lower := (rows 11 35 134 76 52 33 64 128 256), losses := [] }

theorem u12520 : Upper (D 6) (R 6) [10,33,130,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12521 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 134 76 52 48 321 449 321), lower := (rows 11 35 134 76 52 48 64 128 256), losses := [] }

theorem u12521 : Upper (D 6) (R 6) [10,33,130,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12521 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12522 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,6),(4,0),(4,6)], upper := (rows 11 35 134 76 52 96 337 401 273), lower := (rows 11 35 134 76 52 96 64 128 256), losses := [] }

theorem u12522 : Upper (D 6) (R 6) [10,33,130,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12523 : Route 9 := (fun mask => (mask,id))

def c12523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12523 : Upper (D 6) (R 6) [10,33,130,68,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,36,256] 13 (by decide) (choices 1) [1,16] r12523 c12523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2438
  · exact u2439

def b12524 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 134 76 81 36 368 432 304), lower := (rows 11 35 134 76 81 36 64 128 256), losses := [] }

theorem u12524 : Upper (D 6) (R 6) [10,33,130,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12525 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 134 76 81 48 356 420 292), lower := (rows 11 35 134 76 81 48 64 128 256), losses := [] }

theorem u12525 : Upper (D 6) (R 6) [10,33,130,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12525 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12526 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 35 134 76 81 288 116 180 308), lower := (rows 11 35 134 76 81 288 64 128 256), losses := [] }

theorem u12526 : Upper (D 6) (R 6) [10,33,130,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12526 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12527 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 134 76 112 33 340 404 276), lower := (rows 11 35 134 76 112 33 64 128 256), losses := [] }

theorem u12527 : Upper (D 6) (R 6) [10,33,130,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12528 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 11 35 134 76 112 36 337 401 273), lower := (rows 11 35 134 76 112 36 64 128 256), losses := [] }

theorem u12528 : Upper (D 6) (R 6) [10,33,130,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12529 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 134 76 112 48 325 389 261), lower := (rows 11 35 134 76 112 48 64 128 256), losses := [] }

theorem u12529 : Upper (D 6) (R 6) [10,33,130,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12529 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12530 : Route 9 := (fun mask => (mask,id))

def c12530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12530 : Upper (D 6) (R 6) [10,33,130,68,96,256] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,96,256] 13 (by decide) (choices 1) [1,4,16] r12530 c12530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2440
  · exact u2441
  · exact u2442

def b12531 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 134 76 273 36 112 240 368), lower := (rows 11 35 134 76 273 36 64 128 256), losses := [] }

theorem u12531 : Upper (D 6) (R 6) [10,33,130,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12532 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 134 76 273 48 100 228 356), lower := (rows 11 35 134 76 273 48 64 128 256), losses := [] }

theorem u12532 : Upper (D 6) (R 6) [10,33,130,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12532 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12533 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 76 273 96 116 180 308), lower := (rows 11 35 134 76 273 96 64 128 256), losses := [] }

theorem u12533 : Upper (D 6) (R 6) [10,33,130,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12534 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 76 276 33 112 240 368), lower := (rows 11 35 134 76 276 33 64 128 256), losses := [] }

theorem u12534 : Upper (D 6) (R 6) [10,33,130,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12535 : PairBound 9 := { available := 97, camps := [], pairs := [(3,1),(4,1)], upper := (rows 11 35 134 76 276 48 97 225 353), lower := (rows 11 35 134 76 276 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 60 67 131 259), good := (rows 489 481 508 124 316 48 64 128 256) }] }

theorem u12535 : Upper (D 6) (R 6) [10,33,130,68,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12535 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12536 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 76 276 96 113 177 305), lower := (rows 11 35 134 76 276 96 64 128 256), losses := [] }

theorem u12536 : Upper (D 6) (R 6) [10,33,130,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12537 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 76 304 33 84 212 340), lower := (rows 11 35 134 76 304 33 64 128 256), losses := [] }

theorem u12537 : Upper (D 6) (R 6) [10,33,130,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12538 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 134 76 304 36 81 209 337), lower := (rows 11 35 134 76 304 36 64 128 256), losses := [] }

theorem u12538 : Upper (D 6) (R 6) [10,33,130,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12539 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 134 76 304 48 69 197 325), lower := (rows 11 35 134 76 304 48 64 128 256), losses := [] }

theorem u12539 : Upper (D 6) (R 6) [10,33,130,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12539 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12539
end Delivery.IrregularNine14.P06
