import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0009

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7440 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 132, targets := 33 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(2,0),(2,5)], upper := (rows 37 74 196 168 273 48 65 130 258), lower := (rows 37 74 196 168 273 48 65 128 256), losses := [] }

theorem u7440 : Upper (D 7) (R 7) [36,72,192,160,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7440 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7441 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 196 168 273 48 66 131 259), lower := (rows 37 74 196 168 273 48 66 128 256), losses := [] }

theorem u7441 : Upper (D 7) (R 7) [36,72,192,160,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7441 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7442 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(3,1),(3,6)], upper := (rows 37 74 196 265 19 34 80 160 416), lower := (rows 37 74 196 265 19 34 80 128 256), losses := [] }

theorem u7442 : Upper (D 7) (R 7) [36,72,192,257,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7442 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7443 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 114, targets := 128 },{ cop := 4, region := 392, targets := 34 }], pairs := [(1,7),(3,1),(3,5),(4,7)], upper := (rows 37 74 196 265 19 34 96 144 400), lower := (rows 37 74 196 265 19 34 96 128 256), losses := [] }

theorem u7443 : Upper (D 7) (R 7) [36,72,192,257,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7444 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 265 19 34 192 176 304), lower := (rows 37 74 196 265 19 34 192 128 256), losses := [] }

theorem u7444 : Upper (D 7) (R 7) [36,72,192,257,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7445 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,5),(3,1),(3,6)], upper := (rows 37 74 196 265 19 48 66 160 416), lower := (rows 37 74 196 265 19 48 66 128 256), losses := [] }

theorem u7445 : Upper (D 7) (R 7) [36,72,192,257,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7445 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7446 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 132, targets := 33 },{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7),(2,0),(2,5)], upper := (rows 37 74 196 265 19 48 96 130 386), lower := (rows 37 74 196 265 19 48 96 128 256), losses := [] }

theorem u7446 : Upper (D 7) (R 7) [36,72,192,257,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7446 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7447 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 265 19 48 192 162 290), lower := (rows 37 74 196 265 19 48 192 128 256), losses := [] }

theorem u7447 : Upper (D 7) (R 7) [36,72,192,257,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7447 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7448 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 196 265 145 34 66 176 304), lower := (rows 37 74 196 265 145 34 66 128 256), losses := [] }

theorem u7448 : Upper (D 7) (R 7) [36,72,192,257,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7449 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 265 145 34 80 162 290), lower := (rows 37 74 196 265 145 34 80 128 256), losses := [] }

theorem u7449 : Upper (D 7) (R 7) [36,72,192,257,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7449 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7450 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 98, targets := 129 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 37 74 196 265 145 34 96 146 274), lower := (rows 37 74 196 265 145 34 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 42 107 128 256), good := (rows 100 106 196 362 212 98 96 128 256) }] }

theorem u7450 : Upper (D 7) (R 7) [36,72,192,257,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7451 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 180, targets := 1 },{ cop := 1, region := 176, targets := 64 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(4,0),(4,6)], upper := (rows 37 74 196 265 146 34 65 176 304), lower := (rows 37 74 196 265 146 34 65 128 256), losses := [] }

theorem u7451 : Upper (D 7) (R 7) [36,72,192,257,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7452 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 265 146 34 80 161 289), lower := (rows 37 74 196 265 146 34 80 128 256), losses := [] }

theorem u7452 : Upper (D 7) (R 7) [36,72,192,257,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7452 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7453 : Route 9 := (fun mask => (mask,id))

def c7453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7453 : Upper (D 7) (R 7) [36,72,192,257,130,2,32] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257,130,2,32] 13 (by decide) (choices 1) [1,16] r7453 c7453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u554
  · exact u555

def b7454 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 1, region := 180, targets := 1 }], pairs := [(1,7),(2,0),(3,7)], upper := (rows 37 74 196 265 146 48 65 162 290), lower := (rows 37 74 196 265 146 48 65 128 256), losses := [] }

theorem u7454 : Upper (D 7) (R 7) [36,72,192,257,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7454 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7455 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 196 265 146 48 66 161 289), lower := (rows 37 74 196 265 146 48 66 128 256), losses := [] }

theorem u7455 : Upper (D 7) (R 7) [36,72,192,257,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7455 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7456 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 74 196 265 146 48 96 131 259), lower := (rows 37 74 196 265 146 48 96 128 256), losses := [] }

theorem u7456 : Upper (D 7) (R 7) [36,72,192,257,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7456 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7457 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 180, targets := 1 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(2,0),(2,1),(4,0)], upper := (rows 37 74 196 265 176 34 65 146 274), lower := (rows 37 74 196 265 176 34 65 128 256), losses := [] }

theorem u7457 : Upper (D 7) (R 7) [36,72,192,257,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7458 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 196 265 176 34 66 145 273), lower := (rows 37 74 196 265 176 34 66 128 256), losses := [] }

theorem u7458 : Upper (D 7) (R 7) [36,72,192,257,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7459 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 265 176 34 80 131 259), lower := (rows 37 74 196 265 176 34 80 128 256), losses := [] }

theorem u7459 : Upper (D 7) (R 7) [36,72,192,257,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7459 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7460 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 392, targets := 97 },{ cop := 1, region := 132, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,6)], upper := (rows 37 74 196 280 50 33 65 130 386), lower := (rows 37 74 196 280 50 33 65 128 256), losses := [] }

theorem u7460 : Upper (D 7) (R 7) [36,72,192,272,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7461 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 1, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 74 196 280 50 33 66 129 385), lower := (rows 37 74 196 280 50 33 66 128 256), losses := [] }

theorem u7461 : Upper (D 7) (R 7) [36,72,192,272,34,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7462 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 280 50 33 192 131 259), lower := (rows 37 74 196 280 50 33 192 128 256), losses := [] }

theorem u7462 : Upper (D 7) (R 7) [36,72,192,272,34,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7463 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 68, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,5),(3,7)], upper := (rows 37 74 196 280 145 34 65 162 290), lower := (rows 37 74 196 280 145 34 65 128 256), losses := [] }

theorem u7463 : Upper (D 7) (R 7) [36,72,192,272,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7464 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 196 280 145 34 66 161 289), lower := (rows 37 74 196 280 145 34 66 128 256), losses := [] }

theorem u7464 : Upper (D 7) (R 7) [36,72,192,272,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7465 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 129 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 37 74 196 280 145 34 96 131 259), lower := (rows 37 74 196 280 145 34 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 42 107 128 256), good := (rows 100 106 196 382 212 98 96 128 256) }] }

theorem u7465 : Upper (D 7) (R 7) [36,72,192,272,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7466 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 33, targets := 64 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 196 280 146 33 65 162 290), lower := (rows 37 74 196 280 146 33 65 128 256), losses := [] }

theorem u7466 : Upper (D 7) (R 7) [36,72,192,272,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7467 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 1, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 74 196 280 146 33 66 161 289), lower := (rows 37 74 196 280 146 33 66 128 256), losses := [] }

theorem u7467 : Upper (D 7) (R 7) [36,72,192,272,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7468 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 33, targets := 64 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 196 280 146 33 96 131 259), lower := (rows 37 74 196 280 146 33 96 128 256), losses := [] }

theorem u7468 : Upper (D 7) (R 7) [36,72,192,272,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7469 : Route 9 := (fun mask => (mask,id))

def c7469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7469 : Upper (D 7) (R 7) [36,72,192,272,130,2,1] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,130,2,1] 13 (by decide) (choices 1) [1,32] r7469 c7469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u556
  · exact u557

def b7470 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 98, targets := 129 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 74 196 280 146 34 96 129 257), lower := (rows 37 74 196 280 146 34 96 128 256), losses := [] }

theorem u7470 : Upper (D 7) (R 7) [36,72,192,272,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7471 : Route 9 := (fun mask => (mask,id))

def c7471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7471 : Upper (D 7) (R 7) [36,72,192,272,160,2,1] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,160,2,1] 13 (by decide) (choices 1) [1,2] r7471 c7471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u558
  · exact u559

def b7472 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 196 280 176 34 66 129 257), lower := (rows 37 74 196 280 176 34 66 128 256), losses := [] }

theorem u7472 : Upper (D 7) (R 7) [36,72,192,272,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7473 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 424, targets := 65 },{ cop := 4, region := 196, targets := 34 }], pairs := [(2,1),(2,5),(3,0),(3,6)], upper := (rows 37 74 196 296 19 34 65 144 400), lower := (rows 37 74 196 296 19 34 65 128 256), losses := [] }

theorem u7473 : Upper (D 7) (R 7) [36,72,192,288,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7474 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 4, region := 196, targets := 2 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 37 74 196 296 19 34 80 129 385), lower := (rows 37 74 196 296 19 34 80 128 256), losses := [] }

theorem u7474 : Upper (D 7) (R 7) [36,72,192,288,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7474 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7475 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 296 19 34 192 145 273), lower := (rows 37 74 196 296 19 34 192 128 256), losses := [] }

theorem u7475 : Upper (D 7) (R 7) [36,72,192,288,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7476 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 132, targets := 33 },{ cop := 4, region := 424, targets := 1 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 74 196 296 19 48 65 130 386), lower := (rows 37 74 196 296 19 48 65 128 256), losses := [] }

theorem u7476 : Upper (D 7) (R 7) [36,72,192,288,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7476 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7477 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 196 296 19 48 66 129 385), lower := (rows 37 74 196 296 19 48 66 128 256), losses := [] }

theorem u7477 : Upper (D 7) (R 7) [36,72,192,288,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7477 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7478 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 296 19 48 192 131 259), lower := (rows 37 74 196 296 19 48 192 128 256), losses := [] }

theorem u7478 : Upper (D 7) (R 7) [36,72,192,288,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7478 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7479 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 68, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,5),(3,7)], upper := (rows 37 74 196 296 145 34 65 146 274), lower := (rows 37 74 196 296 145 34 65 128 256), losses := [] }

theorem u7479 : Upper (D 7) (R 7) [36,72,192,288,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7480 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 196 296 145 34 66 145 273), lower := (rows 37 74 196 296 145 34 66 128 256), losses := [] }

theorem u7480 : Upper (D 7) (R 7) [36,72,192,288,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7481 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 296 145 34 80 131 259), lower := (rows 37 74 196 296 145 34 80 128 256), losses := [] }

theorem u7481 : Upper (D 7) (R 7) [36,72,192,288,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7481 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7482 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 74 196 296 146 33 65 146 274), lower := (rows 37 74 196 296 146 33 65 128 256), losses := [] }

theorem u7482 : Upper (D 7) (R 7) [36,72,192,288,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7483 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 196 296 146 33 66 145 273), lower := (rows 37 74 196 296 146 33 66 128 256), losses := [] }

theorem u7483 : Upper (D 7) (R 7) [36,72,192,288,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7484 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 296 146 33 80 131 259), lower := (rows 37 74 196 296 146 33 80 128 256), losses := [] }

theorem u7484 : Upper (D 7) (R 7) [36,72,192,288,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7484 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7485 : Route 9 := (fun mask => (mask,id))

def c7485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7485 : Upper (D 7) (R 7) [36,72,192,288,130,2,1] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,130,2,1] 13 (by decide) (choices 1) [1,16] r7485 c7485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u560
  · exact u561

def b7486 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 296 146 34 80 129 257), lower := (rows 37 74 196 296 146 34 80 128 256), losses := [] }

theorem u7486 : Upper (D 7) (R 7) [36,72,192,288,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7486 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7487 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 74 196 296 146 48 65 131 259), lower := (rows 37 74 196 296 146 48 65 128 256), losses := [] }

theorem u7487 : Upper (D 7) (R 7) [36,72,192,288,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7487 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7488 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 196 296 146 48 66 129 257), lower := (rows 37 74 196 296 146 48 66 128 256), losses := [] }

theorem u7488 : Upper (D 7) (R 7) [36,72,192,288,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7488 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7489 : Route 9 := (fun mask => (mask,id))

def c7489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7489 : Upper (D 7) (R 7) [36,72,192,384,3,2,1] 13 := by
  apply FastRouting.sound _ _ [36,72,192,384,3,2,1] 13 (by decide) (choices 1) [16,32] r7489 c7489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u562
  · exact u563

def b7490 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 66 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 37 74 196 392 19 34 80 161 289), lower := (rows 37 74 196 392 19 34 80 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 32 80 129 257), good := (rows 429 72 196 392 477 32 92 128 256) }] }

theorem u7490 : Upper (D 7) (R 7) [36,72,192,384,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7490 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7491 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 102, targets := 1 },{ cop := 4, region := 392, targets := 34 }], pairs := [(1,0),(2,0),(3,1),(3,5)], upper := (rows 37 74 196 392 19 34 96 145 273), lower := (rows 37 74 196 392 19 34 96 128 256), losses := [] }

theorem u7491 : Upper (D 7) (R 7) [36,72,192,384,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7492 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 424, targets := 65 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 37 74 196 392 19 48 65 162 290), lower := (rows 37 74 196 392 19 48 65 128 256), losses := [{ target := 0, region := (rows 0 70 68 121 16 48 64 145 273), good := (rows 430 78 206 392 442 440 462 128 256) }] }

theorem u7492 : Upper (D 7) (R 7) [36,72,192,384,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7492 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7493 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 196 392 19 48 66 161 289), lower := (rows 37 74 196 392 19 48 66 128 256), losses := [] }

theorem u7493 : Upper (D 7) (R 7) [36,72,192,384,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7493 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7494 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 392, targets := 32 },{ cop := 4, region := 392, targets := 64 }], pairs := [(1,5),(3,5),(3,6)], upper := (rows 37 74 196 392 19 48 96 131 259), lower := (rows 37 74 196 392 19 48 96 128 256), losses := [{ target := 5, region := (rows 1 66 4 56 16 0 64 144 272), good := (rows 13 74 198 392 411 408 74 128 256) }] }

theorem u7494 : Upper (D 7) (R 7) [36,72,192,384,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7494 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7495 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 392, targets := 97 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,6)], upper := (rows 37 74 196 392 50 33 65 146 274), lower := (rows 37 74 196 392 50 33 65 128 256), losses := [] }

theorem u7495 : Upper (D 7) (R 7) [36,72,192,384,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7496 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 74 196 392 50 33 66 145 273), lower := (rows 37 74 196 392 50 33 66 128 256), losses := [] }

theorem u7496 : Upper (D 7) (R 7) [36,72,192,384,34,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7497 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 74 196 392 50 33 80 131 259), lower := (rows 37 74 196 392 50 33 80 128 256), losses := [] }

theorem u7497 : Upper (D 7) (R 7) [36,72,192,384,34,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7497 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7498 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 26 208 288 65 130 386), lower := (rows 37 98 13 26 208 288 65 128 256), losses := [] }

theorem u7498 : Upper (D 7) (R 7) [36,96,9,18,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7498 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7499 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 13 26 208 288 66 129 385), lower := (rows 37 98 13 26 208 288 66 128 256), losses := [] }

theorem u7499 : Upper (D 7) (R 7) [36,96,9,18,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7499 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7499
end Delivery.IrregularNine14.P07
