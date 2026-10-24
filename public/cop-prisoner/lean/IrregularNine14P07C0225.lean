import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0032
import IrregularNine14P07C0033

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13500 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 261 200 81 160 114 178 306), lower := (rows 7 42 261 200 81 160 64 128 256), losses := [] }

theorem u13500 : Upper (D 7) (R 7) [6,40,257,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13501 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 7 42 261 200 82 33 240 176 432), lower := (rows 7 42 261 200 82 33 64 128 256), losses := [] }

theorem u13501 : Upper (D 7) (R 7) [6,40,257,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13502 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 42 261 200 82 48 225 161 417), lower := (rows 7 42 261 200 82 48 64 128 256), losses := [] }

theorem u13502 : Upper (D 7) (R 7) [6,40,257,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13502 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13503 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 261 200 82 160 113 177 305), lower := (rows 7 42 261 200 82 160 64 128 256), losses := [] }

theorem u13503 : Upper (D 7) (R 7) [6,40,257,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13504 : Route 9 := (fun mask => (mask,id))

def c13504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13504 : Upper (D 7) (R 7) [6,40,257,192,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192,96,1] 13 (by decide) (choices 1) [2,16,128] r13504 c13504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1952
  · exact u1953
  · exact u1954

def b13505 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 42 261 200 112 34 209 145 401), lower := (rows 7 42 261 200 112 34 64 128 256), losses := [] }

theorem u13505 : Upper (D 7) (R 7) [6,40,257,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13506 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 42 261 200 112 48 195 131 387), lower := (rows 7 42 261 200 112 48 64 128 256), losses := [] }

theorem u13506 : Upper (D 7) (R 7) [6,40,257,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13506 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13507 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 261 200 112 160 83 147 275), lower := (rows 7 42 261 200 112 160 64 128 256), losses := [] }

theorem u13507 : Upper (D 7) (R 7) [6,40,257,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13508 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 50, targets := 128 }], pairs := [(1,7),(2,0),(4,0),(4,7)], upper := (rows 7 42 276 73 112 33 194 130 386), lower := (rows 7 42 276 73 112 33 64 128 256), losses := [] }

theorem u13508 : Upper (D 7) (R 7) [6,40,272,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13509 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 42 276 73 112 34 193 129 385), lower := (rows 7 42 276 73 112 34 64 128 256), losses := [] }

theorem u13509 : Upper (D 7) (R 7) [6,40,272,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13510 : Route 9 := (fun mask => (mask,id))

def c13510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13510 : Upper (D 7) (R 7) [6,40,272,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,96,128] 13 (by decide) (choices 1) [1,2,128] r13510 c13510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1955
  · exact u1956
  · exact u1957

def b13511 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 7 42 276 73 145 34 224 224 480), lower := (rows 7 42 276 73 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 123 187 315), good := (rows 486 490 468 490 500 482 64 128 256) }] }

theorem u13511 : Upper (D 7) (R 7) [6,40,272,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13512 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 276 73 145 96 226 162 418), lower := (rows 7 42 276 73 145 96 64 128 256), losses := [] }

theorem u13512 : Upper (D 7) (R 7) [6,40,272,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13513 : Route 9 := (fun mask => (mask,id))

def c13513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13513 : Upper (D 7) (R 7) [6,40,272,65,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,129,128] 13 (by decide) (choices 1) [2,32] r13513 c13513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1958
  · exact u1959

def b13514 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 276 73 146 33 224 224 480), lower := (rows 7 42 276 73 146 33 64 128 256), losses := [] }

theorem u13514 : Upper (D 7) (R 7) [6,40,272,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13515 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 276 73 146 96 225 161 417), lower := (rows 7 42 276 73 146 96 64 128 256), losses := [] }

theorem u13515 : Upper (D 7) (R 7) [6,40,272,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13516 : Route 9 := (fun mask => (mask,id))

def c13516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13516 : Upper (D 7) (R 7) [6,40,272,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,130,128] 13 (by decide) (choices 1) [1,32] r13516 c13516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1960
  · exact u1961

def b13517 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 276 73 176 33 194 194 450), lower := (rows 7 42 276 73 176 33 64 128 256), losses := [] }

theorem u13517 : Upper (D 7) (R 7) [6,40,272,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13518 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 42 276 73 176 34 193 193 449), lower := (rows 7 42 276 73 176 34 64 128 256), losses := [] }

theorem u13518 : Upper (D 7) (R 7) [6,40,272,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13519 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 276 73 176 96 195 131 387), lower := (rows 7 42 276 73 176 96 64 128 256), losses := [] }

theorem u13519 : Upper (D 7) (R 7) [6,40,272,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13520 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 276 73 176 160 67 195 323), lower := (rows 7 42 276 73 176 160 64 128 256), losses := [] }

theorem u13520 : Upper (D 7) (R 7) [6,40,272,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13521 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 276 73 208 33 226 162 418), lower := (rows 7 42 276 73 208 33 64 128 256), losses := [] }

theorem u13521 : Upper (D 7) (R 7) [6,40,272,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13522 : Route 9 := (fun mask => (mask,id))

def c13522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13522 : Upper (D 7) (R 7) [6,40,272,65,192,2] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,192,2] 13 (by decide) (choices 1) [1,32,128] r13522 c13522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1962
  · exact u1963
  · exact u1964

def r13523 : Route 9 := (fun mask => (mask,id))

def c13523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13523 : Upper (D 7) (R 7) [6,40,272,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,192,128] 13 (by decide) (choices 1) [1,2,32] r13523 c13523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1965
  · exact u1966
  · exact u1967

def b13524 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 42, targets := 128 }], pairs := [(1,7),(2,1),(3,7),(4,1)], upper := (rows 7 42 276 74 81 33 224 160 416), lower := (rows 7 42 276 74 81 33 64 128 256), losses := [] }

theorem u13524 : Upper (D 7) (R 7) [6,40,272,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13525 : Route 9 := (fun mask => (mask,id))

def c13525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13525 : Upper (D 7) (R 7) [6,40,272,66,65,128] 13 := by
  apply FastRouting.sound _ _ [6,40,272,66,65,128] 13 (by decide) (choices 1) [1,32,128] r13525 c13525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1968
  · exact u1969
  · exact u1970

def b13526 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 276 74 145 33 224 224 480), lower := (rows 7 42 276 74 145 33 64 128 256), losses := [] }

theorem u13526 : Upper (D 7) (R 7) [6,40,272,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13527 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 276 74 145 96 225 161 417), lower := (rows 7 42 276 74 145 96 64 128 256), losses := [] }

theorem u13527 : Upper (D 7) (R 7) [6,40,272,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13528 : Route 9 := (fun mask => (mask,id))

def c13528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13528 : Upper (D 7) (R 7) [6,40,272,66,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,272,66,129,128] 13 (by decide) (choices 1) [1,32] r13528 c13528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1971
  · exact u1972

def b13529 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(2,5),(3,5),(4,1)], upper := (rows 7 42 276 74 176 33 193 193 449), lower := (rows 7 42 276 74 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 11 16 0 97 161 289), good := (rows 463 458 276 74 468 457 64 128 256) }] }

theorem u13529 : Upper (D 7) (R 7) [6,40,272,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13530 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 276 74 176 96 193 129 385), lower := (rows 7 42 276 74 176 96 64 128 256), losses := [] }

theorem u13530 : Upper (D 7) (R 7) [6,40,272,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13531 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 276 74 176 160 65 193 321), lower := (rows 7 42 276 74 176 160 64 128 256), losses := [] }

theorem u13531 : Upper (D 7) (R 7) [6,40,272,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13532 : Route 9 := (fun mask => (mask,id))

def c13532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13532 : Upper (D 7) (R 7) [6,40,272,66,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,272,66,192,1] 13 (by decide) (choices 1) [1,32,128] r13532 c13532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1973
  · exact u1974
  · exact u1975

def b13533 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 276 74 208 160 97 161 289), lower := (rows 7 42 276 74 208 160 64 128 256), losses := [] }

theorem u13533 : Upper (D 7) (R 7) [6,40,272,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13534 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 7 42 276 200 49 33 194 194 450), lower := (rows 7 42 276 200 49 33 64 128 256), losses := [] }

theorem u13534 : Upper (D 7) (R 7) [6,40,272,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13535 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 42 276 200 49 34 193 193 449), lower := (rows 7 42 276 200 49 34 64 128 256), losses := [] }

theorem u13535 : Upper (D 7) (R 7) [6,40,272,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13536 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 276 200 49 96 195 131 387), lower := (rows 7 42 276 200 49 96 64 128 256), losses := [] }

theorem u13536 : Upper (D 7) (R 7) [6,40,272,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13537 : Route 9 := (fun mask => (mask,id))

def c13537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13537 : Upper (D 7) (R 7) [6,40,272,192,65,1] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,65,1] 13 (by decide) (choices 1) [2,32,128] r13537 c13537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1976
  · exact u1977
  · exact u1978

def b13538 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,6)], upper := (rows 7 42 276 200 81 34 225 161 417), lower := (rows 7 42 276 200 81 34 64 128 256), losses := [{ target := 6, region := (rows 1 10 20 8 16 43 0 145 273), good := (rows 423 42 404 170 437 34 0 128 256) }] }

theorem u13538 : Upper (D 7) (R 7) [6,40,272,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13539 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 276 200 81 160 99 163 291), lower := (rows 7 42 276 200 81 160 64 128 256), losses := [] }

theorem u13539 : Upper (D 7) (R 7) [6,40,272,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13540 : Route 9 := (fun mask => (mask,id))

def c13540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13540 : Upper (D 7) (R 7) [6,40,272,192,66,1] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,66,1] 13 (by decide) (choices 1) [1,32,128] r13540 c13540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1979
  · exact u1980
  · exact u1981

def b13541 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 276 200 82 160 97 161 289), lower := (rows 7 42 276 200 82 160 64 128 256), losses := [] }

theorem u13541 : Upper (D 7) (R 7) [6,40,272,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13542 : Route 9 := (fun mask => (mask,id))

def c13542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13542 : Upper (D 7) (R 7) [6,40,272,192,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,96,1] 13 (by decide) (choices 1) [1,2,128] r13542 c13542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1982
  · exact u1983
  · exact u1984

def b13543 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 42 276 200 112 34 193 129 385), lower := (rows 7 42 276 200 112 34 64 128 256), losses := [] }

theorem u13543 : Upper (D 7) (R 7) [6,40,272,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13544 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 276 200 112 160 67 131 259), lower := (rows 7 42 276 200 112 160 64 128 256), losses := [] }

theorem u13544 : Upper (D 7) (R 7) [6,40,272,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13545 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 292 25 82 33 192 192 448), lower := (rows 7 42 292 25 82 33 64 128 256), losses := [] }

theorem u13545 : Upper (D 7) (R 7) [6,40,288,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13546 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 42 292 25 82 96 193 129 385), lower := (rows 7 42 292 25 82 96 64 128 256), losses := [] }

theorem u13546 : Upper (D 7) (R 7) [6,40,288,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13547 : Route 9 := (fun mask => (mask,id))

def c13547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13547 : Upper (D 7) (R 7) [6,40,288,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,40,288,17,66,128] 13 (by decide) (choices 1) [1,128] r13547 c13547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1985
  · exact u1986

def b13548 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 292 25 208 33 194 194 450), lower := (rows 7 42 292 25 208 33 64 128 256), losses := [] }

theorem u13548 : Upper (D 7) (R 7) [6,40,288,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13549 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 292 25 208 34 193 193 449), lower := (rows 7 42 292 25 208 34 64 128 256), losses := [] }

theorem u13549 : Upper (D 7) (R 7) [6,40,288,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13550 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 42 292 25 208 96 195 131 387), lower := (rows 7 42 292 25 208 96 64 128 256), losses := [] }

theorem u13550 : Upper (D 7) (R 7) [6,40,288,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13551 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 292 73 145 34 208 208 464), lower := (rows 7 42 292 73 145 34 64 128 256), losses := [] }

theorem u13551 : Upper (D 7) (R 7) [6,40,288,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13552 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 292 73 145 48 194 194 450), lower := (rows 7 42 292 73 145 48 64 128 256), losses := [] }

theorem u13552 : Upper (D 7) (R 7) [6,40,288,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13552 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13553 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 292 73 145 96 210 146 402), lower := (rows 7 42 292 73 145 96 64 128 256), losses := [] }

theorem u13553 : Upper (D 7) (R 7) [6,40,288,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13554 : Route 9 := (fun mask => (mask,id))

def c13554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13554 : Upper (D 7) (R 7) [6,40,288,65,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,129,128] 13 (by decide) (choices 1) [2,16] r13554 c13554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1987
  · exact u1988

def b13555 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 292 73 146 33 208 208 464), lower := (rows 7 42 292 73 146 33 64 128 256), losses := [] }

theorem u13555 : Upper (D 7) (R 7) [6,40,288,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13556 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 42 292 73 146 48 193 193 449), lower := (rows 7 42 292 73 146 48 64 128 256), losses := [] }

theorem u13556 : Upper (D 7) (R 7) [6,40,288,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13556 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13557 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 292 73 146 96 209 145 401), lower := (rows 7 42 292 73 146 96 64 128 256), losses := [] }

theorem u13557 : Upper (D 7) (R 7) [6,40,288,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13558 : Route 9 := (fun mask => (mask,id))

def c13558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13558 : Upper (D 7) (R 7) [6,40,288,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,130,128] 13 (by decide) (choices 1) [1,16] r13558 c13558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1989
  · exact u1990

def b13559 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 292 73 208 33 210 146 402), lower := (rows 7 42 292 73 208 33 64 128 256), losses := [] }

theorem u13559 : Upper (D 7) (R 7) [6,40,288,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13559
end Delivery.IrregularNine14.P07
