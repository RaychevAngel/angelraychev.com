import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0301
import IrregularNine14P06C0302

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34440 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 386 37 25 82 100 100 228 356), lower := (rows 11 386 37 25 82 32 64 128 256), losses := [] }

theorem u34440 : Upper (D 6) (R 6) [10,384,33,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34441 : Route 9 := (fun mask => (mask,id))

def c34441 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34441 : Upper (D 6) (R 6) [10,384,33,17,68] 13 := by
  apply FastRouting.sound _ _ [10,384,33,17,68] 13 (by decide) (choices 1) [2,4,64] r34441 c34441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18069
  · exact u18070
  · exact u18071

def b34442 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 386 37 25 112 102 70 198 326), lower := (rows 11 386 37 25 112 32 64 128 256), losses := [] }

theorem u34442 : Upper (D 6) (R 6) [10,384,33,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34443 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 37 28 19 100 100 228 356), lower := (rows 11 386 37 28 19 32 64 128 256), losses := [] }

theorem u34443 : Upper (D 6) (R 6) [10,384,33,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34444 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 386 37 28 21 98 98 226 354), lower := (rows 11 386 37 28 21 32 64 128 256), losses := [] }

theorem u34444 : Upper (D 6) (R 6) [10,384,33,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34445 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 37 28 22 97 97 225 353), lower := (rows 11 386 37 28 22 32 64 128 256), losses := [] }

theorem u34445 : Upper (D 6) (R 6) [10,384,33,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34446 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 11 386 37 28 49 102 70 198 326), lower := (rows 11 386 37 28 49 32 64 128 256), losses := [] }

theorem u34446 : Upper (D 6) (R 6) [10,384,33,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34447 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 386 37 28 50 101 69 197 325), lower := (rows 11 386 37 28 50 32 64 128 256), losses := [] }

theorem u34447 : Upper (D 6) (R 6) [10,384,33,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34448 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 386 37 28 52 99 67 195 323), lower := (rows 11 386 37 28 52 32 64 128 256), losses := [] }

theorem u34448 : Upper (D 6) (R 6) [10,384,33,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34449 : Route 9 := (fun mask => (mask,id))

def c34449 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34449 : Upper (D 6) (R 6) [10,384,33,20,65] 13 := by
  apply FastRouting.sound _ _ [10,384,33,20,65] 13 (by decide) (choices 1) [2,4,64] r34449 c34449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18072
  · exact u18073
  · exact u18074

def r34450 : Route 9 := (fun mask => (mask,id))

def c34450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34450 : Upper (D 6) (R 6) [10,384,33,20,66] 13 := by
  apply FastRouting.sound _ _ [10,384,33,20,66] 13 (by decide) (choices 1) [1,4,64] r34450 c34450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18075
  · exact u18076
  · exact u18077

def b34451 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 386 37 28 84 99 99 227 355), lower := (rows 11 386 37 28 84 32 64 128 256), losses := [] }

theorem u34451 : Upper (D 6) (R 6) [10,384,33,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34452 : Route 9 := (fun mask => (mask,id))

def c34452 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34452 : Upper (D 6) (R 6) [10,384,33,20,96] 13 := by
  apply FastRouting.sound _ _ [10,384,33,20,96] 13 (by decide) (choices 1) [1,2,4,64] r34452 c34452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18078
  · exact u18079
  · exact u18080
  · exact u18081

def b34453 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 37 56 19 100 68 196 324), lower := (rows 11 386 37 56 19 32 64 128 256), losses := [] }

theorem u34453 : Upper (D 6) (R 6) [10,384,33,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34454 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 11 386 37 56 21 102 70 198 326), lower := (rows 11 386 37 56 21 32 64 128 256), losses := [] }

theorem u34454 : Upper (D 6) (R 6) [10,384,33,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34455 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 386 37 56 22 101 69 197 325), lower := (rows 11 386 37 56 22 32 64 128 256), losses := [] }

theorem u34455 : Upper (D 6) (R 6) [10,384,33,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34456 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 11 386 37 56 81 102 70 198 326), lower := (rows 11 386 37 56 81 32 64 128 256), losses := [] }

theorem u34456 : Upper (D 6) (R 6) [10,384,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34457 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 386 37 56 82 101 69 197 325), lower := (rows 11 386 37 56 82 32 64 128 256), losses := [] }

theorem u34457 : Upper (D 6) (R 6) [10,384,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34458 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 386 37 56 84 103 71 199 327), lower := (rows 11 386 37 56 84 32 64 128 256), losses := [{ target := 5, region := (rows 9 22 4 8 20 0 68 132 260), good := (rows 11 386 471 27 470 0 64 128 256) }] }

theorem u34458 : Upper (D 6) (R 6) [10,384,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34459 : Route 9 := (fun mask => (mask,id))

def c34459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34459 : Upper (D 6) (R 6) [10,384,33,65,6] 13 := by
  apply FastRouting.sound _ _ [10,384,33,65,6] 13 (by decide) (choices 1) [4,16,64] r34459 c34459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18082
  · exact u18083
  · exact u18084

def r34460 : Route 9 := (fun mask => (mask,id))

def c34460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34460 : Upper (D 6) (R 6) [10,384,33,65,34] 13 := by
  apply FastRouting.sound _ _ [10,384,33,65,34] 13 (by decide) (choices 1) [4,16,64] r34460 c34460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18085
  · exact u18086
  · exact u18087

def b34461 : PairBound 9 := { available := 86, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 386 37 73 52 118 86 214 342), lower := (rows 11 386 37 73 52 32 64 128 256), losses := [] }

theorem u34461 : Upper (D 6) (R 6) [10,384,33,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34462 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 386 37 73 82 52 116 180 308), lower := (rows 11 386 37 73 82 32 64 128 256), losses := [] }

theorem u34462 : Upper (D 6) (R 6) [10,384,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34463 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 386 37 73 84 54 118 182 310), lower := (rows 11 386 37 73 84 32 64 128 256), losses := [] }

theorem u34463 : Upper (D 6) (R 6) [10,384,33,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34464 : Route 9 := (fun mask => (mask,id))

def c34464 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34464 : Upper (D 6) (R 6) [10,384,33,65,96] 13 := by
  apply FastRouting.sound _ _ [10,384,33,65,96] 13 (by decide) (choices 1) [2,4,16] r34464 c34464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18088
  · exact u18089
  · exact u18090

def b34465 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 37 76 19 116 116 244 372), lower := (rows 11 386 37 76 19 32 64 128 256), losses := [] }

theorem u34465 : Upper (D 6) (R 6) [10,384,33,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34466 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 386 37 76 21 114 114 242 370), lower := (rows 11 386 37 76 21 32 64 128 256), losses := [] }

theorem u34466 : Upper (D 6) (R 6) [10,384,33,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34467 : Route 9 := (fun mask => (mask,id))

def c34467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34467 : Upper (D 6) (R 6) [10,384,33,68,6] 13 := by
  apply FastRouting.sound _ _ [10,384,33,68,6] 13 (by decide) (choices 1) [1,16,64] r34467 c34467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18091
  · exact u18092
  · exact u18093

def b34468 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 386 37 76 49 118 86 214 342), lower := (rows 11 386 37 76 49 32 64 128 256), losses := [] }

theorem u34468 : Upper (D 6) (R 6) [10,384,33,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34469 : Route 9 := (fun mask => (mask,id))

def c34469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34469 : Upper (D 6) (R 6) [10,384,33,68,34] 13 := by
  apply FastRouting.sound _ _ [10,384,33,68,34] 13 (by decide) (choices 1) [1,4,16,64] r34469 c34469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18094
  · exact u18095
  · exact u18096
  · exact u18097

def b34470 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 386 37 76 52 115 83 211 339), lower := (rows 11 386 37 76 52 32 64 128 256), losses := [] }

theorem u34470 : Upper (D 6) (R 6) [10,384,33,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34471 : Route 9 := (fun mask => (mask,id))

def c34471 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34471 : Upper (D 6) (R 6) [10,384,33,68,65] 13 := by
  apply FastRouting.sound _ _ [10,384,33,68,65] 13 (by decide) (choices 1) [2,4,16] r34471 c34471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18098
  · exact u18099
  · exact u18100

def r34472 : Route 9 := (fun mask => (mask,id))

def c34472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34472 : Upper (D 6) (R 6) [10,384,33,68,66] 13 := by
  apply FastRouting.sound _ _ [10,384,33,68,66] 13 (by decide) (choices 1) [1,4,16] r34472 c34472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18101
  · exact u18102
  · exact u18103

def b34473 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 386 37 76 84 51 115 179 307), lower := (rows 11 386 37 76 84 32 64 128 256), losses := [] }

theorem u34473 : Upper (D 6) (R 6) [10,384,33,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34474 : Route 9 := (fun mask => (mask,id))

def c34474 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34474 : Upper (D 6) (R 6) [10,384,33,68,96] 13 := by
  apply FastRouting.sound _ _ [10,384,33,68,96] 13 (by decide) (choices 1) [1,2,4,16] r34474 c34474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18104
  · exact u18105
  · exact u18106
  · exact u18107

def b34475 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 37 88 19 100 100 228 356), lower := (rows 11 386 37 88 19 32 64 128 256), losses := [] }

theorem u34475 : Upper (D 6) (R 6) [10,384,33,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34476 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 386 37 88 21 102 102 230 358), lower := (rows 11 386 37 88 21 32 64 128 256), losses := [] }

theorem u34476 : Upper (D 6) (R 6) [10,384,33,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34477 : Route 9 := (fun mask => (mask,id))

def c34477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34477 : Upper (D 6) (R 6) [10,384,33,80,6] 13 := by
  apply FastRouting.sound _ _ [10,384,33,80,6] 13 (by decide) (choices 1) [1,4,64] r34477 c34477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18108
  · exact u18109
  · exact u18110

def b34478 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 386 37 88 49 102 70 198 326), lower := (rows 11 386 37 88 49 32 64 128 256), losses := [] }

theorem u34478 : Upper (D 6) (R 6) [10,384,33,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34479 : Route 9 := (fun mask => (mask,id))

def c34479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34479 : Upper (D 6) (R 6) [10,384,33,80,34] 13 := by
  apply FastRouting.sound _ _ [10,384,33,80,34] 13 (by decide) (choices 1) [1,4,64] r34479 c34479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18111
  · exact u18112
  · exact u18113

def b34480 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 386 37 88 52 103 71 199 327), lower := (rows 11 386 37 88 52 32 64 128 256), losses := [] }

theorem u34480 : Upper (D 6) (R 6) [10,384,33,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34481 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 386 37 88 81 38 102 166 294), lower := (rows 11 386 37 88 81 32 64 128 256), losses := [] }

theorem u34481 : Upper (D 6) (R 6) [10,384,33,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34482 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 386 37 88 82 37 101 165 293), lower := (rows 11 386 37 88 82 32 64 128 256), losses := [] }

theorem u34482 : Upper (D 6) (R 6) [10,384,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34483 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 386 37 88 84 39 103 167 295), lower := (rows 11 386 37 88 84 32 64 128 256), losses := [] }

theorem u34483 : Upper (D 6) (R 6) [10,384,33,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34484 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 386 37 88 112 39 71 135 263), lower := (rows 11 386 37 88 112 32 64 128 256), losses := [] }

theorem u34484 : Upper (D 6) (R 6) [10,384,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34485 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 386 37 104 19 116 84 212 340), lower := (rows 11 386 37 104 19 32 64 128 256), losses := [] }

theorem u34485 : Upper (D 6) (R 6) [10,384,33,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34486 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 11 386 37 104 21 118 86 214 342), lower := (rows 11 386 37 104 21 32 64 128 256), losses := [] }

theorem u34486 : Upper (D 6) (R 6) [10,384,33,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34487 : Route 9 := (fun mask => (mask,id))

def c34487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34487 : Upper (D 6) (R 6) [10,384,33,96,6] 13 := by
  apply FastRouting.sound _ _ [10,384,33,96,6] 13 (by decide) (choices 1) [1,4,16,64] r34487 c34487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18114
  · exact u18115
  · exact u18116
  · exact u18117

def b34488 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 386 37 104 81 54 86 150 278), lower := (rows 11 386 37 104 81 32 64 128 256), losses := [] }

theorem u34488 : Upper (D 6) (R 6) [10,384,33,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34489 : Route 9 := (fun mask => (mask,id))

def c34489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34489 : Upper (D 6) (R 6) [10,384,33,96,66] 13 := by
  apply FastRouting.sound _ _ [10,384,33,96,66] 13 (by decide) (choices 1) [1,4,16] r34489 c34489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18118
  · exact u18119
  · exact u18120

def r34490 : Route 9 := (fun mask => (mask,id))

def c34490 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34490 : Upper (D 6) (R 6) [10,384,33,96,68] 13 := by
  apply FastRouting.sound _ _ [10,384,33,96,68] 13 (by decide) (choices 1) [1,2,4,16] r34490 c34490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18121
  · exact u18122
  · exact u18123
  · exact u18124

def b34491 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 38 25 21 100 100 228 356), lower := (rows 11 386 38 25 21 32 64 128 256), losses := [] }

theorem u34491 : Upper (D 6) (R 6) [10,384,34,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34492 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 386 38 25 49 100 68 196 324), lower := (rows 11 386 38 25 49 32 64 128 256), losses := [] }

theorem u34492 : Upper (D 6) (R 6) [10,384,34,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34493 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 386 38 25 52 101 69 197 325), lower := (rows 11 386 38 25 52 32 64 128 256), losses := [] }

theorem u34493 : Upper (D 6) (R 6) [10,384,34,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34494 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 386 38 25 81 100 100 228 356), lower := (rows 11 386 38 25 81 32 64 128 256), losses := [] }

theorem u34494 : Upper (D 6) (R 6) [10,384,34,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34495 : Route 9 := (fun mask => (mask,id))

def c34495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34495 : Upper (D 6) (R 6) [10,384,34,17,68] 13 := by
  apply FastRouting.sound _ _ [10,384,34,17,68] 13 (by decide) (choices 1) [1,4,64] r34495 c34495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18125
  · exact u18126
  · exact u18127

def r34496 : Route 9 := (fun mask => (mask,id))

def c34496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34496 : Upper (D 6) (R 6) [10,384,34,17,96] 13 := by
  apply FastRouting.sound _ _ [10,384,34,17,96] 13 (by decide) (choices 1) [1,4,64] r34496 c34496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18128
  · exact u18129
  · exact u18130

def b34497 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 386 38 28 21 97 97 225 353), lower := (rows 11 386 38 28 21 32 64 128 256), losses := [] }

theorem u34497 : Upper (D 6) (R 6) [10,384,34,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34498 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 386 38 28 49 101 69 197 325), lower := (rows 11 386 38 28 49 32 64 128 256), losses := [] }

theorem u34498 : Upper (D 6) (R 6) [10,384,34,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34499 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 386 38 28 52 97 65 193 321), lower := (rows 11 386 38 28 52 32 64 128 256), losses := [] }

theorem u34499 : Upper (D 6) (R 6) [10,384,34,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34499
end Delivery.IrregularNine14.P06
