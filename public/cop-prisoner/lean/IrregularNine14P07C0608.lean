import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0368
import IrregularNine14P07C0369

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36480 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 100 152 152 39 71 135 263), lower := (rows 35 322 100 152 152 32 64 128 256), losses := [] }

theorem u36480 : Upper (D 7) (R 7) [34,320,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36481 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 42 21 73 82 418 450 386 386), lower := (rows 37 42 21 73 82 32 64 128 256), losses := [] }

theorem u36481 : Upper (D 7) (R 7) [36,40,17,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36482 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 1, region := 464, targets := 32 }], pairs := [(1,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 73 146 482 450 450 450), lower := (rows 37 42 21 73 146 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 18 0 82 146 274), good := (rows 13 474 477 73 466 0 64 128 256) }] }

theorem u36482 : Upper (D 7) (R 7) [36,40,17,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36483 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 1, region := 464, targets := 32 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 37 42 21 73 208 418 450 386 386), lower := (rows 37 42 21 73 208 32 64 128 256), losses := [] }

theorem u36483 : Upper (D 7) (R 7) [36,40,17,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36484 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 1, region := 464, targets := 32 }], pairs := [(1,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 73 274 226 194 194 450), lower := (rows 37 42 21 73 274 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 18 0 82 146 274), good := (rows 13 474 477 73 466 0 64 128 256) }] }

theorem u36484 : Upper (D 7) (R 7) [36,40,17,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36485 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 1, region := 464, targets := 32 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 37 42 21 73 336 162 194 130 386), lower := (rows 37 42 21 73 336 32 64 128 256), losses := [] }

theorem u36485 : Upper (D 7) (R 7) [36,40,17,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36486 : Route 9 := (fun mask => (mask,id))

def c36486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36486 : Upper (D 7) (R 7) [36,40,17,65,384] 13 := by
  apply FastRouting.sound _ _ [36,40,17,65,384] 13 (by decide) (choices 1) [2,64,128] r36486 c36486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22089
  · exact u22090
  · exact u22091

def b36487 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 21 74 19 480 448 448 448), lower := (rows 37 42 21 74 19 32 64 128 256), losses := [] }

theorem u36487 : Upper (D 7) (R 7) [36,40,17,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36488 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 42 21 74 81 418 450 386 386), lower := (rows 37 42 21 74 81 32 64 128 256), losses := [] }

theorem u36488 : Upper (D 7) (R 7) [36,40,17,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36489 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 37 42 21 74 82 417 449 385 385), lower := (rows 37 42 21 74 82 32 64 128 256), losses := [] }

theorem u36489 : Upper (D 7) (R 7) [36,40,17,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36490 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 42 21 74 145 482 450 450 450), lower := (rows 37 42 21 74 145 32 64 128 256), losses := [] }

theorem u36490 : Upper (D 7) (R 7) [36,40,17,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36491 : Route 9 := (fun mask => (mask,id))

def c36491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u36491 : Upper (D 7) (R 7) [36,40,17,66,130] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,130] 13 (by decide) (choices 1) [1,64,128,256] r36491 c36491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22092
  · exact u22093
  · exact u22094
  · exact u22095

def r36492 : Route 9 := (fun mask => (mask,id))

def c36492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36492 : Upper (D 7) (R 7) [36,40,17,66,192] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,192] 13 (by decide) (choices 1) [1,2,128,256] r36492 c36492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22096
  · exact u22097
  · exact u22098
  · exact u22099

def b36493 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 42 21 74 273 226 194 194 450), lower := (rows 37 42 21 74 273 32 64 128 256), losses := [] }

theorem u36493 : Upper (D 7) (R 7) [36,40,17,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36494 : Route 9 := (fun mask => (mask,id))

def c36494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36494 : Upper (D 7) (R 7) [36,40,17,66,258] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,258] 13 (by decide) (choices 1) [1,64,128] r36494 c36494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22100
  · exact u22101
  · exact u22102

def r36495 : Route 9 := (fun mask => (mask,id))

def c36495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36495 : Upper (D 7) (R 7) [36,40,17,66,320] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,320] 13 (by decide) (choices 1) [1,2,128] r36495 c36495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22103
  · exact u22104
  · exact u22105

def r36496 : Route 9 := (fun mask => (mask,id))

def c36496 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36496 : Upper (D 7) (R 7) [36,40,17,66,384] 13 := by
  apply FastRouting.sound _ _ [36,40,17,66,384] 13 (by decide) (choices 1) [1,2,64,128] r36496 c36496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22106
  · exact u22107
  · exact u22108
  · exact u22109

def b36497 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 21 200 19 482 450 450 450), lower := (rows 37 42 21 200 19 32 64 128 256), losses := [] }

theorem u36497 : Upper (D 7) (R 7) [36,40,17,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36498 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 42 21 200 81 418 450 386 386), lower := (rows 37 42 21 200 81 32 64 128 256), losses := [] }

theorem u36498 : Upper (D 7) (R 7) [36,40,17,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36499 : Route 9 := (fun mask => (mask,id))

def c36499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36499 : Upper (D 7) (R 7) [36,40,17,192,66] 13 := by
  apply FastRouting.sound _ _ [36,40,17,192,66] 13 (by decide) (choices 1) [1,2,128,256] r36499 c36499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22110
  · exact u22111
  · exact u22112
  · exact u22113

def b36500 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 42 21 200 208 291 323 387 259), lower := (rows 37 42 21 200 208 32 64 128 256), losses := [] }

theorem u36500 : Upper (D 7) (R 7) [36,40,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36501 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 42 21 200 273 226 194 194 450), lower := (rows 37 42 21 200 273 32 64 128 256), losses := [] }

theorem u36501 : Upper (D 7) (R 7) [36,40,17,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36502 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c36502 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36502 : Upper (D 7) (R 7) [36,40,17,192,258] 13 := by
  apply FastRouting.sound _ _ [36,40,17,192,258] 13 (by decide) (choices 1) [1,2,64] r36502 c36502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22114
  · exact u22115
  · exact u22116

def r36503 : Route 9 := (fun mask => (mask,id))

def c36503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36503 : Upper (D 7) (R 7) [36,40,17,192,320] 13 := by
  apply FastRouting.sound _ _ [36,40,17,192,320] 13 (by decide) (choices 1) [1,2,128] r36503 c36503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22117
  · exact u22118
  · exact u22119

def b36504 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 21 265 82 226 194 194 450), lower := (rows 37 42 21 265 82 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 18 0 82 146 274), good := (rows 13 474 477 265 466 0 64 128 256) }] }

theorem u36504 : Upper (D 7) (R 7) [36,40,17,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36505 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c36505 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36505 : Upper (D 7) (R 7) [36,40,17,257,192] 13 := by
  apply FastRouting.sound _ _ [36,40,17,257,192] 13 (by decide) (choices 1) [2,64] r36505 c36505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22120
  · exact u22121

def b36506 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 21 266 19 224 192 192 448), lower := (rows 37 42 21 266 19 32 64 128 256), losses := [] }

theorem u36506 : Upper (D 7) (R 7) [36,40,17,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36507 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 42 21 266 81 226 194 194 450), lower := (rows 37 42 21 266 81 32 64 128 256), losses := [] }

theorem u36507 : Upper (D 7) (R 7) [36,40,17,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36508 : Route 9 := (fun mask => (mask,id))

def c36508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36508 : Upper (D 7) (R 7) [36,40,17,258,66] 13 := by
  apply FastRouting.sound _ _ [36,40,17,258,66] 13 (by decide) (choices 1) [1,64,128] r36508 c36508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22122
  · exact u22123
  · exact u22124

def r36509 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c36509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36509 : Upper (D 7) (R 7) [36,40,17,258,192] 13 := by
  apply FastRouting.sound _ _ [36,40,17,258,192] 13 (by decide) (choices 1) [1,2,64] r36509 c36509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22125
  · exact u22126
  · exact u22127

def b36510 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 21 328 19 226 194 194 450), lower := (rows 37 42 21 328 19 32 64 128 256), losses := [] }

theorem u36510 : Upper (D 7) (R 7) [36,40,17,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36511 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 42 21 328 81 162 194 130 386), lower := (rows 37 42 21 328 81 32 64 128 256), losses := [] }

theorem u36511 : Upper (D 7) (R 7) [36,40,17,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36512 : Route 9 := (fun mask => (mask,id))

def c36512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36512 : Upper (D 7) (R 7) [36,40,17,320,66] 13 := by
  apply FastRouting.sound _ _ [36,40,17,320,66] 13 (by decide) (choices 1) [1,2,128] r36512 c36512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22128
  · exact u22129
  · exact u22130

def b36513 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 42 21 328 145 226 194 194 450), lower := (rows 37 42 21 328 145 32 64 128 256), losses := [] }

theorem u36513 : Upper (D 7) (R 7) [36,40,17,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36514 : Route 9 := (fun mask => (mask,id))

def c36514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36514 : Upper (D 7) (R 7) [36,40,17,320,130] 13 := by
  apply FastRouting.sound _ _ [36,40,17,320,130] 13 (by decide) (choices 1) [1,2,64,128] r36514 c36514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22131
  · exact u22132
  · exact u22133
  · exact u22134

def r36515 : Route 9 := (fun mask => (mask,id))

def c36515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36515 : Upper (D 7) (R 7) [36,40,17,320,192] 13 := by
  apply FastRouting.sound _ _ [36,40,17,320,192] 13 (by decide) (choices 1) [1,2,128] r36515 c36515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22135
  · exact u22136
  · exact u22137

def b36516 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 22 73 19 480 448 448 448), lower := (rows 37 42 22 73 19 32 64 128 256), losses := [] }

theorem u36516 : Upper (D 7) (R 7) [36,40,18,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36517 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 37 42 22 73 81 418 450 386 386), lower := (rows 37 42 22 73 81 32 64 128 256), losses := [] }

theorem u36517 : Upper (D 7) (R 7) [36,40,18,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36518 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 161 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 42 22 73 82 417 449 385 385), lower := (rows 37 42 22 73 82 32 64 128 256), losses := [] }

theorem u36518 : Upper (D 7) (R 7) [36,40,18,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36519 : Route 9 := (fun mask => (mask,id))

def c36519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u36519 : Upper (D 7) (R 7) [36,40,18,65,129] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65,129] 13 (by decide) (choices 1) [2,64,128,256] r36519 c36519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22138
  · exact u22139
  · exact u22140
  · exact u22141

def b36520 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 42 22 73 146 481 449 449 449), lower := (rows 37 42 22 73 146 32 64 128 256), losses := [] }

theorem u36520 : Upper (D 7) (R 7) [36,40,18,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36521 : Route 9 := (fun mask => (mask,id))

def c36521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36521 : Upper (D 7) (R 7) [36,40,18,65,192] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65,192] 13 (by decide) (choices 1) [1,2,128,256] r36521 c36521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22142
  · exact u22143
  · exact u22144
  · exact u22145

def r36522 : Route 9 := (fun mask => (mask,id))

def c36522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36522 : Upper (D 7) (R 7) [36,40,18,65,257] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65,257] 13 (by decide) (choices 1) [2,64,128] r36522 c36522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22146
  · exact u22147
  · exact u22148

def b36523 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 42 22 73 274 225 193 193 449), lower := (rows 37 42 22 73 274 32 64 128 256), losses := [] }

theorem u36523 : Upper (D 7) (R 7) [36,40,18,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36524 : Route 9 := (fun mask => (mask,id))

def c36524 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36524 : Upper (D 7) (R 7) [36,40,18,65,320] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65,320] 13 (by decide) (choices 1) [1,2,128] r36524 c36524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22149
  · exact u22150
  · exact u22151

def r36525 : Route 9 := (fun mask => (mask,id))

def c36525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36525 : Upper (D 7) (R 7) [36,40,18,65,384] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65,384] 13 (by decide) (choices 1) [1,2,64,128] r36525 c36525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22152
  · exact u22153
  · exact u22154
  · exact u22155

def b36526 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 2, region := 417, targets := 64 }], pairs := [(0,1),(0,6),(4,1),(4,5)], upper := (rows 37 42 22 74 81 417 449 385 385), lower := (rows 37 42 22 74 81 32 64 128 256), losses := [] }

theorem u36526 : Upper (D 7) (R 7) [36,40,18,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36527 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 74 145 481 449 449 449), lower := (rows 37 42 22 74 145 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 17 0 81 145 273), good := (rows 477 10 478 74 465 0 64 128 256) }] }

theorem u36527 : Upper (D 7) (R 7) [36,40,18,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36528 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 2, region := 417, targets := 64 }], pairs := [(0,1),(0,6),(4,1),(4,5)], upper := (rows 37 42 22 74 208 417 449 385 385), lower := (rows 37 42 22 74 208 32 64 128 256), losses := [] }

theorem u36528 : Upper (D 7) (R 7) [36,40,18,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36529 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 74 273 225 193 193 449), lower := (rows 37 42 22 74 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 17 0 81 145 273), good := (rows 477 10 478 74 465 0 64 128 256) }] }

theorem u36529 : Upper (D 7) (R 7) [36,40,18,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36530 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(4,1),(4,5)], upper := (rows 37 42 22 74 336 161 193 129 385), lower := (rows 37 42 22 74 336 32 64 128 256), losses := [] }

theorem u36530 : Upper (D 7) (R 7) [36,40,18,66,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36531 : Route 9 := (fun mask => (mask,id))

def c36531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36531 : Upper (D 7) (R 7) [36,40,18,66,384] 13 := by
  apply FastRouting.sound _ _ [36,40,18,66,384] 13 (by decide) (choices 1) [1,64,128] r36531 c36531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22156
  · exact u22157
  · exact u22158

def b36532 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 22 200 19 481 449 449 449), lower := (rows 37 42 22 200 19 32 64 128 256), losses := [] }

theorem u36532 : Upper (D 7) (R 7) [36,40,18,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36533 : Route 9 := (fun mask => (mask,id))

def c36533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36533 : Upper (D 7) (R 7) [36,40,18,192,65] 13 := by
  apply FastRouting.sound _ _ [36,40,18,192,65] 13 (by decide) (choices 1) [1,2,128,256] r36533 c36533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22159
  · exact u22160
  · exact u22161
  · exact u22162

def b36534 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 161 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 42 22 200 82 417 449 385 385), lower := (rows 37 42 22 200 82 32 64 128 256), losses := [] }

theorem u36534 : Upper (D 7) (R 7) [36,40,18,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36535 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 42 22 200 208 291 323 387 259), lower := (rows 37 42 22 200 208 32 64 128 256), losses := [] }

theorem u36535 : Upper (D 7) (R 7) [36,40,18,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36536 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c36536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36536 : Upper (D 7) (R 7) [36,40,18,192,257] 13 := by
  apply FastRouting.sound _ _ [36,40,18,192,257] 13 (by decide) (choices 1) [1,2,64] r36536 c36536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22163
  · exact u22164
  · exact u22165

def b36537 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 42 22 200 274 225 193 193 449), lower := (rows 37 42 22 200 274 32 64 128 256), losses := [] }

theorem u36537 : Upper (D 7) (R 7) [36,40,18,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36538 : Route 9 := (fun mask => (mask,id))

def c36538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36538 : Upper (D 7) (R 7) [36,40,18,192,320] 13 := by
  apply FastRouting.sound _ _ [36,40,18,192,320] 13 (by decide) (choices 1) [1,2,128] r36538 c36538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22166
  · exact u22167
  · exact u22168

def b36539 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 42 22 265 19 224 192 192 448), lower := (rows 37 42 22 265 19 32 64 128 256), losses := [] }

theorem u36539 : Upper (D 7) (R 7) [36,40,18,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36539
end Delivery.IrregularNine14.P07
