import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0178
import IrregularNine14P07C0179

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r28440 : Route 9 := (fun mask => (mask,id))

def c28440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28440 : Upper (D 7) (R 7) [96,257,9,130,160,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,160,2] 13 (by decide) (choices 1) [4,16] r28440 c28440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10708
  · exact u10709

def r28441 : Route 9 := (fun mask => (mask,id))

def c28441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28441 : Upper (D 7) (R 7) [96,257,9,130,160,4] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,160,4] 13 (by decide) (choices 1) [2,16] r28441 c28441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10710
  · exact u10711

def b28442 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 138 176 48 70 198 326), lower := (rows 97 259 13 138 176 48 64 128 256), losses := [] }

theorem u28442 : Upper (D 7) (R 7) [96,257,9,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28442 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28443 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 138 176 96 86 150 278), lower := (rows 97 259 13 138 176 96 64 128 256), losses := [] }

theorem u28443 : Upper (D 7) (R 7) [96,257,9,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28444 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 205, targets := 2 },{ cop := 1, region := 48, targets := 64 }], pairs := [(0,1),(2,1),(3,1),(4,6)], upper := (rows 97 259 13 140 50 34 208 208 464), lower := (rows 97 259 13 140 50 34 64 128 256), losses := [] }

theorem u28444 : Upper (D 7) (R 7) [96,257,9,132,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28445 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 140 50 48 194 194 450), lower := (rows 97 259 13 140 50 48 64 128 256), losses := [] }

theorem u28445 : Upper (D 7) (R 7) [96,257,9,132,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28445 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28446 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 140 50 96 210 146 402), lower := (rows 97 259 13 140 50 96 64 128 256), losses := [] }

theorem u28446 : Upper (D 7) (R 7) [96,257,9,132,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28447 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(4,0),(4,7)], upper := (rows 97 259 13 140 50 160 82 210 338), lower := (rows 97 259 13 140 50 160 64 128 256), losses := [] }

theorem u28447 : Upper (D 7) (R 7) [96,257,9,132,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28448 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 97 259 13 140 146 34 112 240 368), lower := (rows 97 259 13 140 146 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 50 50 115 179 307), good := (rows 496 498 460 140 498 498 64 128 256) }] }

theorem u28448 : Upper (D 7) (R 7) [96,257,9,132,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28449 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(4,0)], upper := (rows 97 259 13 140 146 48 98 226 354), lower := (rows 97 259 13 140 146 48 64 128 256), losses := [] }

theorem u28449 : Upper (D 7) (R 7) [96,257,9,132,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28449 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28450 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 140 146 96 114 178 306), lower := (rows 97 259 13 140 146 96 64 128 256), losses := [] }

theorem u28450 : Upper (D 7) (R 7) [96,257,9,132,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28451 : Route 9 := (fun mask => (mask,id))

def c28451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28451 : Upper (D 7) (R 7) [96,257,9,132,160,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,132,160,2] 13 (by decide) (choices 1) [2,16] r28451 c28451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10712
  · exact u10713

def b28452 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 140 176 48 66 194 322), lower := (rows 97 259 13 140 176 48 64 128 256), losses := [] }

theorem u28452 : Upper (D 7) (R 7) [96,257,9,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28452 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28453 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 140 176 96 82 146 274), lower := (rows 97 259 13 140 176 96 64 128 256), losses := [] }

theorem u28453 : Upper (D 7) (R 7) [96,257,9,132,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28454 : Route 9 := (fun mask => (mask,id))

def c28454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u28454 : Upper (D 7) (R 7) [96,257,9,144,6,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,144,6,2] 13 (by decide) (choices 1) [32,128] r28454 c28454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10714
  · exact u10715

def b28455 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 152 22 96 226 162 418), lower := (rows 97 259 13 152 22 96 64 128 256), losses := [] }

theorem u28455 : Upper (D 7) (R 7) [96,257,9,144,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28456 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,7)], upper := (rows 97 259 13 152 22 160 98 226 354), lower := (rows 97 259 13 152 22 160 64 128 256), losses := [{ target := 7, region := (rows 33 39 4 8 20 32 97 0 289), good := (rows 355 323 351 24 22 355 64 0 256) }] }

theorem u28456 : Upper (D 7) (R 7) [96,257,9,144,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28457 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 97 259 13 152 50 34 196 196 452), lower := (rows 97 259 13 152 50 34 64 128 256), losses := [] }

theorem u28457 : Upper (D 7) (R 7) [96,257,9,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28458 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 200, targets := 33 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(3,0),(3,5)], upper := (rows 97 259 13 152 50 36 194 194 450), lower := (rows 97 259 13 152 50 36 64 128 256), losses := [] }

theorem u28458 : Upper (D 7) (R 7) [96,257,9,144,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28458 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28459 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 152 50 96 198 134 390), lower := (rows 97 259 13 152 50 96 64 128 256), losses := [] }

theorem u28459 : Upper (D 7) (R 7) [96,257,9,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28460 : Route 9 := (fun mask => (mask,id))

def c28460 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28460 : Upper (D 7) (R 7) [96,257,9,144,34,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,144,34,128] 13 (by decide) (choices 1) [2,4] r28460 c28460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10716
  · exact u10717

def r28461 : Route 9 := (fun mask => (mask,id))

def c28461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28461 : Upper (D 7) (R 7) [96,257,9,144,36,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,144,36,2] 13 (by decide) (choices 1) [2,128] r28461 c28461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10718
  · exact u10719

def b28462 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 152 52 96 194 130 386), lower := (rows 97 259 13 152 52 96 64 128 256), losses := [] }

theorem u28462 : Upper (D 7) (R 7) [96,257,9,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28463 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,0)], upper := (rows 97 259 13 152 52 160 66 194 322), lower := (rows 97 259 13 152 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 170 66 130 258), good := (rows 96 482 60 184 52 160 64 160 256) }] }

theorem u28463 : Upper (D 7) (R 7) [96,257,9,144,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28464 : Route 9 := (fun mask => (mask,id))

def c28464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28464 : Upper (D 7) (R 7) [96,257,9,160,6,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,6,2] 13 (by decide) (choices 1) [16,128] r28464 c28464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10720
  · exact u10721

def b28465 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 232, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 97 259 13 168 22 48 194 194 450), lower := (rows 97 259 13 168 22 48 64 128 256), losses := [] }

theorem u28465 : Upper (D 7) (R 7) [96,257,9,160,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28465 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28466 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 168 22 96 210 146 402), lower := (rows 97 259 13 168 22 96 64 128 256), losses := [] }

theorem u28466 : Upper (D 7) (R 7) [96,257,9,160,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28467 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 259 13 168 22 160 82 210 338), lower := (rows 97 259 13 168 22 160 64 128 256), losses := [] }

theorem u28467 : Upper (D 7) (R 7) [96,257,9,160,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28468 : Route 9 := (fun mask => (mask,id))

def c28468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28468 : Upper (D 7) (R 7) [96,257,9,160,66,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,66,2] 13 (by decide) (choices 1) [4,16,128] r28468 c28468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10722
  · exact u10723
  · exact u10724

def b28469 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 1, region := 208, targets := 1 }], pairs := [(1,5),(4,0),(4,5)], upper := (rows 97 259 13 168 82 36 210 146 402), lower := (rows 97 259 13 168 82 36 64 128 256), losses := [] }

theorem u28469 : Upper (D 7) (R 7) [96,257,9,160,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28469 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28470 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 168 82 48 198 134 390), lower := (rows 97 259 13 168 82 48 64 128 256), losses := [] }

theorem u28470 : Upper (D 7) (R 7) [96,257,9,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28470 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28471 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 259 13 168 82 160 86 150 278), lower := (rows 97 259 13 168 82 160 64 128 256), losses := [] }

theorem u28471 : Upper (D 7) (R 7) [96,257,9,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28472 : Route 9 := (fun mask => (mask,id))

def c28472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28472 : Upper (D 7) (R 7) [96,257,9,160,68,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,68,2] 13 (by decide) (choices 1) [2,16,128] r28472 c28472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10725
  · exact u10726
  · exact u10727

def b28473 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 168 84 48 194 130 386), lower := (rows 97 259 13 168 84 48 64 128 256), losses := [] }

theorem u28473 : Upper (D 7) (R 7) [96,257,9,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28473 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28474 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 259 13 168 84 160 82 146 274), lower := (rows 97 259 13 168 84 160 64 128 256), losses := [] }

theorem u28474 : Upper (D 7) (R 7) [96,257,9,160,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28475 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 97 259 13 168 146 34 84 212 340), lower := (rows 97 259 13 168 146 34 64 128 256), losses := [] }

theorem u28475 : Upper (D 7) (R 7) [96,257,9,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28476 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 1, region := 208, targets := 1 }], pairs := [(1,5),(4,0),(4,5)], upper := (rows 97 259 13 168 146 36 82 210 338), lower := (rows 97 259 13 168 146 36 64 128 256), losses := [] }

theorem u28476 : Upper (D 7) (R 7) [96,257,9,160,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28476 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28477 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 259 13 168 146 48 70 198 326), lower := (rows 97 259 13 168 146 48 64 128 256), losses := [] }

theorem u28477 : Upper (D 7) (R 7) [96,257,9,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28477 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28478 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 168 146 96 86 150 278), lower := (rows 97 259 13 168 146 96 64 128 256), losses := [] }

theorem u28478 : Upper (D 7) (R 7) [96,257,9,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28479 : Route 9 := (fun mask => (mask,id))

def c28479 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28479 : Upper (D 7) (R 7) [96,257,9,160,192,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,192,2] 13 (by decide) (choices 1) [2,4,16] r28479 c28479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10728
  · exact u10729
  · exact u10730

def b28480 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 259 13 168 208 36 82 146 274), lower := (rows 97 259 13 168 208 36 64 128 256), losses := [] }

theorem u28480 : Upper (D 7) (R 7) [96,257,9,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28480 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28481 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 168 208 48 70 134 262), lower := (rows 97 259 13 168 208 48 64 128 256), losses := [] }

theorem u28481 : Upper (D 7) (R 7) [96,257,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28481 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28482 : Route 9 := (fun mask => (mask,id))

def c28482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u28482 : Upper (D 7) (R 7) [96,257,10,20,129,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,20,129,2] 13 (by decide) (choices 1) [32,128] r28482 c28482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10731
  · exact u10732

def b28483 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 28 145 96 226 162 418), lower := (rows 97 259 14 28 145 96 64 128 256), losses := [] }

theorem u28483 : Upper (D 7) (R 7) [96,257,10,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28484 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 259 14 28 145 160 98 226 354), lower := (rows 97 259 14 28 145 160 64 128 256), losses := [{ target := 7, region := (rows 33 51 28 24 16 32 97 0 289), good := (rows 355 323 14 30 351 355 64 0 256) }] }

theorem u28484 : Upper (D 7) (R 7) [96,257,10,20,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28485 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(2,5)], upper := (rows 97 259 14 28 176 33 194 194 450), lower := (rows 97 259 14 28 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 35 20 24 16 0 119 183 311), good := (rows 451 451 462 476 478 451 64 128 256) }] }

theorem u28485 : Upper (D 7) (R 7) [96,257,10,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28486 : Route 9 := (fun mask => (mask,id))

def c28486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28486 : Upper (D 7) (R 7) [96,257,10,20,160,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,20,160,2] 13 (by decide) (choices 1) [1,128] r28486 c28486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10733
  · exact u10734

def b28487 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 28 176 96 195 131 387), lower := (rows 97 259 14 28 176 96 64 128 256), losses := [] }

theorem u28487 : Upper (D 7) (R 7) [96,257,10,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28488 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 259 14 28 176 160 67 195 323), lower := (rows 97 259 14 28 176 160 64 128 256), losses := [] }

theorem u28488 : Upper (D 7) (R 7) [96,257,10,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28489 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 14 44 82 33 208 144 400), lower := (rows 97 259 14 44 82 33 64 128 256), losses := [] }

theorem u28489 : Upper (D 7) (R 7) [96,257,10,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28490 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 259 14 44 82 48 193 129 385), lower := (rows 97 259 14 44 82 48 64 128 256), losses := [] }

theorem u28490 : Upper (D 7) (R 7) [96,257,10,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28490 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28491 : Route 9 := (fun mask => (mask,id))

def c28491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28491 : Upper (D 7) (R 7) [96,257,10,36,66,128] 13 := by
  apply FastRouting.sound _ _ [96,257,10,36,66,128] 13 (by decide) (choices 1) [1,16,128] r28491 c28491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10735
  · exact u10736
  · exact u10737

def b28492 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0)], upper := (rows 97 259 14 44 145 34 208 208 464), lower := (rows 97 259 14 44 145 34 64 128 256), losses := [] }

theorem u28492 : Upper (D 7) (R 7) [96,257,10,36,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28493 : Route 9 := (fun mask => (mask,id))

def c28493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28493 : Upper (D 7) (R 7) [96,257,10,36,129,16] 13 := by
  apply FastRouting.sound _ _ [96,257,10,36,129,16] 13 (by decide) (choices 1) [2,128] r28493 c28493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10738
  · exact u10739

def b28494 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 44 145 96 210 146 402), lower := (rows 97 259 14 44 145 96 64 128 256), losses := [] }

theorem u28494 : Upper (D 7) (R 7) [96,257,10,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28495 : Route 9 := (fun mask => (mask,id))

def c28495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28495 : Upper (D 7) (R 7) [96,257,10,36,129,128] 13 := by
  apply FastRouting.sound _ _ [96,257,10,36,129,128] 13 (by decide) (choices 1) [2,16] r28495 c28495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10740
  · exact u10741

def b28496 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 14 44 146 33 208 208 464), lower := (rows 97 259 14 44 146 33 64 128 256), losses := [] }

theorem u28496 : Upper (D 7) (R 7) [96,257,10,36,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28497 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 259 14 44 146 48 193 193 449), lower := (rows 97 259 14 44 146 48 64 128 256), losses := [] }

theorem u28497 : Upper (D 7) (R 7) [96,257,10,36,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28497 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28498 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 44 146 96 209 145 401), lower := (rows 97 259 14 44 146 96 64 128 256), losses := [] }

theorem u28498 : Upper (D 7) (R 7) [96,257,10,36,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28499 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 259 14 44 146 160 81 209 337), lower := (rows 97 259 14 44 146 160 64 128 256), losses := [] }

theorem u28499 : Upper (D 7) (R 7) [96,257,10,36,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28499
end Delivery.IrregularNine14.P07
