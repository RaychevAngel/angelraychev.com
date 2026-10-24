import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0034
import IrregularNine14P09C0035

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5460 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 44 88 400 33 450 386 386), lower := (rows 97 7 44 88 400 33 64 128 256), losses := [] }

theorem u5460 : Upper (D 9) (R 9) [96,5,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5461 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 88 400 34 449 385 385), lower := (rows 97 7 44 88 400 34 64 128 256), losses := [] }

theorem u5461 : Upper (D 9) (R 9) [96,5,40,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5461 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5462 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 },{ cop := 1, region := 400, targets := 64 }], pairs := [(0,7),(1,7),(3,5),(4,5),(4,6)], upper := (rows 97 7 44 88 400 160 323 387 259), lower := (rows 97 7 44 88 400 160 64 128 256), losses := [] }

theorem u5462 : Upper (D 9) (R 9) [96,5,40,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5462 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5463 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 44 137 82 48 448 384 384), lower := (rows 97 7 44 137 82 48 64 128 256), losses := [] }

theorem u5463 : Upper (D 9) (R 9) [96,5,40,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5463 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5464 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 38, targets := 320 },{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 44 137 82 160 336 400 272), lower := (rows 97 7 44 137 82 160 64 128 256), losses := [] }

theorem u5464 : Upper (D 9) (R 9) [96,5,40,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5464 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5465 : Route 9 := (fun mask => (mask,id))

def c5465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u5465 : Upper (D 9) (R 9) [96,5,40,129,66,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,66,256] 13 (by decide) (choices 1) [16,128,256] r5465 c5465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2094
  · exact u2095
  · exact u2096

def b5466 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 54, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 44 137 146 48 320 448 320), lower := (rows 97 7 44 137 146 48 64 128 256), losses := [] }

theorem u5466 : Upper (D 9) (R 9) [96,5,40,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5466 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5467 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 137 146 96 336 400 272), lower := (rows 97 7 44 137 146 96 64 128 256), losses := [] }

theorem u5467 : Upper (D 9) (R 9) [96,5,40,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5467 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5468 : Route 9 := (fun mask => (mask,id))

def c5468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5468 : Upper (D 9) (R 9) [96,5,40,129,130,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,130,256] 13 (by decide) (choices 1) [16,256] r5468 c5468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2097
  · exact u2098

def b5469 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 38, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6)], upper := (rows 97 7 44 137 208 34 336 400 272), lower := (rows 97 7 44 137 208 34 64 128 256), losses := [] }

theorem u5469 : Upper (D 9) (R 9) [96,5,40,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5469 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5470 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 44 137 208 48 322 386 258), lower := (rows 97 7 44 137 208 48 64 128 256), losses := [] }

theorem u5470 : Upper (D 9) (R 9) [96,5,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5470 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5471 : Route 9 := (fun mask => (mask,id))

def c5471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5471 : Upper (D 9) (R 9) [96,5,40,129,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,192,256] 13 (by decide) (choices 1) [2,16,256] r5471 c5471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2099
  · exact u2100
  · exact u2101

def r5472 : Route 9 := (fun mask => (mask,id))

def c5472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5472 : Upper (D 9) (R 9) [96,5,40,129,258,16] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,258,16] 13 (by decide) (choices 1) [128,256] r5472 c5472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2102
  · exact u2103

def b5473 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 137 274 96 464 400 400), lower := (rows 97 7 44 137 274 96 64 128 256), losses := [] }

theorem u5473 : Upper (D 9) (R 9) [96,5,40,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5473 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5474 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 38, targets := 320 },{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 44 137 274 160 336 464 336), lower := (rows 97 7 44 137 274 160 64 128 256), losses := [] }

theorem u5474 : Upper (D 9) (R 9) [96,5,40,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5474 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5475 : Route 9 := (fun mask => (mask,id))

def c5475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5475 : Upper (D 9) (R 9) [96,5,40,129,258,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,258,256] 13 (by decide) (choices 1) [16,128] r5475 c5475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2104
  · exact u2105

def b5476 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 38, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6)], upper := (rows 97 7 44 137 336 34 464 400 400), lower := (rows 97 7 44 137 336 34 64 128 256), losses := [] }

theorem u5476 : Upper (D 9) (R 9) [96,5,40,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5476 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5477 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 44 137 336 48 450 386 386), lower := (rows 97 7 44 137 336 48 64 128 256), losses := [] }

theorem u5477 : Upper (D 9) (R 9) [96,5,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5477 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5478 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 38, targets := 320 },{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 44 137 336 160 338 402 274), lower := (rows 97 7 44 137 336 160 64 128 256), losses := [] }

theorem u5478 : Upper (D 9) (R 9) [96,5,40,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5478 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5479 : Route 9 := (fun mask => (mask,id))

def c5479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5479 : Upper (D 9) (R 9) [96,5,40,129,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,320,256] 13 (by decide) (choices 1) [2,16,128] r5479 c5479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2106
  · exact u2107
  · exact u2108

def b5480 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 38, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6)], upper := (rows 97 7 44 137 400 34 336 464 336), lower := (rows 97 7 44 137 400 34 64 128 256), losses := [] }

theorem u5480 : Upper (D 9) (R 9) [96,5,40,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5480 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5481 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 44 137 400 48 322 450 322), lower := (rows 97 7 44 137 400 48 64 128 256), losses := [] }

theorem u5481 : Upper (D 9) (R 9) [96,5,40,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5481 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5482 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 137 400 96 338 402 274), lower := (rows 97 7 44 137 400 96 64 128 256), losses := [] }

theorem u5482 : Upper (D 9) (R 9) [96,5,40,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5482 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5483 : Route 9 := (fun mask => (mask,id))

def c5483 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5483 : Upper (D 9) (R 9) [96,5,40,129,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,384,256] 13 (by decide) (choices 1) [2,16] r5483 c5483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2109
  · exact u2110

def b5484 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 46, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 44 138 145 48 320 448 320), lower := (rows 97 7 44 138 145 48 64 128 256), losses := [] }

theorem u5484 : Upper (D 9) (R 9) [96,5,40,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5484 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5485 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 138 145 96 336 400 272), lower := (rows 97 7 44 138 145 96 64 128 256), losses := [] }

theorem u5485 : Upper (D 9) (R 9) [96,5,40,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5485 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5486 : Route 9 := (fun mask => (mask,id))

def c5486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5486 : Upper (D 9) (R 9) [96,5,40,130,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,129,256] 13 (by decide) (choices 1) [16,256] r5486 c5486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2111
  · exact u2112

def b5487 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 138 208 33 336 400 272), lower := (rows 97 7 44 138 208 33 64 128 256), losses := [] }

theorem u5487 : Upper (D 9) (R 9) [96,5,40,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5487 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5488 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 44 138 208 48 321 385 257), lower := (rows 97 7 44 138 208 48 64 128 256), losses := [] }

theorem u5488 : Upper (D 9) (R 9) [96,5,40,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5488 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5489 : Route 9 := (fun mask => (mask,id))

def c5489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5489 : Upper (D 9) (R 9) [96,5,40,130,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,192,256] 13 (by decide) (choices 1) [1,16,256] r5489 c5489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2113
  · exact u2114
  · exact u2115

def r5490 : Route 9 := (fun mask => (mask,id))

def c5490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5490 : Upper (D 9) (R 9) [96,5,40,130,257,16] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,257,16] 13 (by decide) (choices 1) [128,256] r5490 c5490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2116
  · exact u2117

def b5491 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 138 273 96 464 400 400), lower := (rows 97 7 44 138 273 96 64 128 256), losses := [] }

theorem u5491 : Upper (D 9) (R 9) [96,5,40,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5491 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5492 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 97 7 44 138 273 160 336 464 336), lower := (rows 97 7 44 138 273 160 64 128 256), losses := [] }

theorem u5492 : Upper (D 9) (R 9) [96,5,40,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5492 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5493 : Route 9 := (fun mask => (mask,id))

def c5493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5493 : Upper (D 9) (R 9) [96,5,40,130,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,257,256] 13 (by decide) (choices 1) [16,128] r5493 c5493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2118
  · exact u2119

def b5494 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 138 336 33 464 400 400), lower := (rows 97 7 44 138 336 33 64 128 256), losses := [] }

theorem u5494 : Upper (D 9) (R 9) [96,5,40,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5494 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5495 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 44 138 336 48 449 385 385), lower := (rows 97 7 44 138 336 48 64 128 256), losses := [] }

theorem u5495 : Upper (D 9) (R 9) [96,5,40,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5495 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5496 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 97 7 44 138 336 160 337 401 273), lower := (rows 97 7 44 138 336 160 64 128 256), losses := [] }

theorem u5496 : Upper (D 9) (R 9) [96,5,40,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5496 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5497 : Route 9 := (fun mask => (mask,id))

def c5497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5497 : Upper (D 9) (R 9) [96,5,40,130,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,320,256] 13 (by decide) (choices 1) [1,16,128] r5497 c5497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2120
  · exact u2121
  · exact u2122

def b5498 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 138 400 33 336 464 336), lower := (rows 97 7 44 138 400 33 64 128 256), losses := [] }

theorem u5498 : Upper (D 9) (R 9) [96,5,40,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5498 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5499 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 44 138 400 48 321 449 321), lower := (rows 97 7 44 138 400 48 64 128 256), losses := [] }

theorem u5499 : Upper (D 9) (R 9) [96,5,40,130,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5499 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5500 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 138 400 96 337 401 273), lower := (rows 97 7 44 138 400 96 64 128 256), losses := [] }

theorem u5500 : Upper (D 9) (R 9) [96,5,40,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5500 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5501 : Route 9 := (fun mask => (mask,id))

def c5501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5501 : Upper (D 9) (R 9) [96,5,40,130,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,384,256] 13 (by decide) (choices 1) [1,16] r5501 c5501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2123
  · exact u2124

def b5502 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 152 82 33 448 384 384), lower := (rows 97 7 44 152 82 33 64 128 256), losses := [] }

theorem u5502 : Upper (D 9) (R 9) [96,5,40,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5502 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5503 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 97 7 44 152 82 160 321 385 257), lower := (rows 97 7 44 152 82 160 64 128 256), losses := [] }

theorem u5503 : Upper (D 9) (R 9) [96,5,40,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5503 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5504 : Route 9 := (fun mask => (mask,id))

def c5504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5504 : Upper (D 9) (R 9) [96,5,40,144,66,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,66,256] 13 (by decide) (choices 1) [1,128,256] r5504 c5504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2125
  · exact u2126
  · exact u2127

def r5505 : Route 9 := (fun mask => (mask,id))

def c5505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5505 : Upper (D 9) (R 9) [96,5,40,144,257,2] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,257,2] 13 (by decide) (choices 1) [128,256] r5505 c5505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2128
  · exact u2129

def b5506 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 152 273 96 450 386 386), lower := (rows 97 7 44 152 273 96 64 128 256), losses := [] }

theorem u5506 : Upper (D 9) (R 9) [96,5,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5506 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5507 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 97 7 44 152 273 160 322 450 322), lower := (rows 97 7 44 152 273 160 64 128 256), losses := [] }

theorem u5507 : Upper (D 9) (R 9) [96,5,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5507 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5508 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(2,0),(3,5),(4,5)], upper := (rows 97 7 44 152 273 288 194 194 450), lower := (rows 97 7 44 152 273 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 306 66 130 258), good := (rows 96 486 44 188 304 288 64 128 288) }] }

theorem u5508 : Upper (D 9) (R 9) [96,5,40,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5508 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5509 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 152 274 33 448 448 448), lower := (rows 97 7 44 152 274 33 64 128 256), losses := [] }

theorem u5509 : Upper (D 9) (R 9) [96,5,40,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5509 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5510 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 152 274 96 449 385 385), lower := (rows 97 7 44 152 274 96 64 128 256), losses := [] }

theorem u5510 : Upper (D 9) (R 9) [96,5,40,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5510 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5511 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 97 7 44 152 274 160 321 449 321), lower := (rows 97 7 44 152 274 160 64 128 256), losses := [] }

theorem u5511 : Upper (D 9) (R 9) [96,5,40,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5511 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5512 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(2,0),(3,5),(4,5)], upper := (rows 97 7 44 152 274 288 193 193 449), lower := (rows 97 7 44 152 274 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 96 6 44 188 306 288 64 128 288) }] }

theorem u5512 : Upper (D 9) (R 9) [96,5,40,144,258,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5512 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5513 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 152 336 33 450 386 386), lower := (rows 97 7 44 152 336 33 64 128 256), losses := [] }

theorem u5513 : Upper (D 9) (R 9) [96,5,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5513 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5514 : Route 9 := (fun mask => (mask,id))

def c5514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5514 : Upper (D 9) (R 9) [96,5,40,144,320,2] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,320,2] 13 (by decide) (choices 1) [1,128,256] r5514 c5514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2130
  · exact u2131
  · exact u2132

def b5515 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 97 7 44 152 336 160 323 387 259), lower := (rows 97 7 44 152 336 160 64 128 256), losses := [] }

theorem u5515 : Upper (D 9) (R 9) [96,5,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5515 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5516 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 195, targets := 256 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,5),(4,5)], upper := (rows 97 7 44 152 336 288 195 131 387), lower := (rows 97 7 44 152 336 288 64 128 256), losses := [] }

theorem u5516 : Upper (D 9) (R 9) [96,5,40,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5516 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5517 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 7 44 200 145 34 336 400 272), lower := (rows 97 7 44 200 145 34 64 128 256), losses := [] }

theorem u5517 : Upper (D 9) (R 9) [96,5,40,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5517 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5518 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 7 44 200 145 48 322 386 258), lower := (rows 97 7 44 200 145 48 64 128 256), losses := [] }

theorem u5518 : Upper (D 9) (R 9) [96,5,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5518 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5519 : Route 9 := (fun mask => (mask,id))

def c5519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5519 : Upper (D 9) (R 9) [96,5,40,192,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,129,256] 13 (by decide) (choices 1) [2,16,256] r5519 c5519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2133
  · exact u2134
  · exact u2135

#print axioms u5519
end Delivery.IrregularNine14.P09
