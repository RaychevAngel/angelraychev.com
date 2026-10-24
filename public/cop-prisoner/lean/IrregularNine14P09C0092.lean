import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0035
import IrregularNine14P09C0036

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5520 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 200 146 33 336 400 272), lower := (rows 97 7 44 200 146 33 64 128 256), losses := [] }

theorem u5520 : Upper (D 9) (R 9) [96,5,40,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5520 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5521 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 7 44 200 146 48 321 385 257), lower := (rows 97 7 44 200 146 48 64 128 256), losses := [] }

theorem u5521 : Upper (D 9) (R 9) [96,5,40,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5521 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5522 : Route 9 := (fun mask => (mask,id))

def c5522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5522 : Upper (D 9) (R 9) [96,5,40,192,130,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,130,256] 13 (by decide) (choices 1) [1,16,256] r5522 c5522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2136
  · exact u2137
  · exact u2138

def b5523 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 200 273 34 464 400 400), lower := (rows 97 7 44 200 273 34 64 128 256), losses := [] }

theorem u5523 : Upper (D 9) (R 9) [96,5,40,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5523 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5524 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 456, targets := 1 },{ cop := 1, region := 400, targets := 64 }], pairs := [(3,0),(3,5),(4,5),(4,6)], upper := (rows 97 7 44 200 273 48 450 386 386), lower := (rows 97 7 44 200 273 48 64 128 256), losses := [] }

theorem u5524 : Upper (D 9) (R 9) [96,5,40,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5524 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5525 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 39, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 97 7 44 200 273 160 338 402 274), lower := (rows 97 7 44 200 273 160 64 128 256), losses := [] }

theorem u5525 : Upper (D 9) (R 9) [96,5,40,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5525 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5526 : Route 9 := (fun mask => (mask,id))

def c5526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5526 : Upper (D 9) (R 9) [96,5,40,192,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,257,256] 13 (by decide) (choices 1) [2,16,128] r5526 c5526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2139
  · exact u2140
  · exact u2141

def b5527 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 44 200 274 33 464 400 400), lower := (rows 97 7 44 200 274 33 64 128 256), losses := [] }

theorem u5527 : Upper (D 9) (R 9) [96,5,40,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5527 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5528 : Route 9 := (fun mask => (mask,id))

def c5528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5528 : Upper (D 9) (R 9) [96,5,40,192,258,16] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,258,16] 13 (by decide) (choices 1) [1,128,256] r5528 c5528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2142
  · exact u2143
  · exact u2144

def b5529 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 39, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 97 7 44 200 274 160 337 401 273), lower := (rows 97 7 44 200 274 160 64 128 256), losses := [] }

theorem u5529 : Upper (D 9) (R 9) [96,5,40,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5529 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5530 : Route 9 := (fun mask => (mask,id))

def c5530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5530 : Upper (D 9) (R 9) [96,5,40,192,258,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,258,256] 13 (by decide) (choices 1) [1,16,128] r5530 c5530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2145
  · exact u2146
  · exact u2147

def b5531 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 44 200 400 33 338 402 274), lower := (rows 97 7 44 200 400 33 64 128 256), losses := [] }

theorem u5531 : Upper (D 9) (R 9) [96,5,40,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5531 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5532 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 200 400 34 337 401 273), lower := (rows 97 7 44 200 400 34 64 128 256), losses := [] }

theorem u5532 : Upper (D 9) (R 9) [96,5,40,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5532 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5533 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 44 200 400 48 323 387 259), lower := (rows 97 7 44 200 400 48 64 128 256), losses := [] }

theorem u5533 : Upper (D 9) (R 9) [96,5,40,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5533 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5534 : Route 9 := (fun mask => (mask,id))

def c5534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5534 : Upper (D 9) (R 9) [96,5,40,192,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,384,256] 13 (by decide) (choices 1) [1,2,16] r5534 c5534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2148
  · exact u2149
  · exact u2150

def b5535 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 392 82 33 464 400 400), lower := (rows 97 7 44 392 82 33 64 128 256), losses := [] }

theorem u5535 : Upper (D 9) (R 9) [96,5,40,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5535 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5536 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 44 392 82 48 449 385 385), lower := (rows 97 7 44 392 82 48 64 128 256), losses := [] }

theorem u5536 : Upper (D 9) (R 9) [96,5,40,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5536 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5537 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,7)], upper := (rows 97 7 44 392 82 160 337 401 273), lower := (rows 97 7 44 392 82 160 64 128 256), losses := [] }

theorem u5537 : Upper (D 9) (R 9) [96,5,40,384,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5537 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5538 : Route 9 := (fun mask => (mask,id))

def c5538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5538 : Upper (D 9) (R 9) [96,5,40,384,129,2] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,129,2] 13 (by decide) (choices 1) [16,256] r5538 c5538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2151
  · exact u2152

def b5539 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 44 392 145 48 322 450 322), lower := (rows 97 7 44 392 145 48 64 128 256), losses := [] }

theorem u5539 : Upper (D 9) (R 9) [96,5,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5539 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5540 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 392 145 96 338 402 274), lower := (rows 97 7 44 392 145 96 64 128 256), losses := [] }

theorem u5540 : Upper (D 9) (R 9) [96,5,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5540 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5541 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 97 7 44 392 145 288 82 210 338), lower := (rows 97 7 44 392 145 288 64 128 256), losses := [] }

theorem u5541 : Upper (D 9) (R 9) [96,5,40,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5541 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5542 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 392 146 33 336 464 336), lower := (rows 97 7 44 392 146 33 64 128 256), losses := [] }

theorem u5542 : Upper (D 9) (R 9) [96,5,40,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5542 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5543 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 44 392 146 48 321 449 321), lower := (rows 97 7 44 392 146 48 64 128 256), losses := [] }

theorem u5543 : Upper (D 9) (R 9) [96,5,40,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5543 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5544 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 392 146 96 337 401 273), lower := (rows 97 7 44 392 146 96 64 128 256), losses := [] }

theorem u5544 : Upper (D 9) (R 9) [96,5,40,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5544 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5545 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 97 7 44 392 146 288 81 209 337), lower := (rows 97 7 44 392 146 288 64 128 256), losses := [] }

theorem u5545 : Upper (D 9) (R 9) [96,5,40,384,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5545 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5546 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 392 208 33 338 402 274), lower := (rows 97 7 44 392 208 33 64 128 256), losses := [] }

theorem u5546 : Upper (D 9) (R 9) [96,5,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5546 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5547 : Route 9 := (fun mask => (mask,id))

def c5547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5547 : Upper (D 9) (R 9) [96,5,40,384,192,2] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,192,2] 13 (by decide) (choices 1) [1,16,256] r5547 c5547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2153
  · exact u2154
  · exact u2155

def b5548 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 44 392 208 48 323 387 259), lower := (rows 97 7 44 392 208 48 64 128 256), losses := [] }

theorem u5548 : Upper (D 9) (R 9) [96,5,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5548 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5549 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 97 7 44 392 208 288 83 147 275), lower := (rows 97 7 44 392 208 288 64 128 256), losses := [] }

theorem u5549 : Upper (D 9) (R 9) [96,5,40,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5549 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5550 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 25 280 96 480 416 416), lower := (rows 97 7 134 25 280 96 64 128 256), losses := [] }

theorem u5550 : Upper (D 9) (R 9) [96,5,130,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5550 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5551 : PairBound 9 := { available := 352, camps := [{ cop := 5, region := 345, targets := 128 },{ cop := 1, region := 484, targets := 1 },{ cop := 3, region := 496, targets := 1 }], pairs := [(0,7),(2,0),(3,7),(4,0),(4,7)], upper := (rows 97 7 134 25 280 160 352 480 352), lower := (rows 97 7 134 25 280 160 64 128 256), losses := [] }

theorem u5551 : Upper (D 9) (R 9) [96,5,130,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5551 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5552 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 0, region := 400, targets := 1 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,5),(2,0),(2,5),(4,0)], upper := (rows 97 7 134 25 304 40 448 448 448), lower := (rows 97 7 134 25 304 40 64 128 256), losses := [] }

theorem u5552 : Upper (D 9) (R 9) [96,5,130,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5552 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5553 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 390, targets := 32 }], pairs := [(1,5),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 25 304 96 456 392 392), lower := (rows 97 7 134 25 304 96 64 128 256), losses := [] }

theorem u5553 : Upper (D 9) (R 9) [96,5,130,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5553 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5554 : PairBound 9 := { available := 328, camps := [{ cop := 5, region := 345, targets := 128 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,7),(1,5),(2,5),(3,7),(4,7)], upper := (rows 97 7 134 25 304 160 328 456 328), lower := (rows 97 7 134 25 304 160 64 128 256), losses := [] }

theorem u5554 : Upper (D 9) (R 9) [96,5,130,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5554 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5555 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 134 25 304 288 200 200 456), lower := (rows 97 7 134 25 304 288 64 128 256), losses := [] }

theorem u5555 : Upper (D 9) (R 9) [96,5,130,17,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5555 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5556 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(2,0),(3,7),(4,0)], upper := (rows 97 7 134 25 400 40 352 480 352), lower := (rows 97 7 134 25 400 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 59 40 105 169 297), good := (rows 496 470 150 504 400 504 64 128 256) }] }

theorem u5556 : Upper (D 9) (R 9) [96,5,130,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5556 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5557 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 25 400 96 360 424 296), lower := (rows 97 7 134 25 400 96 64 128 256), losses := [] }

theorem u5557 : Upper (D 9) (R 9) [96,5,130,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5557 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5558_8 : Upper (D 9) (R 9) [96,5,130,17,384,256,8] 13 :=
  permutation_upper _ _ _ [96,5,130,17,384,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2156

theorem m5558_32 : Upper (D 9) (R 9) [96,5,130,17,384,256,32] 13 :=
  permutation_upper _ _ _ [96,5,130,17,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2157

def r5558 : Route 9 := (fun mask => (mask,id))

def c5558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5558 : Upper (D 9) (R 9) [96,5,130,17,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,130,17,384,256] 13 (by decide) (choices 1) [8,32] r5558 c5558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5558_8
  · exact m5558_32

def b5559 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 97 7 134 56 208 33 328 392 264), lower := (rows 97 7 134 56 208 33 64 128 256), losses := [] }

theorem u5559 : Upper (D 9) (R 9) [96,5,130,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5559 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5560 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 134 56 208 40 321 385 257), lower := (rows 97 7 134 56 208 40 64 128 256), losses := [] }

theorem u5560 : Upper (D 9) (R 9) [96,5,130,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5560 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5561 : Route 9 := (fun mask => (mask,id))

def c5561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5561 : Upper (D 9) (R 9) [96,5,130,48,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,192,256] 13 (by decide) (choices 1) [1,8,256] r5561 c5561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2158
  · exact u2159
  · exact u2160

def b5562 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 4, region := 40, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,5)], upper := (rows 97 7 134 56 273 40 448 448 448), lower := (rows 97 7 134 56 273 40 64 128 256), losses := [] }

theorem u5562 : Upper (D 9) (R 9) [96,5,130,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5562 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5563 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 56 273 96 456 392 392), lower := (rows 97 7 134 56 273 96 64 128 256), losses := [] }

theorem u5563 : Upper (D 9) (R 9) [96,5,130,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5563 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5564 : Route 9 := (fun mask => (mask,id))

def c5564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5564 : Upper (D 9) (R 9) [96,5,130,48,257,128] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,257,128] 13 (by decide) (choices 1) [8,256] r5564 c5564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2161
  · exact u2162

def b5565 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 192 }], pairs := [(0,8),(1,8),(2,8),(3,6),(3,7)], upper := (rows 97 7 134 56 273 288 200 200 456), lower := (rows 97 7 134 56 273 288 64 128 256), losses := [] }

theorem u5565 : Upper (D 9) (R 9) [96,5,130,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5565 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5566 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 0, region := 390, targets := 32 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,0),(4,0)], upper := (rows 97 7 134 56 280 33 448 448 448), lower := (rows 97 7 134 56 280 33 64 128 256), losses := [] }

theorem u5566 : Upper (D 9) (R 9) [96,5,130,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5566 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5567 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 56 280 96 449 385 385), lower := (rows 97 7 134 56 280 96 64 128 256), losses := [] }

theorem u5567 : Upper (D 9) (R 9) [96,5,130,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5567 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5568 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 345, targets := 128 },{ cop := 0, region := 390, targets := 32 }], pairs := [(0,7),(1,5),(2,5),(3,7),(4,7)], upper := (rows 97 7 134 56 280 160 321 449 321), lower := (rows 97 7 134 56 280 160 64 128 256), losses := [] }

theorem u5568 : Upper (D 9) (R 9) [96,5,130,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5568 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5569 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0),(4,6)], upper := (rows 97 7 134 56 280 288 193 193 449), lower := (rows 97 7 134 56 280 288 64 128 256), losses := [] }

theorem u5569 : Upper (D 9) (R 9) [96,5,130,48,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5569 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5570 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 41, targets := 384 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 134 56 336 33 456 392 392), lower := (rows 97 7 134 56 336 33 64 128 256), losses := [] }

theorem u5570 : Upper (D 9) (R 9) [96,5,130,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5570 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5571 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 97 7 134 56 336 40 449 385 385), lower := (rows 97 7 134 56 336 40 64 128 256), losses := [] }

theorem u5571 : Upper (D 9) (R 9) [96,5,130,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5571 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5572 : Route 9 := (fun mask => (mask,id))

def c5572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5572 : Upper (D 9) (R 9) [96,5,130,48,320,128] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,320,128] 13 (by decide) (choices 1) [1,8,256] r5572 c5572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2163
  · exact u2164
  · exact u2165

def b5573 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 97 7 134 56 336 288 201 137 393), lower := (rows 97 7 134 56 336 288 64 128 256), losses := [] }

theorem u5573 : Upper (D 9) (R 9) [96,5,130,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5573 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5574 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 4, region := 105, targets := 128 },{ cop := 3, region := 464, targets := 32 }], pairs := [(0,7),(3,0),(3,7),(4,0),(4,5)], upper := (rows 97 7 134 56 400 33 328 456 328), lower := (rows 97 7 134 56 400 33 64 128 256), losses := [] }

theorem u5574 : Upper (D 9) (R 9) [96,5,130,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5574 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5575 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 97 7 134 56 400 40 321 449 321), lower := (rows 97 7 134 56 400 40 64 128 256), losses := [] }

theorem u5575 : Upper (D 9) (R 9) [96,5,130,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5575 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5576 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 56 400 96 329 393 265), lower := (rows 97 7 134 56 400 96 64 128 256), losses := [] }

theorem u5576 : Upper (D 9) (R 9) [96,5,130,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5576 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5577 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 97 7 134 56 400 288 73 201 329), lower := (rows 97 7 134 56 400 288 64 128 256), losses := [] }

theorem u5577 : Upper (D 9) (R 9) [96,5,130,48,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5577 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5578 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 369, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,7),(2,0),(3,0),(4,7)], upper := (rows 97 7 134 152 273 40 352 480 352), lower := (rows 97 7 134 152 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 24 16 56 121 185 313), good := (rows 480 454 134 504 504 488 64 128 256) }] }

theorem u5578 : Upper (D 9) (R 9) [96,5,130,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5578 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5579 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 152 273 96 360 424 296), lower := (rows 97 7 134 152 273 96 64 128 256), losses := [] }

theorem u5579 : Upper (D 9) (R 9) [96,5,130,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5579 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5579
end Delivery.IrregularNine14.P09
