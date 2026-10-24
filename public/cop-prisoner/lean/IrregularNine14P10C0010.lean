import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0002

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b600 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 128 },{ cop := 3, region := 36, targets := 64 }], pairs := [(2,6),(4,7)], upper := (rows 7 74 164 392 112 288 113 177 305), lower := (rows 7 74 164 392 112 288 64 128 256), losses := [] }

theorem u600 : Upper (D 10) (R 10) [6,72,160,384,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b600 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 392 304 33 112 240 368), lower := (rows 7 74 164 392 304 33 64 128 256), losses := [] }

theorem u601 : Upper (D 10) (R 10) [6,72,160,384,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b601 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 52, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 392 304 48 97 225 353), lower := (rows 7 74 164 392 304 48 64 128 256), losses := [] }

theorem u602 : Upper (D 10) (R 10) [6,72,160,384,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b602 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r603 : Route 9 := (fun mask => (mask,id))

def c603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u603 : Upper (D 10) (R 10) [6,72,160,384,288,64] 13 := by
  apply FastRouting.sound _ _ [6,72,160,384,288,64] 13 (by decide) (choices 1) [1,16,32] r603 c603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u127
  · exact u128
  · exact u129

def b604 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 392 336 33 112 176 304), lower := (rows 7 74 164 392 336 33 64 128 256), losses := [] }

theorem u604 : Upper (D 10) (R 10) [6,72,160,384,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b604 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 392 336 48 97 161 289), lower := (rows 7 74 164 392 336 48 64 128 256), losses := [] }

theorem u605 : Upper (D 10) (R 10) [6,72,160,384,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b605 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 388 41 112 48 480 416 416), lower := (rows 7 74 388 41 112 48 64 128 256), losses := [] }

theorem u606 : Upper (D 10) (R 10) [6,72,384,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b606 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 388 41 112 160 368 432 304), lower := (rows 7 74 388 41 112 160 64 128 256), losses := [] }

theorem u607 : Upper (D 10) (R 10) [6,72,384,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b607 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 388 41 176 48 352 480 352), lower := (rows 7 74 388 41 176 48 64 128 256), losses := [] }

theorem u608 : Upper (D 10) (R 10) [6,72,384,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b608 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 74 388 41 176 96 368 432 304), lower := (rows 7 74 388 41 176 96 64 128 256), losses := [] }

theorem u609 : Upper (D 10) (R 10) [6,72,384,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b609 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 210, targets := 256 }], pairs := [(1,8),(4,8)], upper := (rows 7 74 388 41 176 288 112 240 368), lower := (rows 7 74 388 41 176 288 64 128 256), losses := [] }

theorem u610 : Upper (D 10) (R 10) [6,72,384,33,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b610 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 388 41 208 48 352 416 288), lower := (rows 7 74 388 41 208 48 64 128 256), losses := [] }

theorem u611 : Upper (D 10) (R 10) [6,72,384,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b611 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 210, targets := 256 }], pairs := [(1,8),(4,8)], upper := (rows 7 74 388 41 208 288 112 176 304), lower := (rows 7 74 388 41 208 288 64 128 256), losses := [] }

theorem u612 : Upper (D 10) (R 10) [6,72,384,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b612 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 202, targets := 256 }], pairs := [(1,8)], upper := (rows 7 74 388 152 304 33 96 224 352), lower := (rows 7 74 388 152 304 33 64 128 256), losses := [] }

theorem u613 : Upper (D 10) (R 10) [6,72,384,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b613 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r614 : Route 9 := (fun mask => (mask,id))

def c614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u614 : Upper (D 10) (R 10) [6,72,384,144,288,64] 13 := by
  apply FastRouting.sound _ _ [6,72,384,144,288,64] 13 (by decide) (choices 1) [1,32] r614 c614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u130
  · exact u131

def b615 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 388 168 49 48 352 480 352), lower := (rows 7 74 388 168 49 48 64 128 256), losses := [] }

theorem u615 : Upper (D 10) (R 10) [6,72,384,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b615 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b616 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 388 168 49 96 368 432 304), lower := (rows 7 74 388 168 49 96 64 128 256), losses := [] }

theorem u616 : Upper (D 10) (R 10) [6,72,384,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b616 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 202, targets := 256 }], pairs := [(1,8),(3,8)], upper := (rows 7 74 388 168 49 288 112 240 368), lower := (rows 7 74 388 168 49 288 64 128 256), losses := [] }

theorem u617 : Upper (D 10) (R 10) [6,72,384,160,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b617 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 388 168 112 33 368 432 304), lower := (rows 7 74 388 168 112 33 64 128 256), losses := [] }

theorem u618 : Upper (D 10) (R 10) [6,72,384,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b618 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 388 168 112 48 353 417 289), lower := (rows 7 74 388 168 112 48 64 128 256), losses := [] }

theorem u619 : Upper (D 10) (R 10) [6,72,384,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b619 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 128 },{ cop := 2, region := 40, targets := 64 }], pairs := [(3,6),(4,7)], upper := (rows 7 74 388 168 112 288 113 177 305), lower := (rows 7 74 388 168 112 288 64 128 256), losses := [] }

theorem u620 : Upper (D 10) (R 10) [6,72,384,160,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b620 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b621 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 388 168 304 33 112 240 368), lower := (rows 7 74 388 168 304 33 64 128 256), losses := [] }

theorem u621 : Upper (D 10) (R 10) [6,72,384,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b621 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 388 168 304 48 97 225 353), lower := (rows 7 74 388 168 304 48 64 128 256), losses := [] }

theorem u622 : Upper (D 10) (R 10) [6,72,384,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b622 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r623 : Route 9 := (fun mask => (mask,id))

def c623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u623 : Upper (D 10) (R 10) [6,72,384,160,288,64] 13 := by
  apply FastRouting.sound _ _ [6,72,384,160,288,64] 13 (by decide) (choices 1) [1,16,32] r623 c623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u132
  · exact u133
  · exact u134

def b624 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 388 168 336 33 112 176 304), lower := (rows 7 74 388 168 336 33 64 128 256), losses := [] }

theorem u624 : Upper (D 10) (R 10) [6,72,384,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b624 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 388 168 336 48 97 161 289), lower := (rows 7 74 388 168 336 48 64 128 256), losses := [] }

theorem u625 : Upper (D 10) (R 10) [6,72,384,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b625 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 41 208 40 336 400 272), lower := (rows 7 98 164 41 208 40 64 128 256), losses := [] }

theorem u626 : Upper (D 10) (R 10) [6,96,160,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b626 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 39, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 41 208 48 328 392 264), lower := (rows 7 98 164 41 208 48 64 128 256), losses := [] }

theorem u627 : Upper (D 10) (R 10) [6,96,160,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b627 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r628 : Route 9 := (fun mask => (mask,id))

def c628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u628 : Upper (D 10) (R 10) [6,96,160,33,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,33,192,256] 13 (by decide) (choices 1) [8,16,256] r628 c628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u135
  · exact u136
  · exact u137

def b629 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 41 280 48 448 448 448), lower := (rows 7 98 164 41 280 48 64 128 256), losses := [] }

theorem u629 : Upper (D 10) (R 10) [6,96,160,33,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b629 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b630 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 41 280 96 464 400 400), lower := (rows 7 98 164 41 280 96 64 128 256), losses := [] }

theorem u630 : Upper (D 10) (R 10) [6,96,160,33,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b630 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r631 : Route 9 := (fun mask => (mask,id))

def c631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u631 : Upper (D 10) (R 10) [6,96,160,33,264,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,33,264,256] 13 (by decide) (choices 1) [16,128] r631 c631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u138
  · exact u139

def b632 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 164 41 336 40 464 400 400), lower := (rows 7 98 164 41 336 40 64 128 256), losses := [] }

theorem u632 : Upper (D 10) (R 10) [6,96,160,33,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b632 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 41 336 48 456 392 392), lower := (rows 7 98 164 41 336 48 64 128 256), losses := [] }

theorem u633 : Upper (D 10) (R 10) [6,96,160,33,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b633 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 164 41 336 160 344 408 280), lower := (rows 7 98 164 41 336 160 64 128 256), losses := [] }

theorem u634 : Upper (D 10) (R 10) [6,96,160,33,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b634 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 464, targets := 32 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7),(4,5)], upper := (rows 7 98 164 41 336 288 216 152 408), lower := (rows 7 98 164 41 336 288 64 128 256), losses := [] }

theorem u635 : Upper (D 10) (R 10) [6,96,160,33,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b635 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 39, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 56 208 33 328 392 264), lower := (rows 7 98 164 56 208 33 64 128 256), losses := [] }

theorem u636 : Upper (D 10) (R 10) [6,96,160,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b636 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 56 208 40 321 385 257), lower := (rows 7 98 164 56 208 40 64 128 256), losses := [] }

theorem u637 : Upper (D 10) (R 10) [6,96,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b637 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r638 : Route 9 := (fun mask => (mask,id))

def c638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u638 : Upper (D 10) (R 10) [6,96,160,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,192,256] 13 (by decide) (choices 1) [1,8,256] r638 c638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u140
  · exact u141
  · exact u142

def b639 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 164 56 273 40 448 448 448), lower := (rows 7 98 164 56 273 40 64 128 256), losses := [] }

theorem u639 : Upper (D 10) (R 10) [6,96,160,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b639 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 56 273 96 456 392 392), lower := (rows 7 98 164 56 273 96 64 128 256), losses := [] }

theorem u640 : Upper (D 10) (R 10) [6,96,160,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b640 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 56 273 288 200 200 456), lower := (rows 7 98 164 56 273 288 64 128 256), losses := [] }

theorem u641 : Upper (D 10) (R 10) [6,96,160,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b641 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 56 280 33 448 448 448), lower := (rows 7 98 164 56 280 33 64 128 256), losses := [] }

theorem u642 : Upper (D 10) (R 10) [6,96,160,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b642 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 56 280 96 449 385 385), lower := (rows 7 98 164 56 280 96 64 128 256), losses := [] }

theorem u643 : Upper (D 10) (R 10) [6,96,160,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b643 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 98 164 56 280 288 193 193 449), lower := (rows 7 98 164 56 280 288 64 128 256), losses := [] }

theorem u644 : Upper (D 10) (R 10) [6,96,160,48,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b644 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 392, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 56 336 33 456 392 392), lower := (rows 7 98 164 56 336 33 64 128 256), losses := [] }

theorem u645 : Upper (D 10) (R 10) [6,96,160,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b645 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 42, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 164 56 336 40 449 385 385), lower := (rows 7 98 164 56 336 40 64 128 256), losses := [] }

theorem u646 : Upper (D 10) (R 10) [6,96,160,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b646 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 164 56 336 160 329 393 265), lower := (rows 7 98 164 56 336 160 64 128 256), losses := [] }

theorem u647 : Upper (D 10) (R 10) [6,96,160,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b647 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 56 336 288 201 137 393), lower := (rows 7 98 164 56 336 288 64 128 256), losses := [] }

theorem u648 : Upper (D 10) (R 10) [6,96,160,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b648 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 88 273 40 480 416 416), lower := (rows 7 98 164 88 273 40 64 128 256), losses := [] }

theorem u649 : Upper (D 10) (R 10) [6,96,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b649 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 164 88 273 160 360 424 296), lower := (rows 7 98 164 88 273 160 64 128 256), losses := [] }

theorem u650 : Upper (D 10) (R 10) [6,96,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b650 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(1,7),(2,6)], upper := (rows 7 98 164 88 273 288 232 168 424), lower := (rows 7 98 164 88 273 288 64 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 16 304 64 0 256), good := (rows 7 98 36 122 305 288 64 0 288) }] }

theorem u651 : Upper (D 10) (R 10) [6,96,160,80,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b651 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 164 88 304 33 456 392 392), lower := (rows 7 98 164 88 304 33 64 128 256), losses := [] }

theorem u652 : Upper (D 10) (R 10) [6,96,160,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b652 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 88 304 40 449 385 385), lower := (rows 7 98 164 88 304 40 64 128 256), losses := [] }

theorem u653 : Upper (D 10) (R 10) [6,96,160,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b653 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 164 88 304 160 329 393 265), lower := (rows 7 98 164 88 304 160 64 128 256), losses := [] }

theorem u654 : Upper (D 10) (R 10) [6,96,160,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b654 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 88 304 288 201 137 393), lower := (rows 7 98 164 88 304 288 64 128 256), losses := [] }

theorem u655 : Upper (D 10) (R 10) [6,96,160,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b655 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r656 : Route 9 := (fun mask => (mask,id))

def c656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u656 : Upper (D 10) (R 10) [6,96,160,80,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,384,1] 13 (by decide) (choices 1) [8,32,256] r656 c656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u143
  · exact u144
  · exact u145

def b657 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 88 400 40 353 417 289), lower := (rows 7 98 164 88 400 40 64 128 256), losses := [] }

theorem u657 : Upper (D 10) (R 10) [6,96,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b657 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b658 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(1,7),(2,6)], upper := (rows 7 98 164 88 400 288 105 169 297), lower := (rows 7 98 164 88 400 288 64 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 16 304 64 0 256), good := (rows 7 98 36 122 304 288 64 0 288) }] }

theorem u658 : Upper (D 10) (R 10) [6,96,160,80,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b658 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 200 273 40 368 432 304), lower := (rows 7 98 164 200 273 40 64 128 256), losses := [] }

theorem u659 : Upper (D 10) (R 10) [6,96,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b659 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P10
