import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0084
import IrregularNine14P07C0085

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r18660 : Route 9 := (fun mask => (mask,id))

def c18660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18660 : Upper (D 7) (R 7) [34,68,9,80,258,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,258,128] 13 (by decide) (choices 1) [1,32,128] r18660 c18660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5086
  · exact u5087
  · exact u5088

def b18661 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 88 304 33 194 130 386), lower := (rows 35 70 13 88 304 33 64 128 256), losses := [] }

theorem u18661 : Upper (D 7) (R 7) [34,68,9,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18662 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 88 304 34 193 129 385), lower := (rows 35 70 13 88 304 34 64 128 256), losses := [] }

theorem u18662 : Upper (D 7) (R 7) [34,68,9,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18663 : Route 9 := (fun mask => (mask,id))

def c18663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18663 : Upper (D 7) (R 7) [34,68,9,80,288,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,288,128] 13 (by decide) (choices 1) [1,2,128] r18663 c18663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5089
  · exact u5090
  · exact u5091

def b18664 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 88 400 33 226 162 418), lower := (rows 35 70 13 88 400 33 64 128 256), losses := [] }

theorem u18664 : Upper (D 7) (R 7) [34,68,9,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18665 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 88 400 34 225 161 417), lower := (rows 35 70 13 88 400 34 64 128 256), losses := [] }

theorem u18665 : Upper (D 7) (R 7) [34,68,9,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18666 : Route 9 := (fun mask => (mask,id))

def c18666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18666 : Upper (D 7) (R 7) [34,68,9,80,384,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,384,128] 13 (by decide) (choices 1) [1,2,32] r18666 c18666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5092
  · exact u5093
  · exact u5094

def b18667 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 13 138 81 48 480 416 416), lower := (rows 35 70 13 138 81 48 64 128 256), losses := [] }

theorem u18667 : Upper (D 7) (R 7) [34,68,9,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18667 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18668 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(2,6),(4,1),(4,7)], upper := (rows 35 70 13 138 81 160 368 432 304), lower := (rows 35 70 13 138 81 160 64 128 256), losses := [] }

theorem u18668 : Upper (D 7) (R 7) [34,68,9,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18669 : Route 9 := (fun mask => (mask,id))

def c18669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u18669 : Upper (D 7) (R 7) [34,68,9,130,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,65,256] 13 (by decide) (choices 1) [16,32,128] r18669 c18669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5095
  · exact u5096
  · exact u5097

def b18670 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 138 112 33 464 400 400), lower := (rows 35 70 13 138 112 33 64 128 256), losses := [] }

theorem u18670 : Upper (D 7) (R 7) [34,68,9,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18671 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 138 112 48 449 385 385), lower := (rows 35 70 13 138 112 48 64 128 256), losses := [] }

theorem u18671 : Upper (D 7) (R 7) [34,68,9,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18671 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18672 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(2,6),(4,1),(4,7)], upper := (rows 35 70 13 138 112 160 337 401 273), lower := (rows 35 70 13 138 112 160 64 128 256), losses := [] }

theorem u18672 : Upper (D 7) (R 7) [34,68,9,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18673 : Route 9 := (fun mask => (mask,id))

def c18673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18673 : Upper (D 7) (R 7) [34,68,9,130,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,96,256] 13 (by decide) (choices 1) [1,16,128] r18673 c18673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5098
  · exact u5099
  · exact u5100

def b18674 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 13 138 145 48 352 480 352), lower := (rows 35 70 13 138 145 48 64 128 256), losses := [] }

theorem u18674 : Upper (D 7) (R 7) [34,68,9,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18674 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18675 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 138 145 96 368 432 304), lower := (rows 35 70 13 138 145 96 64 128 256), losses := [] }

theorem u18675 : Upper (D 7) (R 7) [34,68,9,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18676 : Route 9 := (fun mask => (mask,id))

def c18676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18676 : Upper (D 7) (R 7) [34,68,9,130,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,129,256] 13 (by decide) (choices 1) [16,32] r18676 c18676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5101
  · exact u5102

def b18677 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 35 70 13 138 176 33 336 464 336), lower := (rows 35 70 13 138 176 33 64 128 256), losses := [] }

theorem u18677 : Upper (D 7) (R 7) [34,68,9,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18678 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 138 176 48 321 449 321), lower := (rows 35 70 13 138 176 48 64 128 256), losses := [] }

theorem u18678 : Upper (D 7) (R 7) [34,68,9,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18678 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18679 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 138 176 96 337 401 273), lower := (rows 35 70 13 138 176 96 64 128 256), losses := [] }

theorem u18679 : Upper (D 7) (R 7) [34,68,9,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18680 : Route 9 := (fun mask => (mask,id))

def c18680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18680 : Upper (D 7) (R 7) [34,68,9,130,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,160,256] 13 (by decide) (choices 1) [1,16] r18680 c18680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5103
  · exact u5104

def b18681 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 138 208 33 368 432 304), lower := (rows 35 70 13 138 208 33 64 128 256), losses := [] }

theorem u18681 : Upper (D 7) (R 7) [34,68,9,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18682 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 464, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 70 13 138 208 48 353 417 289), lower := (rows 35 70 13 138 208 48 64 128 256), losses := [] }

theorem u18682 : Upper (D 7) (R 7) [34,68,9,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18682 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18683 : Route 9 := (fun mask => (mask,id))

def c18683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18683 : Upper (D 7) (R 7) [34,68,9,130,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,192,256] 13 (by decide) (choices 1) [1,16,32] r18683 c18683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5105
  · exact u5106
  · exact u5107

def b18684 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 200, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(3,0),(4,1)], upper := (rows 35 70 13 138 273 48 224 224 480), lower := (rows 35 70 13 138 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 13 16 48 113 177 305), good := (rows 490 78 462 138 504 496 64 128 256) }] }

theorem u18684 : Upper (D 7) (R 7) [34,68,9,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18684 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18685 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 138 273 96 240 176 432), lower := (rows 35 70 13 138 273 96 64 128 256), losses := [] }

theorem u18685 : Upper (D 7) (R 7) [34,68,9,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18686 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(2,6),(4,1),(4,7)], upper := (rows 35 70 13 138 273 160 112 240 368), lower := (rows 35 70 13 138 273 160 64 128 256), losses := [] }

theorem u18686 : Upper (D 7) (R 7) [34,68,9,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18687 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 138 304 33 208 208 464), lower := (rows 35 70 13 138 304 33 64 128 256), losses := [] }

theorem u18687 : Upper (D 7) (R 7) [34,68,9,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18688 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 13 138 304 48 193 193 449), lower := (rows 35 70 13 138 304 48 64 128 256), losses := [] }

theorem u18688 : Upper (D 7) (R 7) [34,68,9,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18688 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18689 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 138 304 96 209 145 401), lower := (rows 35 70 13 138 304 96 64 128 256), losses := [] }

theorem u18689 : Upper (D 7) (R 7) [34,68,9,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18690 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(2,6),(4,1),(4,7)], upper := (rows 35 70 13 138 304 160 81 209 337), lower := (rows 35 70 13 138 304 160 64 128 256), losses := [] }

theorem u18690 : Upper (D 7) (R 7) [34,68,9,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18691 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 138 336 33 240 176 432), lower := (rows 35 70 13 138 336 33 64 128 256), losses := [] }

theorem u18691 : Upper (D 7) (R 7) [34,68,9,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18692 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 0, region := 464, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 70 13 138 336 48 225 161 417), lower := (rows 35 70 13 138 336 48 64 128 256), losses := [] }

theorem u18692 : Upper (D 7) (R 7) [34,68,9,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18692 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18693 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(2,6),(4,1),(4,7)], upper := (rows 35 70 13 138 336 160 113 177 305), lower := (rows 35 70 13 138 336 160 64 128 256), losses := [] }

theorem u18693 : Upper (D 7) (R 7) [34,68,9,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18694 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 138 400 33 112 240 368), lower := (rows 35 70 13 138 400 33 64 128 256), losses := [] }

theorem u18694 : Upper (D 7) (R 7) [34,68,9,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18695 : Route 9 := (fun mask => (mask,id))

def c18695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18695 : Upper (D 7) (R 7) [34,68,9,130,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130,384,16] 13 (by decide) (choices 1) [1,32] r18695 c18695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5108
  · exact u5109

def b18696 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 138 400 96 113 177 305), lower := (rows 35 70 13 138 400 96 64 128 256), losses := [] }

theorem u18696 : Upper (D 7) (R 7) [34,68,9,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18697 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,0),(4,0),(4,7)], upper := (rows 35 70 13 152 112 33 450 386 386), lower := (rows 35 70 13 152 112 33 64 128 256), losses := [] }

theorem u18697 : Upper (D 7) (R 7) [34,68,9,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18698 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 152 112 34 449 385 385), lower := (rows 35 70 13 152 112 34 64 128 256), losses := [] }

theorem u18698 : Upper (D 7) (R 7) [34,68,9,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18699 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 336, targets := 128 },{ cop := 1, region := 417, targets := 64 },{ cop := 2, region := 322, targets := 32 },{ cop := 2, region := 322, targets := 128 }], pairs := [(0,6),(1,5),(1,7),(4,7)], upper := (rows 35 70 13 152 112 160 323 387 259), lower := (rows 35 70 13 152 112 160 64 128 256), losses := [] }

theorem u18699 : Upper (D 7) (R 7) [34,68,9,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18700 : Route 9 := (fun mask => (mask,id))

def c18700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18700 : Upper (D 7) (R 7) [34,68,9,144,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,96,256] 13 (by decide) (choices 1) [1,2,128] r18700 c18700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5110
  · exact u5111
  · exact u5112

def b18701 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 152 273 34 224 224 480), lower := (rows 35 70 13 152 273 34 64 128 256), losses := [] }

theorem u18701 : Upper (D 7) (R 7) [34,68,9,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18702 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 152 273 96 226 162 418), lower := (rows 35 70 13 152 273 96 64 128 256), losses := [] }

theorem u18702 : Upper (D 7) (R 7) [34,68,9,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18703 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 336, targets := 128 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 35 70 13 152 273 160 98 226 354), lower := (rows 35 70 13 152 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 191 71 135 263), good := (rows 482 486 494 184 504 160 64 160 256) },{ target := 7, region := (rows 1 6 4 8 21 32 65 0 257), good := (rows 371 86 351 24 337 32 64 0 256) }] }

theorem u18703 : Upper (D 7) (R 7) [34,68,9,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18704 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 152 274 33 224 224 480), lower := (rows 35 70 13 152 274 33 64 128 256), losses := [] }

theorem u18704 : Upper (D 7) (R 7) [34,68,9,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18705 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 152 274 96 225 161 417), lower := (rows 35 70 13 152 274 96 64 128 256), losses := [] }

theorem u18705 : Upper (D 7) (R 7) [34,68,9,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18706 : Route 9 := (fun mask => (mask,id))

def c18706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18706 : Upper (D 7) (R 7) [34,68,9,144,258,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,258,128] 13 (by decide) (choices 1) [1,32] r18706 c18706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5113
  · exact u5114

def b18707 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 152 304 33 194 194 450), lower := (rows 35 70 13 152 304 33 64 128 256), losses := [] }

theorem u18707 : Upper (D 7) (R 7) [34,68,9,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18708 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 152 304 34 193 193 449), lower := (rows 35 70 13 152 304 34 64 128 256), losses := [] }

theorem u18708 : Upper (D 7) (R 7) [34,68,9,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18709 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 152 304 96 195 131 387), lower := (rows 35 70 13 152 304 96 64 128 256), losses := [] }

theorem u18709 : Upper (D 7) (R 7) [34,68,9,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18710 : Route 9 := (fun mask => (mask,id))

def c18710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18710 : Upper (D 7) (R 7) [34,68,9,144,288,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,288,128] 13 (by decide) (choices 1) [1,2] r18710 c18710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5115
  · exact u5116

def b18711 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 152 336 33 226 162 418), lower := (rows 35 70 13 152 336 33 64 128 256), losses := [] }

theorem u18711 : Upper (D 7) (R 7) [34,68,9,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18712 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 152 336 34 225 161 417), lower := (rows 35 70 13 152 336 34 64 128 256), losses := [] }

theorem u18712 : Upper (D 7) (R 7) [34,68,9,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18713 : Route 9 := (fun mask => (mask,id))

def c18713 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18713 : Upper (D 7) (R 7) [34,68,9,144,320,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,320,128] 13 (by decide) (choices 1) [1,2,32] r18713 c18713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5117
  · exact u5118
  · exact u5119

def b18714 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 168 81 34 464 400 400), lower := (rows 35 70 13 168 81 34 64 128 256), losses := [] }

theorem u18714 : Upper (D 7) (R 7) [34,68,9,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18715 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 13 168 81 48 450 386 386), lower := (rows 35 70 13 168 81 48 64 128 256), losses := [] }

theorem u18715 : Upper (D 7) (R 7) [34,68,9,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18715 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18716 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 13 168 81 160 338 402 274), lower := (rows 35 70 13 168 81 160 64 128 256), losses := [] }

theorem u18716 : Upper (D 7) (R 7) [34,68,9,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18717 : Route 9 := (fun mask => (mask,id))

def c18717 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18717 : Upper (D 7) (R 7) [34,68,9,160,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,65,256] 13 (by decide) (choices 1) [2,16,128] r18717 c18717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5120
  · exact u5121
  · exact u5122

def b18718 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 168 145 34 336 464 336), lower := (rows 35 70 13 168 145 34 64 128 256), losses := [] }

theorem u18718 : Upper (D 7) (R 7) [34,68,9,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18719 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 70 13 168 145 48 322 450 322), lower := (rows 35 70 13 168 145 48 64 128 256), losses := [] }

theorem u18719 : Upper (D 7) (R 7) [34,68,9,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18719 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18719
end Delivery.IrregularNine14.P07
