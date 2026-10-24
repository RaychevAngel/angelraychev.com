import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0014
import IrregularNine14P07C0015

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11700 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 328 176 34 208 208 464), lower := (rows 7 11 37 328 176 34 64 128 256), losses := [] }

theorem u11700 : Upper (D 7) (R 7) [6,9,33,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11701 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 37 328 176 48 194 194 450), lower := (rows 7 11 37 328 176 48 64 128 256), losses := [] }

theorem u11701 : Upper (D 7) (R 7) [6,9,33,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11701 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11702 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 11 37 328 176 96 210 146 402), lower := (rows 7 11 37 328 176 96 64 128 256), losses := [] }

theorem u11702 : Upper (D 7) (R 7) [6,9,33,320,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11703 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 37 328 176 160 82 210 338), lower := (rows 7 11 37 328 176 160 64 128 256), losses := [] }

theorem u11703 : Upper (D 7) (R 7) [6,9,33,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11704 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 328 208 34 240 176 432), lower := (rows 7 11 37 328 208 34 64 128 256), losses := [] }

theorem u11704 : Upper (D 7) (R 7) [6,9,33,320,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11705 : Route 9 := (fun mask => (mask,id))

def c11705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11705 : Upper (D 7) (R 7) [6,9,33,320,192,16] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,192,16] 13 (by decide) (choices 1) [2,32,128] r11705 c11705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u885
  · exact u886
  · exact u887

def r11706 : Route 9 := (fun mask => (mask,id))

def c11706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11706 : Upper (D 7) (R 7) [6,9,33,320,192,128] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,192,128] 13 (by decide) (choices 1) [2,16,32] r11706 c11706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u888
  · exact u889
  · exact u890

def b11707 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 2, region := 456, targets := 3 }], pairs := [(3,0),(3,1),(4,1),(4,5)], upper := (rows 7 11 52 104 145 34 448 448 448), lower := (rows 7 11 52 104 145 34 64 128 256), losses := [] }

theorem u11707 : Upper (D 7) (R 7) [6,9,48,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11708 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 52 104 145 96 450 386 386), lower := (rows 7 11 52 104 145 96 64 128 256), losses := [] }

theorem u11708 : Upper (D 7) (R 7) [6,9,48,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11709 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 11 52 104 145 160 322 450 322), lower := (rows 7 11 52 104 145 160 64 128 256), losses := [] }

theorem u11709 : Upper (D 7) (R 7) [6,9,48,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11710 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 488, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 52 104 145 288 194 194 450), lower := (rows 7 11 52 104 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 307 67 131 259), good := (rows 494 490 60 104 508 288 64 128 288) }] }

theorem u11710 : Upper (D 7) (R 7) [6,9,48,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11710 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11711 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 52 104 146 33 448 448 448), lower := (rows 7 11 52 104 146 33 64 128 256), losses := [] }

theorem u11711 : Upper (D 7) (R 7) [6,9,48,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11712 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 52 104 146 96 449 385 385), lower := (rows 7 11 52 104 146 96 64 128 256), losses := [] }

theorem u11712 : Upper (D 7) (R 7) [6,9,48,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11713 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 11 52 104 146 160 321 449 321), lower := (rows 7 11 52 104 146 160 64 128 256), losses := [] }

theorem u11713 : Upper (D 7) (R 7) [6,9,48,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11714 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 488, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 11 52 104 146 288 193 193 449), lower := (rows 7 11 52 104 146 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 27 16 307 67 131 259), good := (rows 493 489 60 104 508 288 64 128 288) }] }

theorem u11714 : Upper (D 7) (R 7) [6,9,48,96,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11714 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11715 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 52 104 208 33 450 386 386), lower := (rows 7 11 52 104 208 33 64 128 256), losses := [] }

theorem u11715 : Upper (D 7) (R 7) [6,9,48,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11716 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 52 104 208 34 449 385 385), lower := (rows 7 11 52 104 208 34 64 128 256), losses := [] }

theorem u11716 : Upper (D 7) (R 7) [6,9,48,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11717 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 104 208 160 323 387 259), lower := (rows 7 11 52 104 208 160 64 128 256), losses := [] }

theorem u11717 : Upper (D 7) (R 7) [6,9,48,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11718 : Route 9 := (fun mask => (mask,id))

def c11718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11718 : Upper (D 7) (R 7) [6,9,48,96,192,256] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192,256] 13 (by decide) (choices 1) [1,2,128] r11718 c11718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u891
  · exact u892
  · exact u893

def b11719 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 2, region := 200, targets := 3 }], pairs := [(3,0),(3,1),(4,1),(4,5)], upper := (rows 7 11 52 104 273 34 192 192 448), lower := (rows 7 11 52 104 273 34 64 128 256), losses := [] }

theorem u11719 : Upper (D 7) (R 7) [6,9,48,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11720 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 52 104 273 96 194 130 386), lower := (rows 7 11 52 104 273 96 64 128 256), losses := [] }

theorem u11720 : Upper (D 7) (R 7) [6,9,48,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11721 : Route 9 := (fun mask => (mask,id))

def c11721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11721 : Upper (D 7) (R 7) [6,9,48,96,257,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,257,128] 13 (by decide) (choices 1) [2,128] r11721 c11721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u894
  · exact u895

def b11722 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 52 104 274 33 192 192 448), lower := (rows 7 11 52 104 274 33 64 128 256), losses := [] }

theorem u11722 : Upper (D 7) (R 7) [6,9,48,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11723 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 52 104 274 96 193 129 385), lower := (rows 7 11 52 104 274 96 64 128 256), losses := [] }

theorem u11723 : Upper (D 7) (R 7) [6,9,48,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11724 : Route 9 := (fun mask => (mask,id))

def c11724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11724 : Upper (D 7) (R 7) [6,9,48,96,258,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,258,128] 13 (by decide) (choices 1) [1,128] r11724 c11724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u896
  · exact u897

def b11725 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 52 104 336 33 194 130 386), lower := (rows 7 11 52 104 336 33 64 128 256), losses := [] }

theorem u11725 : Upper (D 7) (R 7) [6,9,48,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11726 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 52 104 336 34 193 129 385), lower := (rows 7 11 52 104 336 34 64 128 256), losses := [] }

theorem u11726 : Upper (D 7) (R 7) [6,9,48,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11727 : Route 9 := (fun mask => (mask,id))

def c11727 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11727 : Upper (D 7) (R 7) [6,9,48,96,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,320,128] 13 (by decide) (choices 1) [1,2,128] r11727 c11727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u898
  · exact u899
  · exact u900

def b11728 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 464, targets := 33 }], pairs := [(2,0),(3,0),(4,0),(4,5)], upper := (rows 7 11 52 104 400 33 194 194 450), lower := (rows 7 11 52 104 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 51 32 67 131 259), good := (rows 470 478 60 124 400 508 64 128 256) }] }

theorem u11728 : Upper (D 7) (R 7) [6,9,48,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11729 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 }], pairs := [(2,1),(3,1),(4,1),(4,5)], upper := (rows 7 11 52 104 400 34 193 193 449), lower := (rows 7 11 52 104 400 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 40 51 32 67 131 259), good := (rows 469 477 60 124 400 508 64 128 256) }] }

theorem u11729 : Upper (D 7) (R 7) [6,9,48,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11730 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 52 104 400 96 195 131 387), lower := (rows 7 11 52 104 400 96 64 128 256), losses := [] }

theorem u11730 : Upper (D 7) (R 7) [6,9,48,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11731 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 11 52 104 400 160 67 195 323), lower := (rows 7 11 52 104 400 160 64 128 256), losses := [] }

theorem u11731 : Upper (D 7) (R 7) [6,9,48,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11732 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 200 81 34 480 416 416), lower := (rows 7 11 52 200 81 34 64 128 256), losses := [] }

theorem u11732 : Upper (D 7) (R 7) [6,9,48,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11733 : Route 9 := (fun mask => (mask,id))

def c11733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u11733 : Upper (D 7) (R 7) [6,9,48,192,65,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,65,128] 13 (by decide) (choices 1) [2,32,256] r11733 c11733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u901
  · exact u902
  · exact u903

def b11734 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 488, targets := 1 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 7 11 52 200 81 288 226 162 418), lower := (rows 7 11 52 200 81 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 307 67 131 259), good := (rows 494 490 60 200 508 288 64 128 288) },{ target := 6, region := (rows 1 2 20 8 16 307 0 131 259), good := (rows 423 427 52 136 437 288 0 128 288) }] }

theorem u11734 : Upper (D 7) (R 7) [6,9,48,192,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11734 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11735 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 200, targets := 3 }], pairs := [(2,0),(3,0),(3,1),(4,1)], upper := (rows 7 11 52 200 273 34 224 224 480), lower := (rows 7 11 52 200 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 63 16 35 119 183 311), good := (rows 494 490 508 200 508 490 64 128 256) },{ target := 1, region := (rows 1 0 4 45 17 32 100 164 292), good := (rows 477 25 508 200 281 488 64 128 256) }] }

theorem u11735 : Upper (D 7) (R 7) [6,9,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11736 : Route 9 := (fun mask => (mask,id))

def c11736 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11736 : Upper (D 7) (R 7) [6,9,48,192,257,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257,64] 13 (by decide) (choices 1) [2,32,128] r11736 c11736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u904
  · exact u905
  · exact u906

def b11737 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 52 200 274 33 224 224 480), lower := (rows 7 11 52 200 274 33 64 128 256), losses := [] }

theorem u11737 : Upper (D 7) (R 7) [6,9,48,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11738 : Route 9 := (fun mask => (mask,id))

def c11738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11738 : Upper (D 7) (R 7) [6,9,48,192,258,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,258,64] 13 (by decide) (choices 1) [1,32,128] r11738 c11738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u907
  · exact u908
  · exact u909

def r11739 : Route 9 := (fun mask => (mask,id))

def c11739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11739 : Upper (D 7) (R 7) [6,9,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,1] 13 (by decide) (choices 1) [2,32,128] r11739 c11739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u910
  · exact u911
  · exact u912

def r11740 : Route 9 := (fun mask => (mask,id))

def c11740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11740 : Upper (D 7) (R 7) [6,9,48,192,320,2] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,2] 13 (by decide) (choices 1) [1,32,128] r11740 c11740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u913
  · exact u914
  · exact u915

def r11741 : Route 9 := (fun mask => (mask,id))

def c11741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11741 : Upper (D 7) (R 7) [6,9,48,192,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,128] 13 (by decide) (choices 1) [1,2,32] r11741 c11741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u916
  · exact u917
  · exact u918

def b11742 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 11 52 266 208 33 224 224 480), lower := (rows 7 11 52 266 208 33 64 128 256), losses := [] }

theorem u11742 : Upper (D 7) (R 7) [6,9,48,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11743 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 11 52 266 208 96 225 161 417), lower := (rows 7 11 52 266 208 96 64 128 256), losses := [] }

theorem u11743 : Upper (D 7) (R 7) [6,9,48,258,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11744 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 2, region := 456, targets := 3 }], pairs := [(3,0),(3,1),(4,1),(4,5)], upper := (rows 7 11 52 296 81 34 192 192 448), lower := (rows 7 11 52 296 81 34 64 128 256), losses := [] }

theorem u11744 : Upper (D 7) (R 7) [6,9,48,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11745 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 11 52 296 81 96 194 130 386), lower := (rows 7 11 52 296 81 96 64 128 256), losses := [] }

theorem u11745 : Upper (D 7) (R 7) [6,9,48,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11746 : Route 9 := (fun mask => (mask,id))

def c11746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11746 : Upper (D 7) (R 7) [6,9,48,288,65,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,288,65,128] 13 (by decide) (choices 1) [2,128] r11746 c11746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u919
  · exact u920

def b11747 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 52 296 82 33 192 192 448), lower := (rows 7 11 52 296 82 33 64 128 256), losses := [] }

theorem u11747 : Upper (D 7) (R 7) [6,9,48,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11748 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 11 52 296 82 96 193 129 385), lower := (rows 7 11 52 296 82 96 64 128 256), losses := [] }

theorem u11748 : Upper (D 7) (R 7) [6,9,48,288,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11749 : Route 9 := (fun mask => (mask,id))

def c11749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11749 : Upper (D 7) (R 7) [6,9,48,288,66,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,288,66,128] 13 (by decide) (choices 1) [1,128] r11749 c11749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u921
  · exact u922

def b11750 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 208, targets := 33 }], pairs := [(2,0),(3,0),(4,0),(4,5)], upper := (rows 7 11 52 296 208 33 194 194 450), lower := (rows 7 11 52 296 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 51 32 67 131 259), good := (rows 470 478 60 316 208 508 64 128 256) }] }

theorem u11750 : Upper (D 7) (R 7) [6,9,48,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11751 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(2,1),(3,1),(4,1),(4,5)], upper := (rows 7 11 52 296 208 34 193 193 449), lower := (rows 7 11 52 296 208 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 40 51 32 67 131 259), good := (rows 469 477 60 316 208 508 64 128 256) }] }

theorem u11751 : Upper (D 7) (R 7) [6,9,48,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11752 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 11 52 296 208 96 195 131 387), lower := (rows 7 11 52 296 208 96 64 128 256), losses := [] }

theorem u11752 : Upper (D 7) (R 7) [6,9,48,288,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11753 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 328 81 34 224 160 416), lower := (rows 7 11 52 328 81 34 64 128 256), losses := [] }

theorem u11753 : Upper (D 7) (R 7) [6,9,48,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11754 : Route 9 := (fun mask => (mask,id))

def c11754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11754 : Upper (D 7) (R 7) [6,9,48,320,65,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,65,128] 13 (by decide) (choices 1) [2,32,128] r11754 c11754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u923
  · exact u924
  · exact u925

def b11755 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 456, targets := 3 }], pairs := [(2,0),(3,0),(3,1),(4,1)], upper := (rows 7 11 52 328 145 34 224 224 480), lower := (rows 7 11 52 328 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 63 16 35 119 183 311), good := (rows 494 490 508 328 508 490 64 128 256) },{ target := 1, region := (rows 1 0 4 45 17 32 100 164 292), good := (rows 477 25 508 328 153 488 64 128 256) }] }

theorem u11755 : Upper (D 7) (R 7) [6,9,48,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11756 : Route 9 := (fun mask => (mask,id))

def c11756 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11756 : Upper (D 7) (R 7) [6,9,48,320,129,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,129,64] 13 (by decide) (choices 1) [2,32,128] r11756 c11756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u926
  · exact u927
  · exact u928

def b11757 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 11 52 328 145 160 98 226 354), lower := (rows 7 11 52 328 145 160 64 128 256), losses := [] }

theorem u11757 : Upper (D 7) (R 7) [6,9,48,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11758 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 52 328 146 33 224 224 480), lower := (rows 7 11 52 328 146 33 64 128 256), losses := [] }

theorem u11758 : Upper (D 7) (R 7) [6,9,48,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11759 : Route 9 := (fun mask => (mask,id))

def c11759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11759 : Upper (D 7) (R 7) [6,9,48,320,130,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,130,64] 13 (by decide) (choices 1) [1,32,128] r11759 c11759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u929
  · exact u930
  · exact u931

#print axioms u11759
end Delivery.IrregularNine14.P07
