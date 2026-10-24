import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0160
import IrregularNine14P07C0161

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26700 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 266 196 56 19 33 194 194 450), lower := (rows 37 266 196 56 19 33 64 128 256), losses := [] }

theorem u26700 : Upper (D 7) (R 7) [36,264,192,48,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26701 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(3,6),(3,7)], upper := (rows 37 266 196 56 19 34 193 193 449), lower := (rows 37 266 196 56 19 34 64 128 256), losses := [] }

theorem u26701 : Upper (D 7) (R 7) [36,264,192,48,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26702 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 196 56 19 96 195 131 387), lower := (rows 37 266 196 56 19 96 64 128 256), losses := [] }

theorem u26702 : Upper (D 7) (R 7) [36,264,192,48,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26703 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 196 56 81 33 194 130 386), lower := (rows 37 266 196 56 81 33 64 128 256), losses := [] }

theorem u26703 : Upper (D 7) (R 7) [36,264,192,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26704 : Route 9 := (fun mask => (mask,id))

def c26704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26704 : Upper (D 7) (R 7) [36,264,192,48,65,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,48,65,2] 13 (by decide) (choices 1) [1,2,128] r26704 c26704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9623
  · exact u9624
  · exact u9625

def b26705 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 56 81 160 67 131 259), lower := (rows 37 266 196 56 81 160 64 128 256), losses := [] }

theorem u26705 : Upper (D 7) (R 7) [36,264,192,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26706 : Route 9 := (fun mask => (mask,id))

def c26706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26706 : Upper (D 7) (R 7) [36,264,192,48,66,1] 13 := by
  apply FastRouting.sound _ _ [36,264,192,48,66,1] 13 (by decide) (choices 1) [1,2,128] r26706 c26706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9626
  · exact u9627
  · exact u9628

def b26707 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(3,6),(3,7)], upper := (rows 37 266 196 56 82 34 193 129 385), lower := (rows 37 266 196 56 82 34 64 128 256), losses := [] }

theorem u26707 : Upper (D 7) (R 7) [36,264,192,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26708 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 56 82 160 67 131 259), lower := (rows 37 266 196 56 82 160 64 128 256), losses := [] }

theorem u26708 : Upper (D 7) (R 7) [36,264,192,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26709 : Route 9 := (fun mask => (mask,id))

def c26709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u26709 : Upper (D 7) (R 7) [36,264,192,65,3,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,65,3,2] 13 (by decide) (choices 1) [16,32,128] r26709 c26709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9629
  · exact u9630
  · exact u9631

def b26710 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 228, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 37 266 196 73 19 48 226 162 418), lower := (rows 37 266 196 73 19 48 64 128 256), losses := [] }

theorem u26710 : Upper (D 7) (R 7) [36,264,192,65,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26710 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26711 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 73 19 160 114 178 306), lower := (rows 37 266 196 73 19 160 64 128 256), losses := [] }

theorem u26711 : Upper (D 7) (R 7) [36,264,192,65,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26712 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 196 73 50 33 210 146 402), lower := (rows 37 266 196 73 50 33 64 128 256), losses := [] }

theorem u26712 : Upper (D 7) (R 7) [36,264,192,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26713 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 266 196 73 50 34 209 145 401), lower := (rows 37 266 196 73 50 34 64 128 256), losses := [] }

theorem u26713 : Upper (D 7) (R 7) [36,264,192,65,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26714 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 196 73 50 48 195 131 387), lower := (rows 37 266 196 73 50 48 64 128 256), losses := [] }

theorem u26714 : Upper (D 7) (R 7) [36,264,192,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26714 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26715 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 73 50 160 83 147 275), lower := (rows 37 266 196 73 50 160 64 128 256), losses := [] }

theorem u26715 : Upper (D 7) (R 7) [36,264,192,65,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26716 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 196 73 146 33 114 178 306), lower := (rows 37 266 196 73 146 33 64 128 256), losses := [] }

theorem u26716 : Upper (D 7) (R 7) [36,264,192,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26717 : Route 9 := (fun mask => (mask,id))

def c26717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26717 : Upper (D 7) (R 7) [36,264,192,65,130,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,65,130,2] 13 (by decide) (choices 1) [1,16,32] r26717 c26717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9632
  · exact u9633
  · exact u9634

def b26718 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(1,7),(3,7)], upper := (rows 37 266 196 73 146 48 99 163 291), lower := (rows 37 266 196 73 146 48 64 128 256), losses := [] }

theorem u26718 : Upper (D 7) (R 7) [36,264,192,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26718 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26719 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 57, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(3,1),(4,1)], upper := (rows 37 266 196 73 176 33 82 146 274), lower := (rows 37 266 196 73 176 33 64 128 256), losses := [] }

theorem u26719 : Upper (D 7) (R 7) [36,264,192,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26720 : Route 9 := (fun mask => (mask,id))

def c26720 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26720 : Upper (D 7) (R 7) [36,264,192,65,160,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,65,160,2] 13 (by decide) (choices 1) [1,2,16] r26720 c26720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9635
  · exact u9636
  · exact u9637

def b26721 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 196 73 176 48 67 131 259), lower := (rows 37 266 196 73 176 48 64 128 256), losses := [] }

theorem u26721 : Upper (D 7) (R 7) [36,264,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26721 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26722 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 228, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 196 74 19 33 240 176 432), lower := (rows 37 266 196 74 19 33 64 128 256), losses := [] }

theorem u26722 : Upper (D 7) (R 7) [36,264,192,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26723 : Route 9 := (fun mask => (mask,id))

def c26723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26723 : Upper (D 7) (R 7) [36,264,192,66,3,16] 13 := by
  apply FastRouting.sound _ _ [36,264,192,66,3,16] 13 (by decide) (choices 1) [1,32,128] r26723 c26723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9638
  · exact u9639
  · exact u9640

def b26724 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 74 19 160 113 177 305), lower := (rows 37 266 196 74 19 160 64 128 256), losses := [] }

theorem u26724 : Upper (D 7) (R 7) [36,264,192,66,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26725 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 196 74 50 33 209 145 401), lower := (rows 37 266 196 74 50 33 64 128 256), losses := [] }

theorem u26725 : Upper (D 7) (R 7) [36,264,192,66,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26726 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 196 74 50 48 193 129 385), lower := (rows 37 266 196 74 50 48 64 128 256), losses := [] }

theorem u26726 : Upper (D 7) (R 7) [36,264,192,66,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26726 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26727 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 74 50 160 81 145 273), lower := (rows 37 266 196 74 50 160 64 128 256), losses := [] }

theorem u26727 : Upper (D 7) (R 7) [36,264,192,66,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26728 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 266 196 74 145 33 114 178 306), lower := (rows 37 266 196 74 145 33 64 128 256), losses := [] }

theorem u26728 : Upper (D 7) (R 7) [36,264,192,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26729 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(4,1)], upper := (rows 37 266 196 74 145 34 113 177 305), lower := (rows 37 266 196 74 145 34 64 128 256), losses := [] }

theorem u26729 : Upper (D 7) (R 7) [36,264,192,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26730 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 266 196 74 145 48 99 163 291), lower := (rows 37 266 196 74 145 48 64 128 256), losses := [] }

theorem u26730 : Upper (D 7) (R 7) [36,264,192,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26730 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26731 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 196 74 146 33 113 177 305), lower := (rows 37 266 196 74 146 33 64 128 256), losses := [] }

theorem u26731 : Upper (D 7) (R 7) [36,264,192,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26732 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 266 196 74 146 48 97 161 289), lower := (rows 37 266 196 74 146 48 64 128 256), losses := [] }

theorem u26732 : Upper (D 7) (R 7) [36,264,192,66,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26732 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26733 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 266 196 74 176 33 83 147 275), lower := (rows 37 266 196 74 176 33 64 128 256), losses := [] }

theorem u26733 : Upper (D 7) (R 7) [36,264,192,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26734 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,1),(2,1),(4,1),(4,6)], upper := (rows 37 266 196 74 176 34 81 145 273), lower := (rows 37 266 196 74 176 34 64 128 256), losses := [] }

theorem u26734 : Upper (D 7) (R 7) [36,264,192,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26735 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 266 196 74 176 48 67 131 259), lower := (rows 37 266 196 74 176 48 64 128 256), losses := [] }

theorem u26735 : Upper (D 7) (R 7) [36,264,192,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26735 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26736 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 266 196 88 19 33 226 162 418), lower := (rows 37 266 196 88 19 33 64 128 256), losses := [{ target := 6, region := (rows 5 10 4 8 16 53 0 152 280), good := (rows 37 394 165 442 435 33 0 128 256) }] }

theorem u26736 : Upper (D 7) (R 7) [36,264,192,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26737 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(3,1)], upper := (rows 37 266 196 88 19 34 225 161 417), lower := (rows 37 266 196 88 19 34 64 128 256), losses := [{ target := 1, region := (rows 33 0 53 24 16 32 97 161 289), good := (rows 485 264 196 92 477 485 64 128 256) },{ target := 6, region := (rows 1 10 4 8 16 58 0 145 273), good := (rows 421 298 132 442 435 34 0 128 256) }] }

theorem u26737 : Upper (D 7) (R 7) [36,264,192,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26738 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 88 19 160 99 163 291), lower := (rows 37 266 196 88 19 160 64 128 256), losses := [] }

theorem u26738 : Upper (D 7) (R 7) [36,264,192,80,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26739 : Route 9 := (fun mask => (mask,id))

def c26739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26739 : Upper (D 7) (R 7) [36,264,192,80,34,1] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,34,1] 13 (by decide) (choices 1) [1,2,128] r26739 c26739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9641
  · exact u9642
  · exact u9643

def b26740 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 266 196 88 50 34 193 129 385), lower := (rows 37 266 196 88 50 34 64 128 256), losses := [] }

theorem u26740 : Upper (D 7) (R 7) [36,264,192,80,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26741 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 88 50 160 67 131 259), lower := (rows 37 266 196 88 50 160 64 128 256), losses := [] }

theorem u26741 : Upper (D 7) (R 7) [36,264,192,80,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26742 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 57, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(3,1),(4,1)], upper := (rows 37 266 196 88 145 33 98 162 290), lower := (rows 37 266 196 88 145 33 64 128 256), losses := [] }

theorem u26742 : Upper (D 7) (R 7) [36,264,192,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26743 : Route 9 := (fun mask => (mask,id))

def c26743 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26743 : Upper (D 7) (R 7) [36,264,192,80,129,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,129,2] 13 (by decide) (choices 1) [1,2,32] r26743 c26743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9644
  · exact u9645
  · exact u9646

def r26744 : Route 9 := (fun mask => (mask,id))

def c26744 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26744 : Upper (D 7) (R 7) [36,264,192,80,130,1] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,130,1] 13 (by decide) (choices 1) [1,2,32] r26744 c26744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9647
  · exact u9648
  · exact u9649

def r26745 : Route 9 := (fun mask => (mask,id))

def c26745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26745 : Upper (D 7) (R 7) [36,264,192,80,130,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,130,2] 13 (by decide) (choices 1) [1,32] r26745 c26745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9650
  · exact u9651

def b26746 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(3,1),(4,1)], upper := (rows 37 266 196 88 176 33 67 131 259), lower := (rows 37 266 196 88 176 33 64 128 256), losses := [] }

theorem u26746 : Upper (D 7) (R 7) [36,264,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26747 : Route 9 := (fun mask => (mask,id))

def c26747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26747 : Upper (D 7) (R 7) [36,264,192,80,160,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,160,2] 13 (by decide) (choices 1) [1,2] r26747 c26747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9652
  · exact u9653

def b26748 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 196 104 19 33 210 146 402), lower := (rows 37 266 196 104 19 33 64 128 256), losses := [] }

theorem u26748 : Upper (D 7) (R 7) [36,264,192,96,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26749 : Route 9 := (fun mask => (mask,id))

def c26749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26749 : Upper (D 7) (R 7) [36,264,192,96,3,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,3,2] 13 (by decide) (choices 1) [1,16,128] r26749 c26749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9654
  · exact u9655
  · exact u9656

def r26750 : Route 9 := (fun mask => (mask,id))

def c26750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26750 : Upper (D 7) (R 7) [36,264,192,96,3,16] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,3,16] 13 (by decide) (choices 1) [1,2,128] r26750 c26750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9657
  · exact u9658
  · exact u9659

def b26751 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 104 19 160 83 147 275), lower := (rows 37 266 196 104 19 160 64 128 256), losses := [] }

theorem u26751 : Upper (D 7) (R 7) [36,264,192,96,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26752 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 57, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(3,1),(4,1)], upper := (rows 37 266 196 104 145 33 82 146 274), lower := (rows 37 266 196 104 145 33 64 128 256), losses := [] }

theorem u26752 : Upper (D 7) (R 7) [36,264,192,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26753 : Route 9 := (fun mask => (mask,id))

def c26753 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26753 : Upper (D 7) (R 7) [36,264,192,96,129,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,129,2] 13 (by decide) (choices 1) [1,2,16] r26753 c26753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9660
  · exact u9661
  · exact u9662

def b26754 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 266 196 104 145 48 67 131 259), lower := (rows 37 266 196 104 145 48 64 128 256), losses := [] }

theorem u26754 : Upper (D 7) (R 7) [36,264,192,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26754 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26755 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 196 104 146 33 83 147 275), lower := (rows 37 266 196 104 146 33 64 128 256), losses := [] }

theorem u26755 : Upper (D 7) (R 7) [36,264,192,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26756 : Route 9 := (fun mask => (mask,id))

def c26756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26756 : Upper (D 7) (R 7) [36,264,192,96,130,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,130,2] 13 (by decide) (choices 1) [1,16] r26756 c26756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9663
  · exact u9664

def r26757 : Route 9 := (fun mask => (mask,id))

def c26757 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26757 : Upper (D 7) (R 7) [36,264,192,96,130,16] 13 := by
  apply FastRouting.sound _ _ [36,264,192,96,130,16] 13 (by decide) (choices 1) [1,2] r26757 c26757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9665
  · exact u9666

def b26758 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 13 26 81 34 192 192 448), lower := (rows 37 290 13 26 81 34 64 128 256), losses := [] }

theorem u26758 : Upper (D 7) (R 7) [36,288,9,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26759 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(1,0),(1,6),(3,0)], upper := (rows 37 290 13 26 81 96 194 130 386), lower := (rows 37 290 13 26 81 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 112 64 128 256), good := (rows 37 288 13 61 113 96 96 128 256) }] }

theorem u26759 : Upper (D 7) (R 7) [36,288,9,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26759
end Delivery.IrregularNine14.P07
