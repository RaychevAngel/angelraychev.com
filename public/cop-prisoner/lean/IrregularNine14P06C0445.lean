import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0139

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26700 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 134 262 74 112 33 85 149 277), lower := (rows 41 134 262 74 112 33 64 128 256), losses := [] }

theorem u26700 : Upper (D 6) (R 6) [40,132,258,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26701 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 41 134 262 74 112 36 81 145 273), lower := (rows 41 134 262 74 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 38 64 128 256), good := (rows 56 166 294 122 112 36 64 128 256) }] }

theorem u26701 : Upper (D 6) (R 6) [40,132,258,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26702 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 262 74 112 48 69 133 261), lower := (rows 41 134 262 74 112 48 64 128 256), losses := [] }

theorem u26702 : Upper (D 6) (R 6) [40,132,258,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26702 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26703 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 88 19 33 100 228 356), lower := (rows 41 134 262 88 19 33 64 128 256), losses := [] }

theorem u26703 : Upper (D 6) (R 6) [40,132,258,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26704 : PairBound 9 := { available := 97, camps := [], pairs := [(0,1),(3,1),(3,2)], upper := (rows 41 134 262 88 19 36 97 225 353), lower := (rows 41 134 262 88 19 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 24 16 38 81 145 273), good := (rows 489 164 292 473 505 36 64 128 256) },{ target := 2, region := (rows 1 2 0 24 16 32 65 129 257), good := (rows 489 130 258 88 475 32 64 128 256) }] }

theorem u26704 : Upper (D 6) (R 6) [40,132,258,80,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26705 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 262 88 19 96 101 165 293), lower := (rows 41 134 262 88 19 96 64 128 256), losses := [] }

theorem u26705 : Upper (D 6) (R 6) [40,132,258,80,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26706 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 88 50 33 69 197 325), lower := (rows 41 134 262 88 50 33 64 128 256), losses := [] }

theorem u26706 : Upper (D 6) (R 6) [40,132,258,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26707 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 88 50 36 65 193 321), lower := (rows 41 134 262 88 50 36 64 128 256), losses := [] }

theorem u26707 : Upper (D 6) (R 6) [40,132,258,80,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26708 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 262 88 50 96 69 133 261), lower := (rows 41 134 262 88 50 96 64 128 256), losses := [] }

theorem u26708 : Upper (D 6) (R 6) [40,132,258,80,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26709 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 276 11 52 33 66 194 322), lower := (rows 41 134 276 11 52 33 64 128 256), losses := [] }

theorem u26709 : Upper (D 6) (R 6) [40,132,272,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26710 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 276 11 52 34 65 193 321), lower := (rows 41 134 276 11 52 34 64 128 256), losses := [] }

theorem u26710 : Upper (D 6) (R 6) [40,132,272,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26711 : Route 9 := (fun mask => (mask,id))

def c26711 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26711 : Upper (D 6) (R 6) [40,132,272,3,36,64] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,36,64] 13 (by decide) (choices 1) [1,2] r26711 c26711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8366
  · exact u8367

def b26712 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 276 11 81 34 100 228 356), lower := (rows 41 134 276 11 81 34 64 128 256), losses := [] }

theorem u26712 : Upper (D 6) (R 6) [40,132,272,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26713 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 41 134 276 11 81 36 98 226 354), lower := (rows 41 134 276 11 81 36 64 128 256), losses := [] }

theorem u26713 : Upper (D 6) (R 6) [40,132,272,3,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26714 : Route 9 := (fun mask => (mask,id))

def c26714 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26714 : Upper (D 6) (R 6) [40,132,272,3,65,64] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,65,64] 13 (by decide) (choices 1) [2,4,32] r26714 c26714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8368
  · exact u8369
  · exact u8370

def b26715 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 276 11 82 33 100 228 356), lower := (rows 41 134 276 11 82 33 64 128 256), losses := [] }

theorem u26715 : Upper (D 6) (R 6) [40,132,272,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26716 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,1),(0,6),(3,6)], upper := (rows 41 134 276 11 82 36 97 225 353), lower := (rows 41 134 276 11 82 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 38 73 137 265), good := (rows 489 164 308 489 112 36 64 128 256) }] }

theorem u26716 : Upper (D 6) (R 6) [40,132,272,3,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26717 : Route 9 := (fun mask => (mask,id))

def c26717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26717 : Upper (D 6) (R 6) [40,132,272,3,66,64] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,66,64] 13 (by decide) (choices 1) [1,4,32] r26717 c26717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8371
  · exact u8372
  · exact u8373

def b26718 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 276 11 84 33 98 226 354), lower := (rows 41 134 276 11 84 33 64 128 256), losses := [] }

theorem u26718 : Upper (D 6) (R 6) [40,132,272,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26719 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 41, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 276 11 84 34 97 225 353), lower := (rows 41 134 276 11 84 34 64 128 256), losses := [] }

theorem u26719 : Upper (D 6) (R 6) [40,132,272,3,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26720 : Route 9 := (fun mask => (mask,id))

def c26720 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26720 : Upper (D 6) (R 6) [40,132,272,3,68,64] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,68,64] 13 (by decide) (choices 1) [1,2,32] r26720 c26720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8374
  · exact u8375
  · exact u8376

def b26721 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 276 11 112 33 70 198 326), lower := (rows 41 134 276 11 112 33 64 128 256), losses := [] }

theorem u26721 : Upper (D 6) (R 6) [40,132,272,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26722 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 276 11 112 34 69 197 325), lower := (rows 41 134 276 11 112 34 64 128 256), losses := [] }

theorem u26722 : Upper (D 6) (R 6) [40,132,272,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26723 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,1),(0,6),(3,6)], upper := (rows 41 134 276 11 112 36 67 195 323), lower := (rows 41 134 276 11 112 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 38 64 128 256), good := (rows 41 164 308 41 112 36 64 128 256) }] }

theorem u26723 : Upper (D 6) (R 6) [40,132,272,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26724 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 134 276 11 112 96 71 135 263), lower := (rows 41 134 276 11 112 96 64 128 256), losses := [] }

theorem u26724 : Upper (D 6) (R 6) [40,132,272,3,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26725 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 276 13 19 34 96 224 352), lower := (rows 41 134 276 13 19 34 64 128 256), losses := [] }

theorem u26725 : Upper (D 6) (R 6) [40,132,272,5,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26726 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 41 134 276 13 19 96 98 226 354), lower := (rows 41 134 276 13 19 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 118 82 146 274), good := (rows 41 482 496 41 499 96 96 128 256) }] }

theorem u26726 : Upper (D 6) (R 6) [40,132,272,5,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26727 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 276 13 50 33 66 194 322), lower := (rows 41 134 276 13 50 33 64 128 256), losses := [] }

theorem u26727 : Upper (D 6) (R 6) [40,132,272,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26728 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 276 13 50 34 65 193 321), lower := (rows 41 134 276 13 50 34 64 128 256), losses := [] }

theorem u26728 : Upper (D 6) (R 6) [40,132,272,5,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26729 : Route 9 := (fun mask => (mask,id))

def c26729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26729 : Upper (D 6) (R 6) [40,132,272,5,34,64] 13 := by
  apply FastRouting.sound _ _ [40,132,272,5,34,64] 13 (by decide) (choices 1) [1,2] r26729 c26729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8377
  · exact u8378

def b26730 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 41 134 276 13 81 34 98 226 354), lower := (rows 41 134 276 13 81 34 64 128 256), losses := [] }

theorem u26730 : Upper (D 6) (R 6) [40,132,272,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26731 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 134 276 13 81 96 98 162 290), lower := (rows 41 134 276 13 81 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 14 16 112 64 128 256), good := (rows 41 141 317 13 113 96 96 128 256) }] }

theorem u26731 : Upper (D 6) (R 6) [40,132,272,5,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26732 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 276 13 82 33 98 226 354), lower := (rows 41 134 276 13 82 33 64 128 256), losses := [] }

theorem u26732 : Upper (D 6) (R 6) [40,132,272,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26733 : Route 9 := (fun mask => (mask,id))

def c26733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26733 : Upper (D 6) (R 6) [40,132,272,5,66,2] 13 := by
  apply FastRouting.sound _ _ [40,132,272,5,66,2] 13 (by decide) (choices 1) [1,32] r26733 c26733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8379
  · exact u8380

def b26734 : PairBound 9 := { available := 35, camps := [], pairs := [(0,1),(1,6),(3,1)], upper := (rows 41 134 276 13 82 96 99 163 291), lower := (rows 41 134 276 13 82 96 64 128 256), losses := [{ target := 1, region := (rows 21 0 4 14 16 112 64 128 256), good := (rows 41 141 317 13 121 96 96 128 256) },{ target := 6, region := (rows 1 10 4 8 16 32 0 129 257), good := (rows 427 134 276 399 18 32 0 128 256) }] }

theorem u26734 : Upper (D 6) (R 6) [40,132,272,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26735 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 276 13 112 33 66 194 322), lower := (rows 41 134 276 13 112 33 64 128 256), losses := [] }

theorem u26735 : Upper (D 6) (R 6) [40,132,272,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26736 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(3,6)], upper := (rows 41 134 276 13 112 34 67 195 323), lower := (rows 41 134 276 13 112 34 64 128 256), losses := [] }

theorem u26736 : Upper (D 6) (R 6) [40,132,272,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26737 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 134 276 13 112 96 67 131 259), lower := (rows 41 134 276 13 112 96 64 128 256), losses := [] }

theorem u26737 : Upper (D 6) (R 6) [40,132,272,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26738 : Route 9 := (fun mask => (mask,id))

def c26738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26738 : Upper (D 6) (R 6) [40,132,272,65,3,2] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,3,2] 13 (by decide) (choices 1) [4,32] r26738 c26738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8381
  · exact u8382

def r26739 : Route 9 := (fun mask => (mask,id))

def c26739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26739 : Upper (D 6) (R 6) [40,132,272,65,3,4] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,3,4] 13 (by decide) (choices 1) [2,32] r26739 c26739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8383
  · exact u8384

def b26740 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 19 96 102 166 294), lower := (rows 41 134 276 73 19 96 64 128 256), losses := [] }

theorem u26740 : Upper (D 6) (R 6) [40,132,272,65,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26741 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 276 73 50 33 70 198 326), lower := (rows 41 134 276 73 50 33 64 128 256), losses := [] }

theorem u26741 : Upper (D 6) (R 6) [40,132,272,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26742 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 41 134 276 73 50 34 69 197 325), lower := (rows 41 134 276 73 50 34 64 128 256), losses := [] }

theorem u26742 : Upper (D 6) (R 6) [40,132,272,65,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26743 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 41 134 276 73 50 36 67 195 323), lower := (rows 41 134 276 73 50 36 64 128 256), losses := [] }

theorem u26743 : Upper (D 6) (R 6) [40,132,272,65,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26744 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 50 96 71 135 263), lower := (rows 41 134 276 73 50 96 64 128 256), losses := [] }

theorem u26744 : Upper (D 6) (R 6) [40,132,272,65,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26745 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 276 73 52 33 66 194 322), lower := (rows 41 134 276 73 52 33 64 128 256), losses := [] }

theorem u26745 : Upper (D 6) (R 6) [40,132,272,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26746 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 41 134 276 73 52 34 67 195 323), lower := (rows 41 134 276 73 52 34 64 128 256), losses := [] }

theorem u26746 : Upper (D 6) (R 6) [40,132,272,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26747 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 52 96 67 131 259), lower := (rows 41 134 276 73 52 96 64 128 256), losses := [] }

theorem u26747 : Upper (D 6) (R 6) [40,132,272,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26748 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 82 33 102 166 294), lower := (rows 41 134 276 73 82 33 64 128 256), losses := [] }

theorem u26748 : Upper (D 6) (R 6) [40,132,272,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26749 : Route 9 := (fun mask => (mask,id))

def c26749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26749 : Upper (D 6) (R 6) [40,132,272,65,66,2] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,66,2] 13 (by decide) (choices 1) [1,4,32] r26749 c26749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8385
  · exact u8386
  · exact u8387

def r26750 : Route 9 := (fun mask => (mask,id))

def c26750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26750 : Upper (D 6) (R 6) [40,132,272,65,66,4] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,66,4] 13 (by decide) (choices 1) [1,2,32] r26750 c26750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8388
  · exact u8389
  · exact u8390

def b26751 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 84 33 98 162 290), lower := (rows 41 134 276 73 84 33 64 128 256), losses := [] }

theorem u26751 : Upper (D 6) (R 6) [40,132,272,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26752 : Route 9 := (fun mask => (mask,id))

def c26752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26752 : Upper (D 6) (R 6) [40,132,272,65,68,2] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,68,2] 13 (by decide) (choices 1) [1,2,32] r26752 c26752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8391
  · exact u8392
  · exact u8393

def b26753 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 134 276 74 19 33 100 228 356), lower := (rows 41 134 276 74 19 33 64 128 256), losses := [] }

theorem u26753 : Upper (D 6) (R 6) [40,132,272,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26754 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 356, targets := 2 }], pairs := [(0,1),(2,1),(3,2)], upper := (rows 41 134 276 74 19 36 97 225 353), lower := (rows 41 134 276 74 19 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 20 8 16 54 89 153 281), good := (rows 489 164 500 489 501 36 64 128 256) },{ target := 2, region := (rows 1 2 0 24 16 32 65 129 257), good := (rows 489 130 280 74 475 32 64 128 256) }] }

theorem u26754 : Upper (D 6) (R 6) [40,132,272,66,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26755 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 276 74 19 96 101 165 293), lower := (rows 41 134 276 74 19 96 64 128 256), losses := [] }

theorem u26755 : Upper (D 6) (R 6) [40,132,272,66,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26756 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 134 276 74 21 33 98 226 354), lower := (rows 41 134 276 74 21 33 64 128 256), losses := [] }

theorem u26756 : Upper (D 6) (R 6) [40,132,272,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26757 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 276 74 21 34 97 225 353), lower := (rows 41 134 276 74 21 34 64 128 256), losses := [] }

theorem u26757 : Upper (D 6) (R 6) [40,132,272,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26758 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 276 74 21 96 99 163 291), lower := (rows 41 134 276 74 21 96 64 128 256), losses := [] }

theorem u26758 : Upper (D 6) (R 6) [40,132,272,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26759 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 134 276 74 50 33 69 197 325), lower := (rows 41 134 276 74 50 33 64 128 256), losses := [] }

theorem u26759 : Upper (D 6) (R 6) [40,132,272,66,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26759
end Delivery.IrregularNine14.P06
