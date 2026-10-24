import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0093

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18960 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 14 274 96 101 165 293), lower := (rows 25 98 133 14 274 96 64 128 256), losses := [] }

theorem u18960 : Upper (D 6) (R 6) [24,96,129,6,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18961 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 25 98 133 14 276 33 98 226 354), lower := (rows 25 98 133 14 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 24 32 98 162 290), good := (rows 24 482 132 478 276 482 64 128 256) }] }

theorem u18961 : Upper (D 6) (R 6) [24,96,129,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m18962_1 : Upper (D 6) (R 6) [24,96,129,6,260,2,1] 13 :=
  permutation_upper _ _ _ [24,96,129,6,260,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5609

def r18962 : Route 9 := (fun mask => (mask,id))

def c18962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18962 : Upper (D 6) (R 6) [24,96,129,6,260,2] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,260,2] 13 (by decide) (choices 1) [1,32] r18962 c18962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m18962_1
  · exact u5610

def b18963 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 14 276 96 99 163 291), lower := (rows 25 98 133 14 276 96 64 128 256), losses := [] }

theorem u18963 : Upper (D 6) (R 6) [24,96,129,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18964 : Route 9 := (fun mask => (mask,id))

def c18964 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18964 : Upper (D 6) (R 6) [24,96,129,6,288,1] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,288,1] 13 (by decide) (choices 1) [2,4] r18964 c18964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5611
  · exact u5612

def b18965 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 98 133 14 304 34 69 197 325), lower := (rows 25 98 133 14 304 34 64 128 256), losses := [] }

theorem u18965 : Upper (D 6) (R 6) [24,96,129,6,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18966 : Route 9 := (fun mask => (mask,id))

def c18966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18966 : Upper (D 6) (R 6) [24,96,129,6,288,4] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,288,4] 13 (by decide) (choices 1) [1,2] r18966 c18966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5613
  · exact u5614

def b18967 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 14 304 96 71 135 263), lower := (rows 25 98 133 14 304 96 64 128 256), losses := [] }

theorem u18967 : Upper (D 6) (R 6) [24,96,129,6,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18968 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 133 41 84 34 326 390 262), lower := (rows 25 98 133 41 84 34 64 128 256), losses := [] }

theorem u18968 : Upper (D 6) (R 6) [24,96,129,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18969 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 133 41 84 36 322 386 258), lower := (rows 25 98 133 41 84 36 64 128 256), losses := [] }

theorem u18969 : Upper (D 6) (R 6) [24,96,129,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18970 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 25 98 133 41 84 288 70 134 262), lower := (rows 25 98 133 41 84 288 64 128 256), losses := [] }

theorem u18970 : Upper (D 6) (R 6) [24,96,129,33,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18970 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18971 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 98 133 41 274 34 68 196 324), lower := (rows 25 98 133 41 274 34 64 128 256), losses := [] }

theorem u18971 : Upper (D 6) (R 6) [24,96,129,33,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18972 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 2, region := 40, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 25 98 133 41 274 36 70 198 326), lower := (rows 25 98 133 41 274 36 64 128 256), losses := [] }

theorem u18972 : Upper (D 6) (R 6) [24,96,129,33,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18973 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 41 274 96 70 134 262), lower := (rows 25 98 133 41 274 96 64 128 256), losses := [] }

theorem u18973 : Upper (D 6) (R 6) [24,96,129,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18974 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 25 98 133 41 276 34 70 198 326), lower := (rows 25 98 133 41 276 34 64 128 256), losses := [] }

theorem u18974 : Upper (D 6) (R 6) [24,96,129,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18975 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 133 41 276 36 66 194 322), lower := (rows 25 98 133 41 276 36 64 128 256), losses := [] }

theorem u18975 : Upper (D 6) (R 6) [24,96,129,33,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18976 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 41 276 96 70 134 262), lower := (rows 25 98 133 41 276 96 64 128 256), losses := [] }

theorem u18976 : Upper (D 6) (R 6) [24,96,129,33,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18977 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 133 41 336 34 70 134 262), lower := (rows 25 98 133 41 336 34 64 128 256), losses := [] }

theorem u18977 : Upper (D 6) (R 6) [24,96,129,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18978 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 2, region := 40, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 25 98 133 41 336 36 70 134 262), lower := (rows 25 98 133 41 336 36 64 128 256), losses := [] }

theorem u18978 : Upper (D 6) (R 6) [24,96,129,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18979 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 133 44 84 33 322 386 258), lower := (rows 25 98 133 44 84 33 64 128 256), losses := [] }

theorem u18979 : Upper (D 6) (R 6) [24,96,129,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18980 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 42, targets := 1 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 25 98 133 44 84 34 323 387 259), lower := (rows 25 98 133 44 84 34 64 128 256), losses := [] }

theorem u18980 : Upper (D 6) (R 6) [24,96,129,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m18981_1 : Upper (D 6) (R 6) [24,96,129,36,68,256,1] 13 :=
  permutation_upper _ _ _ [24,96,129,36,68,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5615

theorem m18981_2 : Upper (D 6) (R 6) [24,96,129,36,68,256,2] 13 :=
  permutation_upper _ _ _ [24,96,129,36,68,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5616

def r18981 : Route 9 := (fun mask => (mask,id))

def c18981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18981 : Upper (D 6) (R 6) [24,96,129,36,68,256] 13 := by
  apply FastRouting.sound _ _ [24,96,129,36,68,256] 13 (by decide) (choices 1) [1,2] r18981 c18981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m18981_1
  · exact m18981_2

def b18982 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 25 98 133 44 273 34 70 198 326), lower := (rows 25 98 133 44 273 34 64 128 256), losses := [] }

theorem u18982 : Upper (D 6) (R 6) [24,96,129,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18983 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 98 133 44 273 36 66 194 322), lower := (rows 25 98 133 44 273 36 64 128 256), losses := [] }

theorem u18983 : Upper (D 6) (R 6) [24,96,129,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18984 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 44 273 96 70 134 262), lower := (rows 25 98 133 44 273 96 64 128 256), losses := [] }

theorem u18984 : Upper (D 6) (R 6) [24,96,129,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18985 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 40, targets := 66 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 25 98 133 44 274 33 70 198 326), lower := (rows 25 98 133 44 274 33 64 128 256), losses := [] }

theorem u18985 : Upper (D 6) (R 6) [24,96,129,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18986 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 98 133 44 274 34 69 197 325), lower := (rows 25 98 133 44 274 34 64 128 256), losses := [] }

theorem u18986 : Upper (D 6) (R 6) [24,96,129,36,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18987 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 98 133 44 274 36 67 195 323), lower := (rows 25 98 133 44 274 36 64 128 256), losses := [] }

theorem u18987 : Upper (D 6) (R 6) [24,96,129,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18988 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 44 274 96 71 135 263), lower := (rows 25 98 133 44 274 96 64 128 256), losses := [] }

theorem u18988 : Upper (D 6) (R 6) [24,96,129,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18989 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 133 44 276 33 66 194 322), lower := (rows 25 98 133 44 276 33 64 128 256), losses := [] }

theorem u18989 : Upper (D 6) (R 6) [24,96,129,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18990 : Route 9 := (fun mask => (mask,id))

def c18990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18990 : Upper (D 6) (R 6) [24,96,129,36,260,2] 13 := by
  apply FastRouting.sound _ _ [24,96,129,36,260,2] 13 (by decide) (choices 1) [1,2] r18990 c18990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5617
  · exact u5618

def b18991 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 133 44 276 96 67 131 259), lower := (rows 25 98 133 44 276 96 64 128 256), losses := [] }

theorem u18991 : Upper (D 6) (R 6) [24,96,129,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18992 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 40, targets := 66 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 25 98 133 44 336 33 70 134 262), lower := (rows 25 98 133 44 336 33 64 128 256), losses := [] }

theorem u18992 : Upper (D 6) (R 6) [24,96,129,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18993 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 25 98 133 44 336 34 71 135 263), lower := (rows 25 98 133 44 336 34 64 128 256), losses := [{ target := 0, region := (rows 0 82 4 12 16 115 64 128 256), good := (rows 58 98 172 44 370 34 98 128 256) }] }

theorem u18993 : Upper (D 6) (R 6) [24,96,129,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18994 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 98 133 44 336 36 67 131 259), lower := (rows 25 98 133 44 336 36 64 128 256), losses := [] }

theorem u18994 : Upper (D 6) (R 6) [24,96,129,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18995 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 98 134 11 52 33 324 452 324), lower := (rows 25 98 134 11 52 33 64 128 256), losses := [] }

theorem u18995 : Upper (D 6) (R 6) [24,96,130,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18996 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 98 134 11 52 36 321 449 321), lower := (rows 25 98 134 11 52 36 64 128 256), losses := [] }

theorem u18996 : Upper (D 6) (R 6) [24,96,130,3,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18997 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 11 52 96 325 389 261), lower := (rows 25 98 134 11 52 96 64 128 256), losses := [] }

theorem u18997 : Upper (D 6) (R 6) [24,96,130,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18998 : Route 9 := (fun mask => (mask,id))

def c18998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18998 : Upper (D 6) (R 6) [24,96,130,3,36,256] 13 := by
  apply FastRouting.sound _ _ [24,96,130,3,36,256] 13 (by decide) (choices 1) [1,4] r18998 c18998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5619
  · exact u5620

def r18999 : Route 9 := (fun mask => (mask,id))

def c18999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18999 : Upper (D 6) (R 6) [24,96,130,3,257,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,3,257,4] 13 (by decide) (choices 1) [4,32] r18999 c18999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5621
  · exact u5622

def b19000 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 11 273 96 100 164 292), lower := (rows 25 98 134 11 273 96 64 128 256), losses := [] }

theorem u19000 : Upper (D 6) (R 6) [24,96,130,3,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19001 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 11 276 33 100 228 356), lower := (rows 25 98 134 11 276 33 64 128 256), losses := [] }

theorem u19001 : Upper (D 6) (R 6) [24,96,130,3,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19002_1 : Upper (D 6) (R 6) [24,96,130,3,260,4,1] 13 :=
  permutation_upper _ _ _ [24,96,130,3,260,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5623

def r19002 : Route 9 := (fun mask => (mask,id))

def c19002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19002 : Upper (D 6) (R 6) [24,96,130,3,260,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,3,260,4] 13 (by decide) (choices 1) [1,32] r19002 c19002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m19002_1
  · exact u5624

def b19003 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 11 276 96 101 165 293), lower := (rows 25 98 134 11 276 96 64 128 256), losses := [] }

theorem u19003 : Upper (D 6) (R 6) [24,96,130,3,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19004 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 11 304 33 68 196 324), lower := (rows 25 98 134 11 304 33 64 128 256), losses := [] }

theorem u19004 : Upper (D 6) (R 6) [24,96,130,3,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19005 : Route 9 := (fun mask => (mask,id))

def c19005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19005 : Upper (D 6) (R 6) [24,96,130,3,288,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,3,288,4] 13 (by decide) (choices 1) [1,4] r19005 c19005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5625
  · exact u5626

def b19006 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 11 304 96 69 133 261), lower := (rows 25 98 134 11 304 96 64 128 256), losses := [] }

theorem u19006 : Upper (D 6) (R 6) [24,96,130,3,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19007 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 134 13 273 34 100 228 356), lower := (rows 25 98 134 13 273 34 64 128 256), losses := [] }

theorem u19007 : Upper (D 6) (R 6) [24,96,130,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19008 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 5, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 134 13 273 36 98 226 354), lower := (rows 25 98 134 13 273 36 64 128 256), losses := [] }

theorem u19008 : Upper (D 6) (R 6) [24,96,130,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19009 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 13 273 96 102 166 294), lower := (rows 25 98 134 13 273 96 64 128 256), losses := [] }

theorem u19009 : Upper (D 6) (R 6) [24,96,130,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19010 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 13 274 33 100 228 356), lower := (rows 25 98 134 13 274 33 64 128 256), losses := [] }

theorem u19010 : Upper (D 6) (R 6) [24,96,130,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19011_1 : Upper (D 6) (R 6) [24,96,130,5,258,4,1] 13 :=
  permutation_upper _ _ _ [24,96,130,5,258,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5627

def r19011 : Route 9 := (fun mask => (mask,id))

def c19011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19011 : Upper (D 6) (R 6) [24,96,130,5,258,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,5,258,4] 13 (by decide) (choices 1) [1,32] r19011 c19011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m19011_1
  · exact u5628

def b19012 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 13 274 96 101 165 293), lower := (rows 25 98 134 13 274 96 64 128 256), losses := [] }

theorem u19012 : Upper (D 6) (R 6) [24,96,130,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19013 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 13 304 33 70 198 326), lower := (rows 25 98 134 13 304 33 64 128 256), losses := [] }

theorem u19013 : Upper (D 6) (R 6) [24,96,130,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19014 : Route 9 := (fun mask => (mask,id))

def c19014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19014 : Upper (D 6) (R 6) [24,96,130,5,288,2] 13 := by
  apply FastRouting.sound _ _ [24,96,130,5,288,2] 13 (by decide) (choices 1) [1,4] r19014 c19014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5629
  · exact u5630

def r19015 : Route 9 := (fun mask => (mask,id))

def c19015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19015 : Upper (D 6) (R 6) [24,96,130,5,288,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,5,288,4] 13 (by decide) (choices 1) [1,2] r19015 c19015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5631
  · exact u5632

def b19016 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 13 304 96 71 135 263), lower := (rows 25 98 134 13 304 96 64 128 256), losses := [] }

theorem u19016 : Upper (D 6) (R 6) [24,96,130,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19017 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 98 134 41 84 33 326 390 262), lower := (rows 25 98 134 41 84 33 64 128 256), losses := [] }

theorem u19017 : Upper (D 6) (R 6) [24,96,130,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19018 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 134 41 84 34 325 389 261), lower := (rows 25 98 134 41 84 34 64 128 256), losses := [] }

theorem u19018 : Upper (D 6) (R 6) [24,96,130,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19019 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 134 41 84 36 323 387 259), lower := (rows 25 98 134 41 84 36 64 128 256), losses := [] }

theorem u19019 : Upper (D 6) (R 6) [24,96,130,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19019
end Delivery.IrregularNine14.P06
