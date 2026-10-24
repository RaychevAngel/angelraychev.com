import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0141

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27000 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 146 292 76 22 96 67 131 259), lower := (rows 41 146 292 76 22 96 64 128 256), losses := [] }

theorem u27000 : Upper (D 6) (R 6) [40,144,288,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27001 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 146 292 76 81 33 70 134 262), lower := (rows 41 146 292 76 81 33 64 128 256), losses := [] }

theorem u27001 : Upper (D 6) (R 6) [40,144,288,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27002 : Route 9 := (fun mask => (mask,id))

def c27002 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27002 : Upper (D 6) (R 6) [40,144,288,68,65,2] 13 := by
  apply FastRouting.sound _ _ [40,144,288,68,65,2] 13 (by decide) (choices 1) [1,2,4] r27002 c27002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8482
  · exact u8483
  · exact u8484

def b27003 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 146 292 76 81 36 67 131 259), lower := (rows 41 146 292 76 81 36 64 128 256), losses := [] }

theorem u27003 : Upper (D 6) (R 6) [40,144,288,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27004 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 292 76 82 33 71 135 263), lower := (rows 41 146 292 76 82 33 64 128 256), losses := [] }

theorem u27004 : Upper (D 6) (R 6) [40,144,288,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27005 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 292 76 82 34 69 133 261), lower := (rows 41 146 292 76 82 34 64 128 256), losses := [] }

theorem u27005 : Upper (D 6) (R 6) [40,144,288,68,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27006 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 146 292 76 82 36 67 131 259), lower := (rows 41 146 292 76 82 36 64 128 256), losses := [] }

theorem u27006 : Upper (D 6) (R 6) [40,144,288,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27007 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 21 34 100 228 356), lower := (rows 41 146 324 11 21 34 64 128 256), losses := [] }

theorem u27007 : Upper (D 6) (R 6) [40,144,320,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27008 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(0,6),(1,0),(2,0)], upper := (rows 41 146 324 11 21 36 98 226 354), lower := (rows 41 146 324 11 21 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 10 16 52 0 128 256), good := (rows 41 187 292 11 53 36 0 128 256) }] }

theorem u27008 : Upper (D 6) (R 6) [40,144,320,3,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27009 : Route 9 := (fun mask => (mask,id))

def c27009 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27009 : Upper (D 6) (R 6) [40,144,320,3,5,64] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,5,64] 13 (by decide) (choices 1) [2,4,32] r27009 c27009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8485
  · exact u8486
  · exact u8487

def b27010 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 22 33 100 228 356), lower := (rows 41 146 324 11 22 33 64 128 256), losses := [] }

theorem u27010 : Upper (D 6) (R 6) [40,144,320,3,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27011 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 146 324 11 22 36 97 225 353), lower := (rows 41 146 324 11 22 36 64 128 256), losses := [] }

theorem u27011 : Upper (D 6) (R 6) [40,144,320,3,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27012 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 357, targets := 2 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 146 324 11 22 96 101 165 293), lower := (rows 41 146 324 11 22 96 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 26 16 100 64 128 256), good := (rows 41 155 352 11 59 96 96 128 256) }] }

theorem u27012 : Upper (D 6) (R 6) [40,144,320,3,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27013 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 52 33 70 198 326), lower := (rows 41 146 324 11 52 33 64 128 256), losses := [] }

theorem u27013 : Upper (D 6) (R 6) [40,144,320,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27014 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 52 34 69 197 325), lower := (rows 41 146 324 11 52 34 64 128 256), losses := [] }

theorem u27014 : Upper (D 6) (R 6) [40,144,320,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27015 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 146 324 11 52 36 67 195 323), lower := (rows 41 146 324 11 52 36 64 128 256), losses := [] }

theorem u27015 : Upper (D 6) (R 6) [40,144,320,3,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27016 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 146 324 11 52 96 71 135 263), lower := (rows 41 146 324 11 52 96 64 128 256), losses := [] }

theorem u27016 : Upper (D 6) (R 6) [40,144,320,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27017 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 81 34 100 164 292), lower := (rows 41 146 324 11 81 34 64 128 256), losses := [] }

theorem u27017 : Upper (D 6) (R 6) [40,144,320,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27018 : Route 9 := (fun mask => (mask,id))

def c27018 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27018 : Upper (D 6) (R 6) [40,144,320,3,65,4] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,65,4] 13 (by decide) (choices 1) [2,4,32] r27018 c27018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8488
  · exact u8489
  · exact u8490

def b27019 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 82 33 100 164 292), lower := (rows 41 146 324 11 82 33 64 128 256), losses := [] }

theorem u27019 : Upper (D 6) (R 6) [40,144,320,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27020 : Route 9 := (fun mask => (mask,id))

def c27020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27020 : Upper (D 6) (R 6) [40,144,320,3,66,4] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,66,4] 13 (by decide) (choices 1) [1,4,32] r27020 c27020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8491
  · exact u8492
  · exact u8493

def b27021 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 112 33 70 134 262), lower := (rows 41 146 324 11 112 33 64 128 256), losses := [] }

theorem u27021 : Upper (D 6) (R 6) [40,144,320,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27022 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 112 34 69 133 261), lower := (rows 41 146 324 11 112 34 64 128 256), losses := [] }

theorem u27022 : Upper (D 6) (R 6) [40,144,320,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27023 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 41 146 324 11 112 36 71 135 263), lower := (rows 41 146 324 11 112 36 64 128 256), losses := [] }

theorem u27023 : Upper (D 6) (R 6) [40,144,320,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27024 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 324 13 19 34 100 228 356), lower := (rows 41 146 324 13 19 34 64 128 256), losses := [] }

theorem u27024 : Upper (D 6) (R 6) [40,144,320,5,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27025 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 19 36 98 226 354), lower := (rows 41 146 324 13 19 36 64 128 256), losses := [] }

theorem u27025 : Upper (D 6) (R 6) [40,144,320,5,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27026 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 41, targets := 2 },{ cop := 4, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 41 146 324 13 19 96 102 166 294), lower := (rows 41 146 324 13 19 96 64 128 256), losses := [] }

theorem u27026 : Upper (D 6) (R 6) [40,144,320,5,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27027 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 22 33 98 226 354), lower := (rows 41 146 324 13 22 33 64 128 256), losses := [] }

theorem u27027 : Upper (D 6) (R 6) [40,144,320,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27028 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 324 13 22 34 97 225 353), lower := (rows 41 146 324 13 22 34 64 128 256), losses := [] }

theorem u27028 : Upper (D 6) (R 6) [40,144,320,5,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27029 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 146 324 13 22 96 99 163 291), lower := (rows 41 146 324 13 22 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 100 64 128 256), good := (rows 41 146 352 41 50 96 96 128 256) }] }

theorem u27029 : Upper (D 6) (R 6) [40,144,320,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27030 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 50 33 70 198 326), lower := (rows 41 146 324 13 50 33 64 128 256), losses := [] }

theorem u27030 : Upper (D 6) (R 6) [40,144,320,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27031 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 50, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 146 324 13 50 34 69 197 325), lower := (rows 41 146 324 13 50 34 64 128 256), losses := [] }

theorem u27031 : Upper (D 6) (R 6) [40,144,320,5,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27032 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 50 36 67 195 323), lower := (rows 41 146 324 13 50 36 64 128 256), losses := [] }

theorem u27032 : Upper (D 6) (R 6) [40,144,320,5,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27033 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 146 324 13 50 96 71 135 263), lower := (rows 41 146 324 13 50 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 100 64 128 256), good := (rows 41 146 352 41 50 96 96 128 256) }] }

theorem u27033 : Upper (D 6) (R 6) [40,144,320,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27034 : Route 9 := (fun mask => (mask,id))

def c27034 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27034 : Upper (D 6) (R 6) [40,144,320,5,65,2] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5,65,2] 13 (by decide) (choices 1) [2,4,32] r27034 c27034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8494
  · exact u8495
  · exact u8496

def b27035 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 81 36 98 162 290), lower := (rows 41 146 324 13 81 36 64 128 256), losses := [] }

theorem u27035 : Upper (D 6) (R 6) [40,144,320,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27036 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 82 33 102 166 294), lower := (rows 41 146 324 13 82 33 64 128 256), losses := [] }

theorem u27036 : Upper (D 6) (R 6) [40,144,320,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27037 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 324 13 82 34 101 165 293), lower := (rows 41 146 324 13 82 34 64 128 256), losses := [] }

theorem u27037 : Upper (D 6) (R 6) [40,144,320,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27038 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 82 36 99 163 291), lower := (rows 41 146 324 13 82 36 64 128 256), losses := [] }

theorem u27038 : Upper (D 6) (R 6) [40,144,320,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27039 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 146 324 13 112 33 70 134 262), lower := (rows 41 146 324 13 112 33 64 128 256), losses := [] }

theorem u27039 : Upper (D 6) (R 6) [40,144,320,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27040 : Route 9 := (fun mask => (mask,id))

def c27040 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27040 : Upper (D 6) (R 6) [40,144,320,5,96,2] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5,96,2] 13 (by decide) (choices 1) [1,2,4] r27040 c27040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8497
  · exact u8498
  · exact u8499

def b27041 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 112 36 67 131 259), lower := (rows 41 146 324 13 112 36 64 128 256), losses := [] }

theorem u27041 : Upper (D 6) (R 6) [40,144,320,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27042 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 146 324 14 19 33 100 228 356), lower := (rows 41 146 324 14 19 33 64 128 256), losses := [] }

theorem u27042 : Upper (D 6) (R 6) [40,144,320,6,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27043 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 146 324 14 19 36 97 225 353), lower := (rows 41 146 324 14 19 36 64 128 256), losses := [] }

theorem u27043 : Upper (D 6) (R 6) [40,144,320,6,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27044 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 357, targets := 2 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 146 324 14 19 96 101 165 293), lower := (rows 41 146 324 14 19 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 24 100 64 128 256), good := (rows 57 146 352 59 19 96 96 128 256) }] }

theorem u27044 : Upper (D 6) (R 6) [40,144,320,6,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27045 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 146 324 14 21 33 98 226 354), lower := (rows 41 146 324 14 21 33 64 128 256), losses := [] }

theorem u27045 : Upper (D 6) (R 6) [40,144,320,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27046 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 41 146 324 14 21 34 97 225 353), lower := (rows 41 146 324 14 21 34 64 128 256), losses := [] }

theorem u27046 : Upper (D 6) (R 6) [40,144,320,6,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27047 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 97, targets := 4 },{ cop := 4, region := 226, targets := 4 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 41 146 324 14 21 96 99 163 291), lower := (rows 41 146 324 14 21 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 100 64 128 256), good := (rows 57 144 356 61 53 96 96 128 256) }] }

theorem u27047 : Upper (D 6) (R 6) [40,144,320,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27048 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 146 324 14 52 33 67 195 323), lower := (rows 41 146 324 14 52 33 64 128 256), losses := [] }

theorem u27048 : Upper (D 6) (R 6) [40,144,320,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27049 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 41 146 324 14 52 34 65 193 321), lower := (rows 41 146 324 14 52 34 64 128 256), losses := [] }

theorem u27049 : Upper (D 6) (R 6) [40,144,320,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27050 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 146 324 14 52 96 67 131 259), lower := (rows 41 146 324 14 52 96 64 128 256), losses := [] }

theorem u27050 : Upper (D 6) (R 6) [40,144,320,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27051 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 324 14 81 33 102 166 294), lower := (rows 41 146 324 14 81 33 64 128 256), losses := [] }

theorem u27051 : Upper (D 6) (R 6) [40,144,320,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27052 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 146 324 14 81 34 101 165 293), lower := (rows 41 146 324 14 81 34 64 128 256), losses := [] }

theorem u27052 : Upper (D 6) (R 6) [40,144,320,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27053 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 146 324 14 81 36 99 163 291), lower := (rows 41 146 324 14 81 36 64 128 256), losses := [] }

theorem u27053 : Upper (D 6) (R 6) [40,144,320,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27054 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 324 14 112 33 71 135 263), lower := (rows 41 146 324 14 112 33 64 128 256), losses := [] }

theorem u27054 : Upper (D 6) (R 6) [40,144,320,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27055 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 146 324 14 112 34 69 133 261), lower := (rows 41 146 324 14 112 34 64 128 256), losses := [] }

theorem u27055 : Upper (D 6) (R 6) [40,144,320,6,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27056 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 41 146 324 14 112 36 67 131 259), lower := (rows 41 146 324 14 112 36 64 128 256), losses := [] }

theorem u27056 : Upper (D 6) (R 6) [40,144,320,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27057 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 324 73 19 34 100 164 292), lower := (rows 41 146 324 73 19 34 64 128 256), losses := [] }

theorem u27057 : Upper (D 6) (R 6) [40,144,320,65,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27058 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 41, targets := 2 },{ cop := 4, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 41 146 324 73 19 36 102 166 294), lower := (rows 41 146 324 73 19 36 64 128 256), losses := [] }

theorem u27058 : Upper (D 6) (R 6) [40,144,320,65,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27059 : PairBound 9 := { available := 38, camps := [{ cop := 6, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 146 324 73 22 33 102 166 294), lower := (rows 41 146 324 73 22 33 64 128 256), losses := [] }

theorem u27059 : Upper (D 6) (R 6) [40,144,320,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27059
end Delivery.IrregularNine14.P06
