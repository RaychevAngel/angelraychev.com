import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0057

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15000 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 13 276 96 99 163 291), lower := (rows 11 98 148 13 276 96 64 128 256), losses := [] }

theorem u15000 : Upper (D 6) (R 6) [10,96,144,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15001 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 304 33 70 198 326), lower := (rows 11 98 148 13 304 33 64 128 256), losses := [] }

theorem u15001 : Upper (D 6) (R 6) [10,96,144,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15002 : Route 9 := (fun mask => (mask,id))

def c15002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15002 : Upper (D 6) (R 6) [10,96,144,5,288,2] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,288,2] 13 (by decide) (choices 1) [1,4] r15002 c15002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3422
  · exact u3423

def r15003 : Route 9 := (fun mask => (mask,id))

def c15003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15003 : Upper (D 6) (R 6) [10,96,144,5,288,4] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,288,4] 13 (by decide) (choices 1) [1,2] r15003 c15003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3424
  · exact u3425

def b15004 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 13 304 96 71 135 263), lower := (rows 11 98 148 13 304 96 64 128 256), losses := [] }

theorem u15004 : Upper (D 6) (R 6) [10,96,144,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15005 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 322, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 148 44 81 33 326 390 262), lower := (rows 11 98 148 44 81 33 64 128 256), losses := [] }

theorem u15005 : Upper (D 6) (R 6) [10,96,144,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15006 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 148 44 81 34 325 389 261), lower := (rows 11 98 148 44 81 34 64 128 256), losses := [] }

theorem u15006 : Upper (D 6) (R 6) [10,96,144,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15007 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 148 44 81 36 323 387 259), lower := (rows 11 98 148 44 81 36 64 128 256), losses := [] }

theorem u15007 : Upper (D 6) (R 6) [10,96,144,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15008 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 148 44 81 288 71 135 263), lower := (rows 11 98 148 44 81 288 64 128 256), losses := [] }

theorem u15008 : Upper (D 6) (R 6) [10,96,144,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15008 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15009 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 148 44 273 33 70 198 326), lower := (rows 11 98 148 44 273 33 64 128 256), losses := [] }

theorem u15009 : Upper (D 6) (R 6) [10,96,144,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15010 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 148 44 273 34 69 197 325), lower := (rows 11 98 148 44 273 34 64 128 256), losses := [] }

theorem u15010 : Upper (D 6) (R 6) [10,96,144,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15011 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 148 44 273 36 67 195 323), lower := (rows 11 98 148 44 273 36 64 128 256), losses := [] }

theorem u15011 : Upper (D 6) (R 6) [10,96,144,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15012 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 44 273 96 71 135 263), lower := (rows 11 98 148 44 273 96 64 128 256), losses := [] }

theorem u15012 : Upper (D 6) (R 6) [10,96,144,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15013 : Route 9 := (fun mask => (mask,id))

def c15013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15013 : Upper (D 6) (R 6) [10,96,144,36,258,1] 13 := by
  apply FastRouting.sound _ _ [10,96,144,36,258,1] 13 (by decide) (choices 1) [1,4] r15013 c15013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3426
  · exact u3427

def b15014 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 148 44 274 36 65 193 321), lower := (rows 11 98 148 44 274 36 64 128 256), losses := [] }

theorem u15014 : Upper (D 6) (R 6) [10,96,144,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15015 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 44 274 96 69 133 261), lower := (rows 11 98 148 44 274 96 64 128 256), losses := [] }

theorem u15015 : Upper (D 6) (R 6) [10,96,144,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15016 : Route 9 := (fun mask => (mask,id))

def c15016 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15016 : Upper (D 6) (R 6) [10,96,144,36,320,1] 13 := by
  apply FastRouting.sound _ _ [10,96,144,36,320,1] 13 (by decide) (choices 1) [1,2,4] r15016 c15016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3428
  · exact u3429
  · exact u3430

def b15017 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 148 44 336 34 69 133 261), lower := (rows 11 98 148 44 336 34 64 128 256), losses := [] }

theorem u15017 : Upper (D 6) (R 6) [10,96,144,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15018 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 148 44 336 36 67 131 259), lower := (rows 11 98 148 44 336 36 64 128 256), losses := [] }

theorem u15018 : Upper (D 6) (R 6) [10,96,144,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15019 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 148 265 21 34 100 228 356), lower := (rows 11 98 148 265 21 34 64 128 256), losses := [] }

theorem u15019 : Upper (D 6) (R 6) [10,96,144,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15020 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 265 21 36 98 226 354), lower := (rows 11 98 148 265 21 36 64 128 256), losses := [] }

theorem u15020 : Upper (D 6) (R 6) [10,96,144,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15021 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 265 21 96 102 166 294), lower := (rows 11 98 148 265 21 96 64 128 256), losses := [] }

theorem u15021 : Upper (D 6) (R 6) [10,96,144,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15022 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 265 22 33 100 228 356), lower := (rows 11 98 148 265 22 33 64 128 256), losses := [] }

theorem u15022 : Upper (D 6) (R 6) [10,96,144,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15023 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 265 22 36 97 225 353), lower := (rows 11 98 148 265 22 36 64 128 256), losses := [] }

theorem u15023 : Upper (D 6) (R 6) [10,96,144,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15024 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 265 22 96 101 165 293), lower := (rows 11 98 148 265 22 96 64 128 256), losses := [] }

theorem u15024 : Upper (D 6) (R 6) [10,96,144,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15025 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 98 148 265 49 34 68 196 324), lower := (rows 11 98 148 265 49 34 64 128 256), losses := [] }

theorem u15025 : Upper (D 6) (R 6) [10,96,144,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15026 : Route 9 := (fun mask => (mask,id))

def c15026 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15026 : Upper (D 6) (R 6) [10,96,144,257,33,4] 13 := by
  apply FastRouting.sound _ _ [10,96,144,257,33,4] 13 (by decide) (choices 1) [2,4] r15026 c15026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3431
  · exact u3432

def b15027 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 265 49 96 70 134 262), lower := (rows 11 98 148 265 49 96 64 128 256), losses := [] }

theorem u15027 : Upper (D 6) (R 6) [10,96,144,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15028 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 265 52 33 70 198 326), lower := (rows 11 98 148 265 52 33 64 128 256), losses := [] }

theorem u15028 : Upper (D 6) (R 6) [10,96,144,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15029 : Route 9 := (fun mask => (mask,id))

def c15029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15029 : Upper (D 6) (R 6) [10,96,144,257,36,2] 13 := by
  apply FastRouting.sound _ _ [10,96,144,257,36,2] 13 (by decide) (choices 1) [1,4] r15029 c15029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3433
  · exact u3434

def b15030 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 148 265 52 36 67 195 323), lower := (rows 11 98 148 265 52 36 64 128 256), losses := [] }

theorem u15030 : Upper (D 6) (R 6) [10,96,144,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15031 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 265 52 96 71 135 263), lower := (rows 11 98 148 265 52 96 64 128 256), losses := [] }

theorem u15031 : Upper (D 6) (R 6) [10,96,144,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15032 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 148 268 21 33 98 226 354), lower := (rows 11 98 148 268 21 33 64 128 256), losses := [] }

theorem u15032 : Upper (D 6) (R 6) [10,96,144,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15033 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 148 268 21 34 97 225 353), lower := (rows 11 98 148 268 21 34 64 128 256), losses := [] }

theorem u15033 : Upper (D 6) (R 6) [10,96,144,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15034 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 268 21 96 99 163 291), lower := (rows 11 98 148 268 21 96 64 128 256), losses := [] }

theorem u15034 : Upper (D 6) (R 6) [10,96,144,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15035 : Route 9 := (fun mask => (mask,id))

def c15035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15035 : Upper (D 6) (R 6) [10,96,144,260,6,1] 13 := by
  apply FastRouting.sound _ _ [10,96,144,260,6,1] 13 (by decide) (choices 1) [1,32] r15035 c15035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3435
  · exact u3436

def b15036 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 268 22 96 97 161 289), lower := (rows 11 98 148 268 22 96 64 128 256), losses := [] }

theorem u15036 : Upper (D 6) (R 6) [10,96,144,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15037 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 98 148 268 49 33 70 198 326), lower := (rows 11 98 148 268 49 33 64 128 256), losses := [] }

theorem u15037 : Upper (D 6) (R 6) [10,96,144,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15038 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 98 148 268 49 34 69 197 325), lower := (rows 11 98 148 268 49 34 64 128 256), losses := [] }

theorem u15038 : Upper (D 6) (R 6) [10,96,144,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15039 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2),(2,5),(4,1)], upper := (rows 11 98 148 268 49 36 67 195 323), lower := (rows 11 98 148 268 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 64 128 256), good := (rows 57 96 180 300 49 36 64 128 256) },{ target := 5, region := (rows 1 2 20 24 16 0 65 129 257), good := (rows 459 66 156 268 477 4 64 128 256) }] }

theorem u15039 : Upper (D 6) (R 6) [10,96,144,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15040 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 268 49 96 71 135 263), lower := (rows 11 98 148 268 49 96 64 128 256), losses := [] }

theorem u15040 : Upper (D 6) (R 6) [10,96,144,260,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15041 : Route 9 := (fun mask => (mask,id))

def c15041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15041 : Upper (D 6) (R 6) [10,96,144,260,36,1] 13 := by
  apply FastRouting.sound _ _ [10,96,144,260,36,1] 13 (by decide) (choices 1) [1,2] r15041 c15041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3437
  · exact u3438

def b15042 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 148 268 52 34 65 193 321), lower := (rows 11 98 148 268 52 34 64 128 256), losses := [] }

theorem u15042 : Upper (D 6) (R 6) [10,96,144,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15043 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 268 52 96 67 131 259), lower := (rows 11 98 148 268 52 96 64 128 256), losses := [] }

theorem u15043 : Upper (D 6) (R 6) [10,96,144,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15044 : Route 9 := (fun mask => (mask,id))

def c15044 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15044 : Upper (D 6) (R 6) [10,96,144,288,5,1] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288,5,1] 13 (by decide) (choices 1) [2,4] r15044 c15044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3439
  · exact u3440

def b15045 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 148 296 21 34 69 197 325), lower := (rows 11 98 148 296 21 34 64 128 256), losses := [] }

theorem u15045 : Upper (D 6) (R 6) [10,96,144,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15046 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 296 21 36 67 195 323), lower := (rows 11 98 148 296 21 36 64 128 256), losses := [] }

theorem u15046 : Upper (D 6) (R 6) [10,96,144,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15047 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 296 21 96 71 135 263), lower := (rows 11 98 148 296 21 96 64 128 256), losses := [] }

theorem u15047 : Upper (D 6) (R 6) [10,96,144,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15048 : Route 9 := (fun mask => (mask,id))

def c15048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15048 : Upper (D 6) (R 6) [10,96,144,288,6,1] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288,6,1] 13 (by decide) (choices 1) [1,4] r15048 c15048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3441
  · exact u3442

def b15049 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 296 22 36 65 193 321), lower := (rows 11 98 148 296 22 36 64 128 256), losses := [] }

theorem u15049 : Upper (D 6) (R 6) [10,96,144,288,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15050 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 296 22 96 69 133 261), lower := (rows 11 98 148 296 22 96 64 128 256), losses := [] }

theorem u15050 : Upper (D 6) (R 6) [10,96,144,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15051 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 98 148 296 81 33 70 134 262), lower := (rows 11 98 148 296 81 33 64 128 256), losses := [] }

theorem u15051 : Upper (D 6) (R 6) [10,96,144,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15052 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 148 296 81 34 69 133 261), lower := (rows 11 98 148 296 81 34 64 128 256), losses := [] }

theorem u15052 : Upper (D 6) (R 6) [10,96,144,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15053 : Route 9 := (fun mask => (mask,id))

def c15053 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15053 : Upper (D 6) (R 6) [10,96,144,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288,65,4] 13 (by decide) (choices 1) [1,2,4] r15053 c15053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3443
  · exact u3444
  · exact u3445

def r15054 : Route 9 := (fun mask => (mask,id))

def c15054 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15054 : Upper (D 6) (R 6) [10,96,144,288,68,1] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288,68,1] 13 (by decide) (choices 1) [1,2,4] r15054 c15054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3446
  · exact u3447
  · exact u3448

def b15055 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 148 296 84 34 69 133 261), lower := (rows 11 98 148 296 84 34 64 128 256), losses := [] }

theorem u15055 : Upper (D 6) (R 6) [10,96,144,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15056 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 296 84 36 67 131 259), lower := (rows 11 98 148 296 84 36 64 128 256), losses := [] }

theorem u15056 : Upper (D 6) (R 6) [10,96,144,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15057 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 336, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 164 13 81 34 340 404 276), lower := (rows 11 98 164 13 81 34 64 128 256), losses := [] }

theorem u15057 : Upper (D 6) (R 6) [10,96,160,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15058 : PairBound 9 := { available := 274, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 164 13 81 36 338 402 274), lower := (rows 11 98 164 13 81 36 64 128 256), losses := [] }

theorem u15058 : Upper (D 6) (R 6) [10,96,160,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15059 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 13 81 48 326 390 262), lower := (rows 11 98 164 13 81 48 64 128 256), losses := [] }

theorem u15059 : Upper (D 6) (R 6) [10,96,160,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15059 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15059
end Delivery.IrregularNine14.P06
