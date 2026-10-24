import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0036

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12000 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 52 140 273 36 66 194 322), lower := (rows 11 35 52 140 273 36 64 128 256), losses := [] }

theorem u12000 : Upper (D 6) (R 6) [10,33,48,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12001 : Route 9 := (fun mask => (mask,id))

def c12001 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12001 : Upper (D 6) (R 6) [10,33,48,132,257,64] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,257,64] 13 (by decide) (choices 1) [2,4] r12001 c12001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2162
  · exact u2163

def b12002 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 140 274 33 68 196 324), lower := (rows 11 35 52 140 274 33 64 128 256), losses := [] }

theorem u12002 : Upper (D 6) (R 6) [10,33,48,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12003 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 140 274 36 65 193 321), lower := (rows 11 35 52 140 274 36 64 128 256), losses := [] }

theorem u12003 : Upper (D 6) (R 6) [10,33,48,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12004 : Route 9 := (fun mask => (mask,id))

def c12004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12004 : Upper (D 6) (R 6) [10,33,48,132,258,64] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,258,64] 13 (by decide) (choices 1) [1,4] r12004 c12004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2164
  · exact u2165

def b12005 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 52 140 276 33 66 194 322), lower := (rows 11 35 52 140 276 33 64 128 256), losses := [] }

theorem u12005 : Upper (D 6) (R 6) [10,33,48,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12006 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 52 140 276 34 65 193 321), lower := (rows 11 35 52 140 276 34 64 128 256), losses := [] }

theorem u12006 : Upper (D 6) (R 6) [10,33,48,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12007 : Route 9 := (fun mask => (mask,id))

def c12007 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12007 : Upper (D 6) (R 6) [10,33,48,132,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,260,64] 13 (by decide) (choices 1) [1,2] r12007 c12007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2166
  · exact u2167

def b12008 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 140 336 33 70 198 326), lower := (rows 11 35 52 140 336 33 64 128 256), losses := [] }

theorem u12008 : Upper (D 6) (R 6) [10,33,48,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12009 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 140 336 34 69 197 325), lower := (rows 11 35 52 140 336 34 64 128 256), losses := [] }

theorem u12009 : Upper (D 6) (R 6) [10,33,48,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12010 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 140 336 36 67 195 323), lower := (rows 11 35 52 140 336 36 64 128 256), losses := [] }

theorem u12010 : Upper (D 6) (R 6) [10,33,48,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12011 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 52 140 336 96 71 135 263), lower := (rows 11 35 52 140 336 96 64 128 256), losses := [] }

theorem u12011 : Upper (D 6) (R 6) [10,33,48,132,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12012 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 52 200 81 34 324 388 260), lower := (rows 11 35 52 200 81 34 64 128 256), losses := [] }

theorem u12012 : Upper (D 6) (R 6) [10,33,48,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12013 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 35 52 200 81 36 326 390 262), lower := (rows 11 35 52 200 81 36 64 128 256), losses := [] }

theorem u12013 : Upper (D 6) (R 6) [10,33,48,192,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12014 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 294, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 35 52 200 81 288 70 134 262), lower := (rows 11 35 52 200 81 288 64 128 256), losses := [] }

theorem u12014 : Upper (D 6) (R 6) [10,33,48,192,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12014 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12015 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 52 200 82 33 324 388 260), lower := (rows 11 35 52 200 82 33 64 128 256), losses := [] }

theorem u12015 : Upper (D 6) (R 6) [10,33,48,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12016 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 200 82 36 325 389 261), lower := (rows 11 35 52 200 82 36 64 128 256), losses := [] }

theorem u12016 : Upper (D 6) (R 6) [10,33,48,192,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12017 : Route 9 := (fun mask => (mask,id))

def c12017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12017 : Upper (D 6) (R 6) [10,33,48,192,66,256] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,66,256] 13 (by decide) (choices 1) [1,4] r12017 c12017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2168
  · exact u2169

def b12018 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 200 84 33 326 390 262), lower := (rows 11 35 52 200 84 33 64 128 256), losses := [] }

theorem u12018 : Upper (D 6) (R 6) [10,33,48,192,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12019 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 200 84 34 325 389 261), lower := (rows 11 35 52 200 84 34 64 128 256), losses := [] }

theorem u12019 : Upper (D 6) (R 6) [10,33,48,192,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12020 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 52 200 84 36 323 387 259), lower := (rows 11 35 52 200 84 36 64 128 256), losses := [] }

theorem u12020 : Upper (D 6) (R 6) [10,33,48,192,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12021 : Route 9 := (fun mask => (mask,id))

def c12021 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12021 : Upper (D 6) (R 6) [10,33,48,192,68,256] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,68,256] 13 (by decide) (choices 1) [1,2,4] r12021 c12021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2170
  · exact u2171
  · exact u2172

def b12022 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 200 273 34 68 196 324), lower := (rows 11 35 52 200 273 34 64 128 256), losses := [] }

theorem u12022 : Upper (D 6) (R 6) [10,33,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12023 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 35 52 200 273 36 70 198 326), lower := (rows 11 35 52 200 273 36 64 128 256), losses := [] }

theorem u12023 : Upper (D 6) (R 6) [10,33,48,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12024 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 276, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 52 200 273 96 70 134 262), lower := (rows 11 35 52 200 273 96 64 128 256), losses := [] }

theorem u12024 : Upper (D 6) (R 6) [10,33,48,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12025 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 200 274 33 68 196 324), lower := (rows 11 35 52 200 274 33 64 128 256), losses := [] }

theorem u12025 : Upper (D 6) (R 6) [10,33,48,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12026 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 200 274 36 69 197 325), lower := (rows 11 35 52 200 274 36 64 128 256), losses := [] }

theorem u12026 : Upper (D 6) (R 6) [10,33,48,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12027 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 276, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 52 200 274 96 69 133 261), lower := (rows 11 35 52 200 274 96 64 128 256), losses := [] }

theorem u12027 : Upper (D 6) (R 6) [10,33,48,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12028 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 200 276 33 70 198 326), lower := (rows 11 35 52 200 276 33 64 128 256), losses := [] }

theorem u12028 : Upper (D 6) (R 6) [10,33,48,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12029 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 200 276 34 69 197 325), lower := (rows 11 35 52 200 276 34 64 128 256), losses := [] }

theorem u12029 : Upper (D 6) (R 6) [10,33,48,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12030 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 200 276 36 67 195 323), lower := (rows 11 35 52 200 276 36 64 128 256), losses := [] }

theorem u12030 : Upper (D 6) (R 6) [10,33,48,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12031 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 276, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 52 200 276 96 71 135 263), lower := (rows 11 35 52 200 276 96 64 128 256), losses := [] }

theorem u12031 : Upper (D 6) (R 6) [10,33,48,192,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12032 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 200 336 33 70 134 262), lower := (rows 11 35 52 200 336 33 64 128 256), losses := [] }

theorem u12032 : Upper (D 6) (R 6) [10,33,48,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12033 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 200 336 34 69 133 261), lower := (rows 11 35 52 200 336 34 64 128 256), losses := [] }

theorem u12033 : Upper (D 6) (R 6) [10,33,48,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12034 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 200 336 36 71 135 263), lower := (rows 11 35 52 200 336 36 64 128 256), losses := [] }

theorem u12034 : Upper (D 6) (R 6) [10,33,48,192,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12035 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 392 81 34 68 196 324), lower := (rows 11 35 52 392 81 34 64 128 256), losses := [] }

theorem u12035 : Upper (D 6) (R 6) [10,33,48,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12036 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 35 52 392 81 36 70 198 326), lower := (rows 11 35 52 392 81 36 64 128 256), losses := [] }

theorem u12036 : Upper (D 6) (R 6) [10,33,48,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12037 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 52 392 81 96 70 134 262), lower := (rows 11 35 52 392 81 96 64 128 256), losses := [] }

theorem u12037 : Upper (D 6) (R 6) [10,33,48,384,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12038 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 392 82 33 68 196 324), lower := (rows 11 35 52 392 82 33 64 128 256), losses := [] }

theorem u12038 : Upper (D 6) (R 6) [10,33,48,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12039 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 392 82 36 69 197 325), lower := (rows 11 35 52 392 82 36 64 128 256), losses := [] }

theorem u12039 : Upper (D 6) (R 6) [10,33,48,384,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12040 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 52 392 82 96 69 133 261), lower := (rows 11 35 52 392 82 96 64 128 256), losses := [] }

theorem u12040 : Upper (D 6) (R 6) [10,33,48,384,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12041 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 392 84 33 70 198 326), lower := (rows 11 35 52 392 84 33 64 128 256), losses := [] }

theorem u12041 : Upper (D 6) (R 6) [10,33,48,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12042 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 392 84 34 69 197 325), lower := (rows 11 35 52 392 84 34 64 128 256), losses := [] }

theorem u12042 : Upper (D 6) (R 6) [10,33,48,384,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12043 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 52 392 84 36 67 195 323), lower := (rows 11 35 52 392 84 36 64 128 256), losses := [] }

theorem u12043 : Upper (D 6) (R 6) [10,33,48,384,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12044 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 392 84 96 71 135 263), lower := (rows 11 35 52 392 84 96 64 128 256), losses := [] }

theorem u12044 : Upper (D 6) (R 6) [10,33,48,384,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12045 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 28 176 34 324 452 324), lower := (rows 11 35 69 28 176 34 64 128 256), losses := [] }

theorem u12045 : Upper (D 6) (R 6) [10,33,65,20,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12046 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 464, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 69 28 176 36 322 450 322), lower := (rows 11 35 69 28 176 36 64 128 256), losses := [] }

theorem u12046 : Upper (D 6) (R 6) [10,33,65,20,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12047 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 324, targets := 32 },{ cop := 2, region := 34, targets := 4 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 35 69 28 176 96 326 390 262), lower := (rows 11 35 69 28 176 96 64 128 256), losses := [{ target := 2, region := (rows 9 14 0 8 16 100 64 128 256), good := (rows 11 35 99 59 176 96 96 128 256) }] }

theorem u12047 : Upper (D 6) (R 6) [10,33,65,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12048 : Route 9 := (fun mask => (mask,id))

def c12048 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12048 : Upper (D 6) (R 6) [10,33,65,20,160,256] 13 := by
  apply FastRouting.sound _ _ [10,33,65,20,160,256] 13 (by decide) (choices 1) [2,4] r12048 c12048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2173
  · exact u2174

def b12049 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 69 28 208 34 356 420 292), lower := (rows 11 35 69 28 208 34 64 128 256), losses := [] }

theorem u12049 : Upper (D 6) (R 6) [10,33,65,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12050 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 464, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 69 28 208 36 354 418 290), lower := (rows 11 35 69 28 208 36 64 128 256), losses := [] }

theorem u12050 : Upper (D 6) (R 6) [10,33,65,20,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12051 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 69 28 208 288 102 166 294), lower := (rows 11 35 69 28 208 288 64 128 256), losses := [] }

theorem u12051 : Upper (D 6) (R 6) [10,33,65,20,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12051 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12052 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 28 400 34 100 228 356), lower := (rows 11 35 69 28 400 34 64 128 256), losses := [] }

theorem u12052 : Upper (D 6) (R 6) [10,33,65,20,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12053 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 464, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 69 28 400 36 98 226 354), lower := (rows 11 35 69 28 400 36 64 128 256), losses := [] }

theorem u12053 : Upper (D 6) (R 6) [10,33,65,20,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12054 : Route 9 := (fun mask => (mask,id))

def c12054 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12054 : Upper (D 6) (R 6) [10,33,65,20,384,64] 13 := by
  apply FastRouting.sound _ _ [10,33,65,20,384,64] 13 (by decide) (choices 1) [2,4,32] r12054 c12054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2175
  · exact u2176
  · exact u2177

def b12055 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 88 400 34 100 164 292), lower := (rows 11 35 69 88 400 34 64 128 256), losses := [] }

theorem u12055 : Upper (D 6) (R 6) [10,33,65,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12056 : Route 9 := (fun mask => (mask,id))

def c12056 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12056 : Upper (D 6) (R 6) [10,33,65,80,384,4] 13 := by
  apply FastRouting.sound _ _ [10,33,65,80,384,4] 13 (by decide) (choices 1) [2,4,32] r12056 c12056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2178
  · exact u2179
  · exact u2180

def b12057 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 69 140 22 48 352 480 352), lower := (rows 11 35 69 140 22 48 64 128 256), losses := [] }

theorem u12057 : Upper (D 6) (R 6) [10,33,65,132,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12057 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12058 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 488, targets := 3 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 35 69 140 22 96 368 432 304), lower := (rows 11 35 69 140 22 96 64 128 256), losses := [] }

theorem u12058 : Upper (D 6) (R 6) [10,33,65,132,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12059 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 488, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 69 140 22 288 112 240 368), lower := (rows 11 35 69 140 22 288 64 128 256), losses := [] }

theorem u12059 : Upper (D 6) (R 6) [10,33,65,132,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12059 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12059
end Delivery.IrregularNine14.P06
