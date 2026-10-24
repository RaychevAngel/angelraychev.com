import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0087

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18000 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 25 52 33 70 198 326), lower := (rows 11 162 324 25 52 33 64 128 256), losses := [] }

theorem u18000 : Upper (D 6) (R 6) [10,160,320,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18001 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 25 52 34 69 197 325), lower := (rows 11 162 324 25 52 34 64 128 256), losses := [] }

theorem u18001 : Upper (D 6) (R 6) [10,160,320,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18002 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 324 25 52 36 67 195 323), lower := (rows 11 162 324 25 52 36 64 128 256), losses := [] }

theorem u18002 : Upper (D 6) (R 6) [10,160,320,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18003 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 324 25 52 96 71 135 263), lower := (rows 11 162 324 25 52 96 64 128 256), losses := [] }

theorem u18003 : Upper (D 6) (R 6) [10,160,320,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18004 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 25 112 33 70 134 262), lower := (rows 11 162 324 25 112 33 64 128 256), losses := [] }

theorem u18004 : Upper (D 6) (R 6) [10,160,320,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18005 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 25 112 34 69 133 261), lower := (rows 11 162 324 25 112 34 64 128 256), losses := [] }

theorem u18005 : Upper (D 6) (R 6) [10,160,320,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18006 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 162 324 25 112 36 71 135 263), lower := (rows 11 162 324 25 112 36 64 128 256), losses := [] }

theorem u18006 : Upper (D 6) (R 6) [10,160,320,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18007 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 324 28 49 33 70 198 326), lower := (rows 11 162 324 28 49 33 64 128 256), losses := [] }

theorem u18007 : Upper (D 6) (R 6) [10,160,320,20,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18008 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 324 28 49 34 69 197 325), lower := (rows 11 162 324 28 49 34 64 128 256), losses := [] }

theorem u18008 : Upper (D 6) (R 6) [10,160,320,20,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18009 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 324, targets := 32 },{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(2,5),(4,1)], upper := (rows 11 162 324 28 49 36 67 195 323), lower := (rows 11 162 324 28 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 64 128 256), good := (rows 57 160 356 60 49 36 64 128 256) }] }

theorem u18009 : Upper (D 6) (R 6) [10,160,320,20,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18010 : Route 9 := (fun mask => (mask,id))

def c18010 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18010 : Upper (D 6) (R 6) [10,160,320,20,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,320,20,33,64] 13 (by decide) (choices 1) [1,2,4] r18010 c18010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5221
  · exact u5222
  · exact u5223

def b18011 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 5, region := 454, targets := 1 }], pairs := [(0,6),(1,0),(1,6)], upper := (rows 11 162 324 28 81 33 102 166 294), lower := (rows 11 162 324 28 81 33 64 128 256), losses := [] }

theorem u18011 : Upper (D 6) (R 6) [10,160,320,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18012 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 28 81 34 101 165 293), lower := (rows 11 162 324 28 81 34 64 128 256), losses := [] }

theorem u18012 : Upper (D 6) (R 6) [10,160,320,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18013 : Route 9 := (fun mask => (mask,id))

def c18013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18013 : Upper (D 6) (R 6) [10,160,320,20,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,20,65,4] 13 (by decide) (choices 1) [1,2,32] r18013 c18013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5224
  · exact u5225
  · exact u5226

def b18014 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 324 44 22 33 81 209 337), lower := (rows 11 162 324 44 22 33 64 128 256), losses := [] }

theorem u18014 : Upper (D 6) (R 6) [10,160,320,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18015 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 324 44 22 48 65 193 321), lower := (rows 11 162 324 44 22 48 64 128 256), losses := [] }

theorem u18015 : Upper (D 6) (R 6) [10,160,320,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18015 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18016 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 147, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 324 44 22 96 81 145 273), lower := (rows 11 162 324 44 22 96 64 128 256), losses := [] }

theorem u18016 : Upper (D 6) (R 6) [10,160,320,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18017 : Route 9 := (fun mask => (mask,id))

def c18017 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18017 : Upper (D 6) (R 6) [10,160,320,36,65,1] 13 := by
  apply FastRouting.sound _ _ [10,160,320,36,65,1] 13 (by decide) (choices 1) [2,4,16] r18017 c18017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5227
  · exact u5228
  · exact u5229

def b18018 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 324 44 81 34 85 149 277), lower := (rows 11 162 324 44 81 34 64 128 256), losses := [] }

theorem u18018 : Upper (D 6) (R 6) [10,160,320,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18019 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 324 44 81 36 83 147 275), lower := (rows 11 162 324 44 81 36 64 128 256), losses := [] }

theorem u18019 : Upper (D 6) (R 6) [10,160,320,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18020 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 324 44 81 48 71 135 263), lower := (rows 11 162 324 44 81 48 64 128 256), losses := [] }

theorem u18020 : Upper (D 6) (R 6) [10,160,320,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18020 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18021 : Route 9 := (fun mask => (mask,id))

def c18021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18021 : Upper (D 6) (R 6) [10,160,320,36,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,320,36,66,1] 13 (by decide) (choices 1) [1,4,16] r18021 c18021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5230
  · exact u5231
  · exact u5232

def b18022 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 324 44 82 36 81 145 273), lower := (rows 11 162 324 44 82 36 64 128 256), losses := [] }

theorem u18022 : Upper (D 6) (R 6) [10,160,320,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18023 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 324 44 82 48 69 133 261), lower := (rows 11 162 324 44 82 48 64 128 256), losses := [] }

theorem u18023 : Upper (D 6) (R 6) [10,160,320,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18023 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18024 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 162 324 56 21 33 70 198 326), lower := (rows 11 162 324 56 21 33 64 128 256), losses := [] }

theorem u18024 : Upper (D 6) (R 6) [10,160,320,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18025 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 324 56 21 34 69 197 325), lower := (rows 11 162 324 56 21 34 64 128 256), losses := [] }

theorem u18025 : Upper (D 6) (R 6) [10,160,320,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18026 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 324 56 21 36 67 195 323), lower := (rows 11 162 324 56 21 36 64 128 256), losses := [] }

theorem u18026 : Upper (D 6) (R 6) [10,160,320,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18027 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 324 56 21 96 71 135 263), lower := (rows 11 162 324 56 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 10 162 356 56 60 96 96 128 256) }] }

theorem u18027 : Upper (D 6) (R 6) [10,160,320,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18028 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 162 324 56 81 33 70 134 262), lower := (rows 11 162 324 56 81 33 64 128 256), losses := [] }

theorem u18028 : Upper (D 6) (R 6) [10,160,320,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18029 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 324 56 81 34 69 133 261), lower := (rows 11 162 324 56 81 34 64 128 256), losses := [] }

theorem u18029 : Upper (D 6) (R 6) [10,160,320,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18030 : Route 9 := (fun mask => (mask,id))

def c18030 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18030 : Upper (D 6) (R 6) [10,160,320,48,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,48,65,4] 13 (by decide) (choices 1) [1,2,4] r18030 c18030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5233
  · exact u5234
  · exact u5235

def b18031 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 73 22 33 116 180 308), lower := (rows 11 162 324 73 22 33 64 128 256), losses := [] }

theorem u18031 : Upper (D 6) (R 6) [10,160,320,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18032 : Route 9 := (fun mask => (mask,id))

def c18032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18032 : Upper (D 6) (R 6) [10,160,320,65,6,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,65,6,4] 13 (by decide) (choices 1) [1,16,32] r18032 c18032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5236
  · exact u5237
  · exact u5238

def r18033 : Route 9 := (fun mask => (mask,id))

def c18033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18033 : Upper (D 6) (R 6) [10,160,320,65,6,16] 13 := by
  apply FastRouting.sound _ _ [10,160,320,65,6,16] 13 (by decide) (choices 1) [1,4,32] r18033 c18033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5239
  · exact u5240
  · exact u5241

def b18034 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 324 73 49 34 84 148 276), lower := (rows 11 162 324 73 49 34 64 128 256), losses := [] }

theorem u18034 : Upper (D 6) (R 6) [10,160,320,65,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18035 : Route 9 := (fun mask => (mask,id))

def c18035 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18035 : Upper (D 6) (R 6) [10,160,320,65,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,65,33,4] 13 (by decide) (choices 1) [2,4,16] r18035 c18035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5242
  · exact u5243
  · exact u5244

def b18036 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 324 73 49 48 70 134 262), lower := (rows 11 162 324 73 49 48 64 128 256), losses := [] }

theorem u18036 : Upper (D 6) (R 6) [10,160,320,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18036 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18037 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 73 52 33 86 150 278), lower := (rows 11 162 324 73 52 33 64 128 256), losses := [] }

theorem u18037 : Upper (D 6) (R 6) [10,160,320,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18038 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 73 52 34 85 149 277), lower := (rows 11 162 324 73 52 34 64 128 256), losses := [] }

theorem u18038 : Upper (D 6) (R 6) [10,160,320,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18039 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 324 73 52 36 83 147 275), lower := (rows 11 162 324 73 52 36 64 128 256), losses := [] }

theorem u18039 : Upper (D 6) (R 6) [10,160,320,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18040 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 324 73 52 48 71 135 263), lower := (rows 11 162 324 73 52 48 64 128 256), losses := [] }

theorem u18040 : Upper (D 6) (R 6) [10,160,320,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18040 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18041 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 324 88 21 33 102 166 294), lower := (rows 11 162 324 88 21 33 64 128 256), losses := [] }

theorem u18041 : Upper (D 6) (R 6) [10,160,320,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18042 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 88 21 34 101 165 293), lower := (rows 11 162 324 88 21 34 64 128 256), losses := [] }

theorem u18042 : Upper (D 6) (R 6) [10,160,320,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18043 : Route 9 := (fun mask => (mask,id))

def c18043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18043 : Upper (D 6) (R 6) [10,160,320,80,5,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,5,4] 13 (by decide) (choices 1) [1,2,32] r18043 c18043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5245
  · exact u5246
  · exact u5247

def r18044 : Route 9 := (fun mask => (mask,id))

def c18044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18044 : Upper (D 6) (R 6) [10,160,320,80,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,6,1] 13 (by decide) (choices 1) [1,4,32] r18044 c18044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5248
  · exact u5249
  · exact u5250

def b18045 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 162 324 88 22 36 97 161 289), lower := (rows 11 162 324 88 22 36 64 128 256), losses := [{ target := 6, region := (rows 9 10 4 8 16 52 0 136 264), good := (rows 395 162 292 443 54 36 0 128 256) }] }

theorem u18045 : Upper (D 6) (R 6) [10,160,320,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18046 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 324 88 49 33 70 134 262), lower := (rows 11 162 324 88 49 33 64 128 256), losses := [] }

theorem u18046 : Upper (D 6) (R 6) [10,160,320,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18047 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 324 88 49 34 69 133 261), lower := (rows 11 162 324 88 49 34 64 128 256), losses := [] }

theorem u18047 : Upper (D 6) (R 6) [10,160,320,80,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18048 : Route 9 := (fun mask => (mask,id))

def c18048 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18048 : Upper (D 6) (R 6) [10,160,320,80,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,33,4] 13 (by decide) (choices 1) [1,2,4] r18048 c18048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5251
  · exact u5252
  · exact u5253

def r18049 : Route 9 := (fun mask => (mask,id))

def c18049 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18049 : Upper (D 6) (R 6) [10,160,320,80,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,36,1] 13 (by decide) (choices 1) [1,2,4] r18049 c18049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5254
  · exact u5255
  · exact u5256

def b18050 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 88 52 34 69 133 261), lower := (rows 11 162 324 88 52 34 64 128 256), losses := [] }

theorem u18050 : Upper (D 6) (R 6) [10,160,320,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18051 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 162 324 88 52 36 67 131 259), lower := (rows 11 162 324 88 52 36 64 128 256), losses := [] }

theorem u18051 : Upper (D 6) (R 6) [10,160,320,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18052 : Route 9 := (fun mask => (mask,id))

def c18052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18052 : Upper (D 6) (R 6) [10,160,320,96,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,320,96,6,1] 13 (by decide) (choices 1) [1,4,16] r18052 c18052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5257
  · exact u5258
  · exact u5259

def b18053 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 324 104 22 36 81 145 273), lower := (rows 11 162 324 104 22 36 64 128 256), losses := [] }

theorem u18053 : Upper (D 6) (R 6) [10,160,320,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18054 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 324 104 22 48 69 133 261), lower := (rows 11 162 324 104 22 48 64 128 256), losses := [] }

theorem u18054 : Upper (D 6) (R 6) [10,160,320,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18054 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18055 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 386 22 41 81 36 100 228 356), lower := (rows 11 386 22 41 81 36 64 128 256), losses := [] }

theorem u18055 : Upper (D 6) (R 6) [10,384,18,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18056 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 386 22 41 81 96 100 164 292), lower := (rows 11 386 22 41 81 96 64 128 256), losses := [] }

theorem u18056 : Upper (D 6) (R 6) [10,384,18,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18057 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 22 41 84 33 100 228 356), lower := (rows 11 386 22 41 84 33 64 128 256), losses := [] }

theorem u18057 : Upper (D 6) (R 6) [10,384,18,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18058 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 386 22 41 84 36 97 225 353), lower := (rows 11 386 22 41 84 36 64 128 256), losses := [] }

theorem u18058 : Upper (D 6) (R 6) [10,384,18,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m18059_1 : Upper (D 6) (R 6) [10,384,18,33,68,64,1] 13 :=
  permutation_upper _ _ _ [10,384,18,33,68,4,32] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5261

theorem m18059_4 : Upper (D 6) (R 6) [10,384,18,33,68,64,4] 13 :=
  permutation_upper _ _ _ [10,384,18,33,68,1,32] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5260

def r18059 : Route 9 := (fun mask => (mask,id))

def c18059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18059 : Upper (D 6) (R 6) [10,384,18,33,68,64] 13 := by
  apply FastRouting.sound _ _ [10,384,18,33,68,64] 13 (by decide) (choices 1) [1,4,32] r18059 c18059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18059_1
  · exact m18059_4
  · exact u5262

#print axioms u18059
end Delivery.IrregularNine14.P06
