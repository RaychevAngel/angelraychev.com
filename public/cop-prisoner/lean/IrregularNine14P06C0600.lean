import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0336
import IrregularNine14P06C0337
import IrregularNine14P06C0338

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36000 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 70 133 28 56 355 323 451 323), lower := (rows 35 70 133 28 56 32 64 128 256), losses := [] }

theorem u36000 : Upper (D 6) (R 6) [34,68,129,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36001 : Route 9 := (fun mask => (mask,id))

def c36001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36001 : Upper (D 6) (R 6) [34,68,129,20,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,65] 13 (by decide) (choices 1) [2,8,256] r36001 c36001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20179
  · exact u20180
  · exact u20181

def b36002 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 133 28 82 297 361 425 297), lower := (rows 35 70 133 28 82 32 64 128 256), losses := [] }

theorem u36002 : Upper (D 6) (R 6) [34,68,129,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36003 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 133 28 88 291 355 419 291), lower := (rows 35 70 133 28 88 32 64 128 256), losses := [] }

theorem u36003 : Upper (D 6) (R 6) [34,68,129,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36004 : Route 9 := (fun mask => (mask,id))

def c36004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36004 : Upper (D 6) (R 6) [34,68,129,20,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,96] 13 (by decide) (choices 1) [1,2,8,256] r36004 c36004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20182
  · exact u20183
  · exact u20184
  · exact u20185

def r36005 : Route 9 := (fun mask => (mask,id))

def c36005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36005 : Upper (D 6) (R 6) [34,68,129,20,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,257] 13 (by decide) (choices 1) [2,8,64] r36005 c36005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20186
  · exact u20187
  · exact u20188

def r36006 : Route 9 := (fun mask => (mask,id))

def c36006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36006 : Upper (D 6) (R 6) [34,68,129,20,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,258] 13 (by decide) (choices 1) [1,8,64] r36006 c36006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20189
  · exact u20190
  · exact u20191

def r36007 : Route 9 := (fun mask => (mask,id))

def c36007 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36007 : Upper (D 6) (R 6) [34,68,129,20,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,264] 13 (by decide) (choices 1) [1,2,64] r36007 c36007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20192
  · exact u20193
  · exact u20194

def r36008 : Route 9 := (fun mask => (mask,id))

def c36008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36008 : Upper (D 6) (R 6) [34,68,129,20,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,288] 13 (by decide) (choices 1) [1,2,8,64] r36008 c36008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20195
  · exact u20196
  · exact u20197
  · exact u20198

def r36009 : Route 9 := (fun mask => (mask,id))

def c36009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36009 : Upper (D 6) (R 6) [34,68,129,20,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,320] 13 (by decide) (choices 1) [1,2,8] r36009 c36009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20199
  · exact u20200
  · exact u20201

def b36010 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 133 41 88 310 342 406 278), lower := (rows 35 70 133 41 88 32 64 128 256), losses := [] }

theorem u36010 : Upper (D 6) (R 6) [34,68,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36011 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 133 41 274 124 92 220 348), lower := (rows 35 70 133 41 274 32 64 128 256), losses := [] }

theorem u36011 : Upper (D 6) (R 6) [34,68,129,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36012 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 133 41 276 122 90 218 346), lower := (rows 35 70 133 41 276 32 64 128 256), losses := [] }

theorem u36012 : Upper (D 6) (R 6) [34,68,129,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36013 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 133 41 280 118 86 214 342), lower := (rows 35 70 133 41 280 32 64 128 256), losses := [] }

theorem u36013 : Upper (D 6) (R 6) [34,68,129,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36014 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 133 41 336 62 94 158 286), lower := (rows 35 70 133 41 336 32 64 128 256), losses := [] }

theorem u36014 : Upper (D 6) (R 6) [34,68,129,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36015 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 133 42 81 316 348 412 284), lower := (rows 35 70 133 42 81 32 64 128 256), losses := [] }

theorem u36015 : Upper (D 6) (R 6) [34,68,129,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36016 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 133 42 88 309 341 405 277), lower := (rows 35 70 133 42 88 32 64 128 256), losses := [] }

theorem u36016 : Upper (D 6) (R 6) [34,68,129,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36017 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 133 42 273 124 92 220 348), lower := (rows 35 70 133 42 273 32 64 128 256), losses := [] }

theorem u36017 : Upper (D 6) (R 6) [34,68,129,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36018 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 133 42 276 121 89 217 345), lower := (rows 35 70 133 42 276 32 64 128 256), losses := [] }

theorem u36018 : Upper (D 6) (R 6) [34,68,129,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36019 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 133 42 280 117 85 213 341), lower := (rows 35 70 133 42 280 32 64 128 256), losses := [] }

theorem u36019 : Upper (D 6) (R 6) [34,68,129,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36020 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 70 133 42 336 61 93 157 285), lower := (rows 35 70 133 42 336 32 64 128 256), losses := [] }

theorem u36020 : Upper (D 6) (R 6) [34,68,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36021 : Route 9 := (fun mask => (mask,id))

def c36021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36021 : Upper (D 6) (R 6) [34,68,129,36,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36,65] 13 (by decide) (choices 1) [2,8,16,256] r36021 c36021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20202
  · exact u20203
  · exact u20204
  · exact u20205

def b36022 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 133 44 82 313 345 409 281), lower := (rows 35 70 133 44 82 32 64 128 256), losses := [] }

theorem u36022 : Upper (D 6) (R 6) [34,68,129,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36023 : Route 9 := (fun mask => (mask,id))

def c36023 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36023 : Upper (D 6) (R 6) [34,68,129,36,72] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36,72] 13 (by decide) (choices 1) [1,2,16,256] r36023 c36023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20206
  · exact u20207
  · exact u20208
  · exact u20209

def r36024 : Route 9 := (fun mask => (mask,id))

def c36024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36024 : Upper (D 6) (R 6) [34,68,129,36,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36,257] 13 (by decide) (choices 1) [2,8,16,64] r36024 c36024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20210
  · exact u20211
  · exact u20212
  · exact u20213

def r36025 : Route 9 := (fun mask => (mask,id))

def c36025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36025 : Upper (D 6) (R 6) [34,68,129,36,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36,258] 13 (by decide) (choices 1) [1,8,16,64] r36025 c36025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20214
  · exact u20215
  · exact u20216
  · exact u20217

def r36026 : Route 9 := (fun mask => (mask,id))

def c36026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36026 : Upper (D 6) (R 6) [34,68,129,36,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36,264] 13 (by decide) (choices 1) [1,2,16,64] r36026 c36026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20218
  · exact u20219
  · exact u20220
  · exact u20221

def r36027 : Route 9 := (fun mask => (mask,id))

def c36027 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36027 : Upper (D 6) (R 6) [34,68,129,36,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36,320] 13 (by decide) (choices 1) [1,2,8,16] r36027 c36027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20222
  · exact u20223
  · exact u20224
  · exact u20225

def r36028 : Route 9 := (fun mask => (mask,id))

def c36028 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36028 : Upper (D 6) (R 6) [34,68,129,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,65] 13 (by decide) (choices 1) [2,4,8,256] r36028 c36028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20226
  · exact u20227
  · exact u20228
  · exact u20229

def b36029 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 133 56 82 301 333 397 269), lower := (rows 35 70 133 56 82 32 64 128 256), losses := [] }

theorem u36029 : Upper (D 6) (R 6) [34,68,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36030 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 133 56 84 299 331 395 267), lower := (rows 35 70 133 56 84 32 64 128 256), losses := [] }

theorem u36030 : Upper (D 6) (R 6) [34,68,129,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36031 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 70 133 56 88 295 327 391 263), lower := (rows 35 70 133 56 88 32 64 128 256), losses := [] }

theorem u36031 : Upper (D 6) (R 6) [34,68,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36032 : Route 9 := (fun mask => (mask,id))

def c36032 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36032 : Upper (D 6) (R 6) [34,68,129,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,257] 13 (by decide) (choices 1) [2,4,8,64] r36032 c36032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20230
  · exact u20231
  · exact u20232
  · exact u20233

def r36033 : Route 9 := (fun mask => (mask,id))

def c36033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36033 : Upper (D 6) (R 6) [34,68,129,48,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,258] 13 (by decide) (choices 1) [1,4,8,64] r36033 c36033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20234
  · exact u20235
  · exact u20236
  · exact u20237

def r36034 : Route 9 := (fun mask => (mask,id))

def c36034 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36034 : Upper (D 6) (R 6) [34,68,129,48,260] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,260] 13 (by decide) (choices 1) [1,2,8,64] r36034 c36034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20238
  · exact u20239
  · exact u20240
  · exact u20241

def r36035 : Route 9 := (fun mask => (mask,id))

def c36035 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36035 : Upper (D 6) (R 6) [34,68,129,48,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,264] 13 (by decide) (choices 1) [1,2,4,64] r36035 c36035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20242
  · exact u20243
  · exact u20244
  · exact u20245

def r36036 : Route 9 := (fun mask => (mask,id))

def c36036 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36036 : Upper (D 6) (R 6) [34,68,129,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,320] 13 (by decide) (choices 1) [1,2,4,8] r36036 c36036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20246
  · exact u20247
  · exact u20248
  · exact u20249

def r36037 : Route 9 := (fun mask => (mask,id))

def c36037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36037 : Upper (D 6) (R 6) [34,68,129,65,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,258] 13 (by decide) (choices 1) [4,8,16] r36037 c36037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20250
  · exact u20251
  · exact u20252

def r36038 : Route 9 := (fun mask => (mask,id))

def c36038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36038 : Upper (D 6) (R 6) [34,68,129,65,260] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,260] 13 (by decide) (choices 1) [2,8,16] r36038 c36038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20253
  · exact u20254
  · exact u20255

def r36039 : Route 9 := (fun mask => (mask,id))

def c36039 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36039 : Upper (D 6) (R 6) [34,68,129,65,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,264] 13 (by decide) (choices 1) [2,4,16] r36039 c36039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20256
  · exact u20257
  · exact u20258

def r36040 : Route 9 := (fun mask => (mask,id))

def c36040 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36040 : Upper (D 6) (R 6) [34,68,129,65,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,288] 13 (by decide) (choices 1) [2,4,8,16] r36040 c36040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20259
  · exact u20260
  · exact u20261
  · exact u20262

def b36041 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 133 74 273 60 124 188 316), lower := (rows 35 70 133 74 273 32 64 128 256), losses := [] }

theorem u36041 : Upper (D 6) (R 6) [34,68,129,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36042 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 133 74 276 57 121 185 313), lower := (rows 35 70 133 74 276 32 64 128 256), losses := [] }

theorem u36042 : Upper (D 6) (R 6) [34,68,129,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36043 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 133 74 280 53 117 181 309), lower := (rows 35 70 133 74 280 32 64 128 256), losses := [] }

theorem u36043 : Upper (D 6) (R 6) [34,68,129,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36044 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 133 74 304 61 93 157 285), lower := (rows 35 70 133 74 304 32 64 128 256), losses := [] }

theorem u36044 : Upper (D 6) (R 6) [34,68,129,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36045 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 133 76 273 58 122 186 314), lower := (rows 35 70 133 76 273 32 64 128 256), losses := [] }

theorem u36045 : Upper (D 6) (R 6) [34,68,129,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36046 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 133 76 274 57 121 185 313), lower := (rows 35 70 133 76 274 32 64 128 256), losses := [] }

theorem u36046 : Upper (D 6) (R 6) [34,68,129,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36047 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 133 76 280 51 115 179 307), lower := (rows 35 70 133 76 280 32 64 128 256), losses := [] }

theorem u36047 : Upper (D 6) (R 6) [34,68,129,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36048 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 133 76 304 59 91 155 283), lower := (rows 35 70 133 76 304 32 64 128 256), losses := [] }

theorem u36048 : Upper (D 6) (R 6) [34,68,129,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36049 : Route 9 := (fun mask => (mask,id))

def c36049 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36049 : Upper (D 6) (R 6) [34,68,129,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,257] 13 (by decide) (choices 1) [2,4,8] r36049 c36049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20263
  · exact u20264
  · exact u20265

def r36050 : Route 9 := (fun mask => (mask,id))

def c36050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36050 : Upper (D 6) (R 6) [34,68,129,80,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,258] 13 (by decide) (choices 1) [1,4,8] r36050 c36050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20266
  · exact u20267
  · exact u20268

def r36051 : Route 9 := (fun mask => (mask,id))

def c36051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36051 : Upper (D 6) (R 6) [34,68,129,80,260] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,260] 13 (by decide) (choices 1) [1,2,8] r36051 c36051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20269
  · exact u20270
  · exact u20271

def r36052 : Route 9 := (fun mask => (mask,id))

def c36052 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36052 : Upper (D 6) (R 6) [34,68,129,80,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,264] 13 (by decide) (choices 1) [1,2,4] r36052 c36052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20272
  · exact u20273
  · exact u20274

def r36053 : Route 9 := (fun mask => (mask,id))

def c36053 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36053 : Upper (D 6) (R 6) [34,68,129,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,288] 13 (by decide) (choices 1) [1,2,4,8] r36053 c36053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20275
  · exact u20276
  · exact u20277
  · exact u20278

def r36054 : Route 9 := (fun mask => (mask,id))

def c36054 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36054 : Upper (D 6) (R 6) [34,68,129,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,257] 13 (by decide) (choices 1) [2,4,8,16] r36054 c36054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20279
  · exact u20280
  · exact u20281
  · exact u20282

def r36055 : Route 9 := (fun mask => (mask,id))

def c36055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36055 : Upper (D 6) (R 6) [34,68,129,96,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,258] 13 (by decide) (choices 1) [1,4,8,16] r36055 c36055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20283
  · exact u20284
  · exact u20285
  · exact u20286

def r36056 : Route 9 := (fun mask => (mask,id))

def c36056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36056 : Upper (D 6) (R 6) [34,68,129,96,260] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,260] 13 (by decide) (choices 1) [1,2,8,16] r36056 c36056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20287
  · exact u20288
  · exact u20289
  · exact u20290

def r36057 : Route 9 := (fun mask => (mask,id))

def c36057 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36057 : Upper (D 6) (R 6) [34,68,129,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264] 13 (by decide) (choices 1) [1,2,4,16] r36057 c36057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20291
  · exact u20292
  · exact u20293
  · exact u20294

def b36058 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 6 },{ cop := 3, region := 16, targets := 32 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 70 134 13 25 368 368 496 368), lower := (rows 35 70 134 13 25 32 64 128 256), losses := [] }

theorem u36058 : Upper (D 6) (R 6) [34,68,130,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36059 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 134 13 49 376 344 472 344), lower := (rows 35 70 134 13 49 32 64 128 256), losses := [] }

theorem u36059 : Upper (D 6) (R 6) [34,68,130,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36059
end Delivery.IrregularNine14.P06
