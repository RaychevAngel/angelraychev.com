import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0166
import IrregularNine14P07C0167

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r27240 : Route 9 := (fun mask => (mask,id))

def c27240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27240 : Upper (D 7) (R 7) [36,320,9,80,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,9,80,160,2] 13 (by decide) (choices 1) [1,2,128] r27240 c27240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9991
  · exact u9992
  · exact u9993

def b27241 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 13 88 176 160 67 131 259), lower := (rows 37 322 13 88 176 160 64 128 256), losses := [] }

theorem u27241 : Upper (D 7) (R 7) [36,320,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27242 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 13 138 19 48 224 224 480), lower := (rows 37 322 13 138 19 48 64 128 256), losses := [] }

theorem u27242 : Upper (D 7) (R 7) [36,320,9,130,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27242 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27243 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 322 13 138 19 96 240 176 432), lower := (rows 37 322 13 138 19 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 114 80 144 272), good := (rows 37 352 13 173 497 96 96 128 256) }] }

theorem u27243 : Upper (D 7) (R 7) [36,320,9,130,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27244 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 0, region := 338, targets := 128 }], pairs := [(0,6),(1,7),(2,6),(4,6)], upper := (rows 37 322 13 138 19 160 112 240 368), lower := (rows 37 322 13 138 19 160 64 128 256), losses := [] }

theorem u27244 : Upper (D 7) (R 7) [36,320,9,130,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27245 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 138 50 33 208 208 464), lower := (rows 37 322 13 138 50 33 64 128 256), losses := [] }

theorem u27245 : Upper (D 7) (R 7) [36,320,9,130,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27246 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 13 138 50 48 193 193 449), lower := (rows 37 322 13 138 50 48 64 128 256), losses := [] }

theorem u27246 : Upper (D 7) (R 7) [36,320,9,130,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27246 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27247 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 141, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 322 13 138 50 96 209 145 401), lower := (rows 37 322 13 138 50 96 64 128 256), losses := [] }

theorem u27247 : Upper (D 7) (R 7) [36,320,9,130,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27248 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 0, region := 338, targets := 128 }], pairs := [(0,6),(1,7),(2,6),(4,6)], upper := (rows 37 322 13 138 50 160 81 209 337), lower := (rows 37 322 13 138 50 160 64 128 256), losses := [] }

theorem u27248 : Upper (D 7) (R 7) [36,320,9,130,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27249 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 138 81 34 240 176 432), lower := (rows 37 322 13 138 81 34 64 128 256), losses := [] }

theorem u27249 : Upper (D 7) (R 7) [36,320,9,130,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27250 : Route 9 := (fun mask => (mask,id))

def c27250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27250 : Upper (D 7) (R 7) [36,320,9,130,65,16] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,65,16] 13 (by decide) (choices 1) [2,32,128] r27250 c27250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9994
  · exact u9995
  · exact u9996

def b27251 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 138 81 160 114 178 306), lower := (rows 37 322 13 138 81 160 64 128 256), losses := [] }

theorem u27251 : Upper (D 7) (R 7) [36,320,9,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27252 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 138 112 33 210 146 402), lower := (rows 37 322 13 138 112 33 64 128 256), losses := [] }

theorem u27252 : Upper (D 7) (R 7) [36,320,9,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27253 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 138 112 34 209 145 401), lower := (rows 37 322 13 138 112 34 64 128 256), losses := [] }

theorem u27253 : Upper (D 7) (R 7) [36,320,9,130,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27254 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 13 138 112 48 195 131 387), lower := (rows 37 322 13 138 112 48 64 128 256), losses := [] }

theorem u27254 : Upper (D 7) (R 7) [36,320,9,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27254 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27255 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 138 112 160 83 147 275), lower := (rows 37 322 13 138 112 160 64 128 256), losses := [] }

theorem u27255 : Upper (D 7) (R 7) [36,320,9,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27256 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 37 322 13 138 145 34 112 240 368), lower := (rows 37 322 13 138 145 34 64 128 256), losses := [] }

theorem u27256 : Upper (D 7) (R 7) [36,320,9,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27257 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 13 138 145 48 98 226 354), lower := (rows 37 322 13 138 145 48 64 128 256), losses := [] }

theorem u27257 : Upper (D 7) (R 7) [36,320,9,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27257 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27258 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 322 13 138 145 96 114 178 306), lower := (rows 37 322 13 138 145 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 24 98 64 128 256), good := (rows 37 352 29 189 145 96 96 128 256) }] }

theorem u27258 : Upper (D 7) (R 7) [36,320,9,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27259 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 138 176 33 82 210 338), lower := (rows 37 322 13 138 176 33 64 128 256), losses := [] }

theorem u27259 : Upper (D 7) (R 7) [36,320,9,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27260 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 37 322 13 138 176 34 81 209 337), lower := (rows 37 322 13 138 176 34 64 128 256), losses := [] }

theorem u27260 : Upper (D 7) (R 7) [36,320,9,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27261 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 13 138 176 48 67 195 323), lower := (rows 37 322 13 138 176 48 64 128 256), losses := [] }

theorem u27261 : Upper (D 7) (R 7) [36,320,9,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27261 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27262 : PairBound 9 := { available := 19, camps := [], pairs := [(0,1),(2,1),(4,0),(4,1)], upper := (rows 37 322 13 138 176 96 83 147 275), lower := (rows 37 322 13 138 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 98 64 128 256), good := (rows 36 354 28 186 176 96 96 128 256) },{ target := 1, region := (rows 9 0 12 8 24 98 64 128 256), good := (rows 37 352 29 189 176 96 96 128 256) }] }

theorem u27262 : Upper (D 7) (R 7) [36,320,9,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27263 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 138 208 33 114 178 306), lower := (rows 37 322 13 138 208 33 64 128 256), losses := [] }

theorem u27263 : Upper (D 7) (R 7) [36,320,9,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27264 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 138 208 34 113 177 305), lower := (rows 37 322 13 138 208 34 64 128 256), losses := [] }

theorem u27264 : Upper (D 7) (R 7) [36,320,9,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27265 : Route 9 := (fun mask => (mask,id))

def c27265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27265 : Upper (D 7) (R 7) [36,320,9,130,192,16] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,192,16] 13 (by decide) (choices 1) [1,2,32] r27265 c27265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9997
  · exact u9998
  · exact u9999

def b27266 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 37 322 13 152 19 34 224 224 480), lower := (rows 37 322 13 152 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 97 161 289), good := (rows 485 320 461 156 477 480 64 128 256) }] }

theorem u27266 : Upper (D 7) (R 7) [36,320,9,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27267 : Route 9 := (fun mask => (mask,id))

def c27267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27267 : Upper (D 7) (R 7) [36,320,9,144,3,64] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144,3,64] 13 (by decide) (choices 1) [2,32,128] r27267 c27267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10000
  · exact u10001
  · exact u10002

def b27268 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 152 19 160 98 226 354), lower := (rows 37 322 13 152 19 160 64 128 256), losses := [] }

theorem u27268 : Upper (D 7) (R 7) [36,320,9,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27269 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 152 50 33 194 194 450), lower := (rows 37 322 13 152 50 33 64 128 256), losses := [] }

theorem u27269 : Upper (D 7) (R 7) [36,320,9,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27270 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 322 13 152 50 34 193 193 449), lower := (rows 37 322 13 152 50 34 64 128 256), losses := [] }

theorem u27270 : Upper (D 7) (R 7) [36,320,9,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27271 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 141, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 322 13 152 50 96 195 131 387), lower := (rows 37 322 13 152 50 96 64 128 256), losses := [] }

theorem u27271 : Upper (D 7) (R 7) [36,320,9,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27272 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 152 50 160 67 195 323), lower := (rows 37 322 13 152 50 160 64 128 256), losses := [] }

theorem u27272 : Upper (D 7) (R 7) [36,320,9,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27273 : Route 9 := (fun mask => (mask,id))

def c27273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27273 : Upper (D 7) (R 7) [36,320,9,144,65,2] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144,65,2] 13 (by decide) (choices 1) [2,32,128] r27273 c27273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10003
  · exact u10004
  · exact u10005

def b27274 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 152 81 160 98 162 290), lower := (rows 37 322 13 152 81 160 64 128 256), losses := [] }

theorem u27274 : Upper (D 7) (R 7) [36,320,9,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27275 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 152 112 33 194 130 386), lower := (rows 37 322 13 152 112 33 64 128 256), losses := [] }

theorem u27275 : Upper (D 7) (R 7) [36,320,9,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27276 : Route 9 := (fun mask => (mask,id))

def c27276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27276 : Upper (D 7) (R 7) [36,320,9,144,96,2] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144,96,2] 13 (by decide) (choices 1) [1,2,128] r27276 c27276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10006
  · exact u10007
  · exact u10008

def b27277 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 152 112 160 67 131 259), lower := (rows 37 322 13 152 112 160 64 128 256), losses := [] }

theorem u27277 : Upper (D 7) (R 7) [36,320,9,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27278 : Route 9 := (fun mask => (mask,id))

def c27278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u27278 : Upper (D 7) (R 7) [36,320,9,192,3,2] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,3,2] 13 (by decide) (choices 1) [16,32,128] r27278 c27278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10009
  · exact u10010
  · exact u10011

def r27279 : Route 9 := (fun mask => (mask,id))

def c27279 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27279 : Upper (D 7) (R 7) [36,320,9,192,3,16] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,3,16] 13 (by decide) (choices 1) [2,32,128] r27279 c27279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10012
  · exact u10013
  · exact u10014

def b27280 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 200 19 160 114 178 306), lower := (rows 37 322 13 200 19 160 64 128 256), losses := [] }

theorem u27280 : Upper (D 7) (R 7) [36,320,9,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27281 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 200 50 33 210 146 402), lower := (rows 37 322 13 200 50 33 64 128 256), losses := [] }

theorem u27281 : Upper (D 7) (R 7) [36,320,9,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27282 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 322 13 200 50 34 209 145 401), lower := (rows 37 322 13 200 50 34 64 128 256), losses := [] }

theorem u27282 : Upper (D 7) (R 7) [36,320,9,192,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27283 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 13 200 50 48 195 131 387), lower := (rows 37 322 13 200 50 48 64 128 256), losses := [] }

theorem u27283 : Upper (D 7) (R 7) [36,320,9,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27283 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27284 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 200 50 160 83 147 275), lower := (rows 37 322 13 200 50 160 64 128 256), losses := [] }

theorem u27284 : Upper (D 7) (R 7) [36,320,9,192,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27285 : Route 9 := (fun mask => (mask,id))

def c27285 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27285 : Upper (D 7) (R 7) [36,320,9,192,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,129,2] 13 (by decide) (choices 1) [2,16,32] r27285 c27285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10015
  · exact u10016
  · exact u10017

def b27286 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 13 200 145 48 98 162 290), lower := (rows 37 322 13 200 145 48 64 128 256), losses := [] }

theorem u27286 : Upper (D 7) (R 7) [36,320,9,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27286 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27287 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 200 146 33 114 178 306), lower := (rows 37 322 13 200 146 33 64 128 256), losses := [] }

theorem u27287 : Upper (D 7) (R 7) [36,320,9,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27288 : Route 9 := (fun mask => (mask,id))

def c27288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27288 : Upper (D 7) (R 7) [36,320,9,192,130,2] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,130,2] 13 (by decide) (choices 1) [1,16,32] r27288 c27288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10018
  · exact u10019
  · exact u10020

def r27289 : Route 9 := (fun mask => (mask,id))

def c27289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27289 : Upper (D 7) (R 7) [36,320,9,192,130,16] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,130,16] 13 (by decide) (choices 1) [1,2,32] r27289 c27289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10021
  · exact u10022
  · exact u10023

def b27290 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 200 176 33 82 146 274), lower := (rows 37 322 13 200 176 33 64 128 256), losses := [] }

theorem u27290 : Upper (D 7) (R 7) [36,320,9,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27291 : Route 9 := (fun mask => (mask,id))

def c27291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27291 : Upper (D 7) (R 7) [36,320,9,192,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,160,2] 13 (by decide) (choices 1) [1,2,16] r27291 c27291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10024
  · exact u10025
  · exact u10026

def b27292 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 13 200 176 48 67 131 259), lower := (rows 37 322 13 200 176 48 64 128 256), losses := [] }

theorem u27292 : Upper (D 7) (R 7) [36,320,9,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27292 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27293 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 14 25 112 33 194 130 386), lower := (rows 37 322 14 25 112 33 64 128 256), losses := [] }

theorem u27293 : Upper (D 7) (R 7) [36,320,10,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27294 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 14 25 112 34 193 129 385), lower := (rows 37 322 14 25 112 34 64 128 256), losses := [] }

theorem u27294 : Upper (D 7) (R 7) [36,320,10,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27295 : Route 9 := (fun mask => (mask,id))

def c27295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27295 : Upper (D 7) (R 7) [36,320,10,17,96,128] 13 := by
  apply FastRouting.sound _ _ [36,320,10,17,96,128] 13 (by decide) (choices 1) [1,2,128] r27295 c27295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10027
  · exact u10028
  · exact u10029

def b27296 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 14 25 146 33 224 224 480), lower := (rows 37 322 14 25 146 33 64 128 256), losses := [] }

theorem u27296 : Upper (D 7) (R 7) [36,320,10,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27297 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 322 14 25 146 96 225 161 417), lower := (rows 37 322 14 25 146 96 64 128 256), losses := [{ target := 7, region := (rows 21 2 20 24 16 98 64 0 256), good := (rows 37 354 47 29 63 96 96 0 256) }] }

theorem u27297 : Upper (D 7) (R 7) [36,320,10,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27298 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(2,6),(3,6)], upper := (rows 37 322 14 25 146 160 97 225 353), lower := (rows 37 322 14 25 146 160 64 128 256), losses := [] }

theorem u27298 : Upper (D 7) (R 7) [36,320,10,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27299 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 14 25 176 33 194 194 450), lower := (rows 37 322 14 25 176 33 64 128 256), losses := [] }

theorem u27299 : Upper (D 7) (R 7) [36,320,10,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27299
end Delivery.IrregularNine14.P07
