import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0016
import IrregularNine14P08C0017

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7260 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 292 200 208 33 97 161 289), lower := (rows 7 26 292 200 208 32 64 128 256), losses := [] }

theorem u7260 : Upper (D 8) (R 8) [6,24,288,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7261 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 324 41 49 224 224 224 480), lower := (rows 7 26 324 41 49 32 64 128 256), losses := [] }

theorem u7261 : Upper (D 8) (R 8) [6,24,320,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7262 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 324 41 81 160 224 160 416), lower := (rows 7 26 324 41 81 32 64 128 256), losses := [] }

theorem u7262 : Upper (D 8) (R 8) [6,24,320,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7263 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 324 41 112 161 225 161 417), lower := (rows 7 26 324 41 112 32 64 128 256), losses := [] }

theorem u7263 : Upper (D 8) (R 8) [6,24,320,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7264 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 324 41 145 224 224 224 480), lower := (rows 7 26 324 41 145 32 64 128 256), losses := [] }

theorem u7264 : Upper (D 8) (R 8) [6,24,320,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7265 : Route 9 := (fun mask => (mask,id))

def c7265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7265 : Upper (D 8) (R 8) [6,24,320,33,160] 13 := by
  apply FastRouting.sound _ _ [6,24,320,33,160] 13 (by decide) (choices 1) [1,64,128] r7265 c7265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1012
  · exact u1013
  · exact u1014

def b7266 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 324 41 208 161 225 161 417), lower := (rows 7 26 324 41 208 32 64 128 256), losses := [] }

theorem u7266 : Upper (D 8) (R 8) [6,24,320,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7267 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 324 73 145 160 224 160 416), lower := (rows 7 26 324 73 145 32 64 128 256), losses := [] }

theorem u7267 : Upper (D 8) (R 8) [6,24,320,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7268 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 324 73 176 161 225 161 417), lower := (rows 7 26 324 73 176 32 64 128 256), losses := [] }

theorem u7268 : Upper (D 8) (R 8) [6,24,320,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7269 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 324 104 145 161 225 161 417), lower := (rows 7 26 324 104 145 32 64 128 256), losses := [] }

theorem u7269 : Upper (D 8) (R 8) [6,24,320,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7270 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 324 104 176 161 225 161 417), lower := (rows 7 26 324 104 176 32 64 128 256), losses := [] }

theorem u7270 : Upper (D 8) (R 8) [6,24,320,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7271 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 324 137 145 96 96 224 352), lower := (rows 7 26 324 137 145 32 64 128 256), losses := [] }

theorem u7271 : Upper (D 8) (R 8) [6,24,320,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7272 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 324 137 176 97 97 225 353), lower := (rows 7 26 324 137 176 32 64 128 256), losses := [] }

theorem u7272 : Upper (D 8) (R 8) [6,24,320,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7273 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 324 137 208 33 97 161 289), lower := (rows 7 26 324 137 208 32 64 128 256), losses := [] }

theorem u7273 : Upper (D 8) (R 8) [6,24,320,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7274 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 324 168 176 97 97 225 353), lower := (rows 7 26 324 168 176 32 64 128 256), losses := [] }

theorem u7274 : Upper (D 8) (R 8) [6,24,320,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7275 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 324 168 208 33 97 161 289), lower := (rows 7 26 324 168 208 32 64 128 256), losses := [] }

theorem u7275 : Upper (D 8) (R 8) [6,24,320,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7276 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 56 49 480 448 448 448), lower := (rows 7 35 76 56 49 32 64 128 256), losses := [] }

theorem u7276 : Upper (D 8) (R 8) [6,33,72,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7277 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 56 81 416 480 416 416), lower := (rows 7 35 76 56 81 32 64 128 256), losses := [] }

theorem u7277 : Upper (D 8) (R 8) [6,33,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7278 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 56 112 417 449 385 385), lower := (rows 7 35 76 56 112 32 64 128 256), losses := [] }

theorem u7278 : Upper (D 8) (R 8) [6,33,72,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7279 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 56 145 480 480 480 480), lower := (rows 7 35 76 56 145 32 64 128 256), losses := [] }

theorem u7279 : Upper (D 8) (R 8) [6,33,72,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7280 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 56 176 481 449 449 449), lower := (rows 7 35 76 56 176 32 64 128 256), losses := [] }

theorem u7280 : Upper (D 8) (R 8) [6,33,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7281 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 56 208 417 481 417 417), lower := (rows 7 35 76 56 208 32 64 128 256), losses := [] }

theorem u7281 : Upper (D 8) (R 8) [6,33,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7282 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 56 273 224 224 224 480), lower := (rows 7 35 76 56 273 32 64 128 256), losses := [] }

theorem u7282 : Upper (D 8) (R 8) [6,33,72,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7283 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 56 304 225 193 193 449), lower := (rows 7 35 76 56 304 32 64 128 256), losses := [] }

theorem u7283 : Upper (D 8) (R 8) [6,33,72,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7284 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 56 336 161 225 161 417), lower := (rows 7 35 76 56 336 32 64 128 256), losses := [] }

theorem u7284 : Upper (D 8) (R 8) [6,33,72,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7285 : Route 9 := (fun mask => (mask,id))

def c7285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7285 : Upper (D 8) (R 8) [6,33,72,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,384] 13 (by decide) (choices 1) [1,64,128] r7285 c7285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1015
  · exact u1016
  · exact u1017

def b7286 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 152 49 480 480 480 480), lower := (rows 7 35 76 152 49 32 64 128 256), losses := [] }

theorem u7286 : Upper (D 8) (R 8) [6,33,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7287 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 81 416 480 416 416), lower := (rows 7 35 76 152 81 32 64 128 256), losses := [] }

theorem u7287 : Upper (D 8) (R 8) [6,33,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7288 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 112 417 481 417 417), lower := (rows 7 35 76 152 112 32 64 128 256), losses := [] }

theorem u7288 : Upper (D 8) (R 8) [6,33,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7289 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 152 145 352 352 480 352), lower := (rows 7 35 76 152 145 32 64 128 256), losses := [] }

theorem u7289 : Upper (D 8) (R 8) [6,33,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7290 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 152 176 353 353 481 353), lower := (rows 7 35 76 152 176 32 64 128 256), losses := [] }

theorem u7290 : Upper (D 8) (R 8) [6,33,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7291 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 152 208 289 353 417 289), lower := (rows 7 35 76 152 208 32 64 128 256), losses := [] }

theorem u7291 : Upper (D 8) (R 8) [6,33,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7292 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 152 273 224 224 224 480), lower := (rows 7 35 76 152 273 32 64 128 256), losses := [] }

theorem u7292 : Upper (D 8) (R 8) [6,33,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7293 : Route 9 := (fun mask => (mask,id))

def c7293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7293 : Upper (D 8) (R 8) [6,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288] 13 (by decide) (choices 1) [1,64,128] r7293 c7293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1018
  · exact u1019
  · exact u1020

def b7294 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 336 161 225 161 417), lower := (rows 7 35 76 152 336 32 64 128 256), losses := [] }

theorem u7294 : Upper (D 8) (R 8) [6,33,72,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7295 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 152 400 97 97 225 353), lower := (rows 7 35 76 152 400 32 64 128 256), losses := [] }

theorem u7295 : Upper (D 8) (R 8) [6,33,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7296 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 168 49 496 464 464 464), lower := (rows 7 35 76 168 49 32 64 128 256), losses := [] }

theorem u7296 : Upper (D 8) (R 8) [6,33,72,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7297 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 168 81 432 496 432 432), lower := (rows 7 35 76 168 81 32 64 128 256), losses := [] }

theorem u7297 : Upper (D 8) (R 8) [6,33,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7298 : Route 9 := (fun mask => (mask,id))

def c7298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7298 : Upper (D 8) (R 8) [6,33,72,160,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,96] 13 (by decide) (choices 1) [1,16,128,256] r7298 c7298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1021
  · exact u1022
  · exact u1023
  · exact u1024

def b7299 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 168 145 368 368 496 368), lower := (rows 7 35 76 168 145 32 64 128 256), losses := [] }

theorem u7299 : Upper (D 8) (R 8) [6,33,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7300 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 168 176 369 337 465 337), lower := (rows 7 35 76 168 176 32 64 128 256), losses := [] }

theorem u7300 : Upper (D 8) (R 8) [6,33,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7301 : Route 9 := (fun mask => (mask,id))

def c7301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7301 : Upper (D 8) (R 8) [6,33,72,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,192] 13 (by decide) (choices 1) [1,16,256] r7301 c7301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1025
  · exact u1026
  · exact u1027

def b7302 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 168 273 240 240 240 496), lower := (rows 7 35 76 168 273 32 64 128 256), losses := [] }

theorem u7302 : Upper (D 8) (R 8) [6,33,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7303 : Route 9 := (fun mask => (mask,id))

def c7303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7303 : Upper (D 8) (R 8) [6,33,72,160,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,288] 13 (by decide) (choices 1) [1,16,64,128] r7303 c7303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1028
  · exact u1029
  · exact u1030
  · exact u1031

def r7304 : Route 9 := (fun mask => (mask,id))

def c7304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7304 : Upper (D 8) (R 8) [6,33,72,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320] 13 (by decide) (choices 1) [1,16,128] r7304 c7304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1032
  · exact u1033
  · exact u1034

def r7305 : Route 9 := (fun mask => (mask,id))

def c7305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7305 : Upper (D 8) (R 8) [6,33,72,160,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,384] 13 (by decide) (choices 1) [1,16,64] r7305 c7305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1035
  · exact u1036
  · exact u1037

def b7306 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 280 49 224 224 224 480), lower := (rows 7 35 76 280 49 32 64 128 256), losses := [] }

theorem u7306 : Upper (D 8) (R 8) [6,33,72,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7307 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 81 160 224 160 416), lower := (rows 7 35 76 280 81 32 64 128 256), losses := [] }

theorem u7307 : Upper (D 8) (R 8) [6,33,72,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7308 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 112 161 225 161 417), lower := (rows 7 35 76 280 112 32 64 128 256), losses := [] }

theorem u7308 : Upper (D 8) (R 8) [6,33,72,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7309 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 280 145 224 224 224 480), lower := (rows 7 35 76 280 145 32 64 128 256), losses := [] }

theorem u7309 : Upper (D 8) (R 8) [6,33,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7310 : Route 9 := (fun mask => (mask,id))

def c7310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7310 : Upper (D 8) (R 8) [6,33,72,272,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,160] 13 (by decide) (choices 1) [1,64,128] r7310 c7310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1038
  · exact u1039
  · exact u1040

def b7311 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 208 161 225 161 417), lower := (rows 7 35 76 280 208 32 64 128 256), losses := [] }

theorem u7311 : Upper (D 8) (R 8) [6,33,72,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7312 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 296 49 240 208 208 464), lower := (rows 7 35 76 296 49 32 64 128 256), losses := [] }

theorem u7312 : Upper (D 8) (R 8) [6,33,72,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7313 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 296 81 176 240 176 432), lower := (rows 7 35 76 296 81 32 64 128 256), losses := [] }

theorem u7313 : Upper (D 8) (R 8) [6,33,72,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7314 : Route 9 := (fun mask => (mask,id))

def c7314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7314 : Upper (D 8) (R 8) [6,33,72,288,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,96] 13 (by decide) (choices 1) [1,16,128] r7314 c7314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1041
  · exact u1042
  · exact u1043

def b7315 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 296 145 240 240 240 496), lower := (rows 7 35 76 296 145 32 64 128 256), losses := [] }

theorem u7315 : Upper (D 8) (R 8) [6,33,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7316 : Route 9 := (fun mask => (mask,id))

def c7316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7316 : Upper (D 8) (R 8) [6,33,72,288,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,160] 13 (by decide) (choices 1) [1,16,64,128] r7316 c7316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1044
  · exact u1045
  · exact u1046
  · exact u1047

def r7317 : Route 9 := (fun mask => (mask,id))

def c7317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7317 : Upper (D 8) (R 8) [6,33,72,288,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,192] 13 (by decide) (choices 1) [1,16,128] r7317 c7317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1048
  · exact u1049
  · exact u1050

def b7318 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 392 49 240 240 240 496), lower := (rows 7 35 76 392 49 32 64 128 256), losses := [] }

theorem u7318 : Upper (D 8) (R 8) [6,33,72,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7319 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 392 81 176 240 176 432), lower := (rows 7 35 76 392 81 32 64 128 256), losses := [] }

theorem u7319 : Upper (D 8) (R 8) [6,33,72,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7319
end Delivery.IrregularNine14.P08
