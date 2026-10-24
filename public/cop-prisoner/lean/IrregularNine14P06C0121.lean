import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0009

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7260 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 134 292 28 88 33 66 193 321), lower := (rows 35 134 292 28 88 33 66 128 256), losses := [] }

theorem u7260 : Upper (D 6) (R 6) [34,132,288,20,72,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7261 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 134 292 73 84 40 65 146 274), lower := (rows 35 134 292 73 84 40 65 128 256), losses := [] }

theorem u7261 : Upper (D 6) (R 6) [34,132,288,65,68,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7261 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7262 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 134 292 73 84 40 66 145 273), lower := (rows 35 134 292 73 84 40 66 128 256), losses := [] }

theorem u7262 : Upper (D 6) (R 6) [34,132,288,65,68,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7262 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7263 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 134 292 73 84 40 80 131 259), lower := (rows 35 134 292 73 84 40 80 128 256), losses := [] }

theorem u7263 : Upper (D 6) (R 6) [34,132,288,65,68,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7263 [(5,3),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7264 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 292 74 84 33 65 152 280), lower := (rows 35 134 292 74 84 33 65 128 256), losses := [] }

theorem u7264 : Upper (D 6) (R 6) [34,132,288,66,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7265 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 35 134 292 74 84 33 72 145 273), lower := (rows 35 134 292 74 84 33 72 128 256), losses := [] }

theorem u7265 : Upper (D 6) (R 6) [34,132,288,66,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7265 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7266 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 35 134 292 74 84 33 80 137 265), lower := (rows 35 134 292 74 84 33 80 128 256), losses := [] }

theorem u7266 : Upper (D 6) (R 6) [34,132,288,66,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7266 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7267 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 35 134 324 13 26 96 65 176 304), lower := (rows 35 134 324 13 26 96 65 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 100 64 136 264), good := (rows 34 166 356 446 410 96 96 128 256) }] }

theorem u7267 : Upper (D 6) (R 6) [34,132,320,5,10,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7268 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,1)], upper := (rows 35 134 324 13 26 96 80 161 289), lower := (rows 35 134 324 13 26 96 80 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 116 80 137 265), good := (rows 417 164 356 429 508 96 116 128 256) }] }

theorem u7268 : Upper (D 6) (R 6) [34,132,320,5,10,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7268 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7269 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 146, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 134 324 13 26 96 96 145 273), lower := (rows 35 134 324 13 26 96 96 128 256), losses := [] }

theorem u7269 : Upper (D 6) (R 6) [34,132,320,5,10,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7270 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 324 13 81 48 66 168 296), lower := (rows 35 134 324 13 81 48 66 128 256), losses := [] }

theorem u7270 : Upper (D 6) (R 6) [34,132,320,5,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7270 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7271 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 80, targets := 2 }], pairs := [(4,1)], upper := (rows 35 134 324 13 81 48 72 162 290), lower := (rows 35 134 324 13 81 48 72 128 256), losses := [] }

theorem u7271 : Upper (D 6) (R 6) [34,132,320,5,65,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7271 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7272 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 324 13 81 48 96 138 266), lower := (rows 35 134 324 13 81 48 96 128 256), losses := [] }

theorem u7272 : Upper (D 6) (R 6) [34,132,320,5,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7272 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7273 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 324 25 28 96 65 162 290), lower := (rows 35 134 324 25 28 96 65 128 256), losses := [] }

theorem u7273 : Upper (D 6) (R 6) [34,132,320,17,12,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7274 : Route 9 := (fun mask => (mask,id))

def c7274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7274 : Upper (D 6) (R 6) [34,132,320,17,12,64,2] 13 := by
  apply FastRouting.sound _ _ [34,132,320,17,12,64,2] 13 (by decide) (choices 1) [1,32] r7274 c7274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u563
  · exact u564

def b7275 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 134 324 25 28 96 96 131 259), lower := (rows 35 134 324 25 28 96 96 128 256), losses := [] }

theorem u7275 : Upper (D 6) (R 6) [34,132,320,17,12,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7276 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 324 26 112 33 65 140 268), lower := (rows 35 134 324 26 112 33 65 128 256), losses := [] }

theorem u7276 : Upper (D 6) (R 6) [34,132,320,18,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7277 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 134 324 26 112 33 68 137 265), lower := (rows 35 134 324 26 112 33 68 128 256), losses := [] }

theorem u7277 : Upper (D 6) (R 6) [34,132,320,18,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7278 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 134 324 26 112 33 72 133 261), lower := (rows 35 134 324 26 112 33 72 128 256), losses := [] }

theorem u7278 : Upper (D 6) (R 6) [34,132,320,18,96,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7278 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7279 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 52 14 273 96 65 196 324), lower := (rows 35 138 52 14 273 96 65 128 256), losses := [] }

theorem u7279 : Upper (D 6) (R 6) [34,136,48,6,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7280 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 52 14 273 96 68 193 321), lower := (rows 35 138 52 14 273 96 68 128 256), losses := [] }

theorem u7280 : Upper (D 6) (R 6) [34,136,48,6,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7281 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 52 73 84 288 65 134 262), lower := (rows 35 138 52 73 84 288 65 128 256), losses := [] }

theorem u7281 : Upper (D 6) (R 6) [34,136,48,65,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7281 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7282 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 138 52 73 84 288 66 133 261), lower := (rows 35 138 52 73 84 288 66 128 256), losses := [] }

theorem u7282 : Upper (D 6) (R 6) [34,136,48,65,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7282 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7283 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 138 52 73 84 288 68 131 259), lower := (rows 35 138 52 73 84 288 68 128 256), losses := [] }

theorem u7283 : Upper (D 6) (R 6) [34,136,48,65,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7283 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7284 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 328 84 33 65 134 262), lower := (rows 35 138 52 328 84 33 65 128 256), losses := [] }

theorem u7284 : Upper (D 6) (R 6) [34,136,48,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7285 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 52 328 84 33 66 133 261), lower := (rows 35 138 52 328 84 33 66 128 256), losses := [] }

theorem u7285 : Upper (D 6) (R 6) [34,136,48,320,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7286 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 52 328 84 33 68 131 259), lower := (rows 35 138 52 328 84 33 68 128 256), losses := [] }

theorem u7286 : Upper (D 6) (R 6) [34,136,48,320,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7287 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 138 70 13 52 288 65 208 336), lower := (rows 35 138 70 13 52 288 65 128 256), losses := [] }

theorem u7287 : Upper (D 6) (R 6) [34,136,66,5,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7287 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7288 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0)], upper := (rows 35 138 70 13 52 288 80 193 321), lower := (rows 35 138 70 13 52 288 80 128 256), losses := [] }

theorem u7288 : Upper (D 6) (R 6) [34,136,66,5,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7288 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7289 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 138 70 13 112 33 320 148 276), lower := (rows 35 138 70 13 112 33 320 128 256), losses := [] }

theorem u7289 : Upper (D 6) (R 6) [34,136,66,5,96,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7289 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7290 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 138 70 13 112 36 320 145 273), lower := (rows 35 138 70 13 112 36 320 128 256), losses := [] }

theorem u7290 : Upper (D 6) (R 6) [34,136,66,5,96,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7290 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7291 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 138 70 13 112 48 320 133 261), lower := (rows 35 138 70 13 112 48 320 128 256), losses := [] }

theorem u7291 : Upper (D 6) (R 6) [34,136,66,5,96,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7291 [(5,4),(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7292 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 272, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 70 13 273 96 68 176 304), lower := (rows 35 138 70 13 273 96 68 128 256), losses := [] }

theorem u7292 : Upper (D 6) (R 6) [34,136,66,5,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7293 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 33, targets := 4 },{ cop := 3, region := 368, targets := 2 }], pairs := [(0,2),(4,1)], upper := (rows 35 138 70 13 273 96 80 164 292), lower := (rows 35 138 70 13 273 96 80 128 256), losses := [] }

theorem u7293 : Upper (D 6) (R 6) [34,136,66,5,257,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7293 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7294 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 138 70 13 273 96 96 148 276), lower := (rows 35 138 70 13 273 96 96 128 256), losses := [] }

theorem u7294 : Upper (D 6) (R 6) [34,136,66,5,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7295 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 32 },{ cop := 2, region := 304, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 35 138 70 13 304 96 65 148 276), lower := (rows 35 138 70 13 304 96 65 128 256), losses := [] }

theorem u7295 : Upper (D 6) (R 6) [34,136,66,5,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7296 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 70 13 304 96 68 145 273), lower := (rows 35 138 70 13 304 96 68 128 256), losses := [] }

theorem u7296 : Upper (D 6) (R 6) [34,136,66,5,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7297 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 138 70 13 304 96 80 133 261), lower := (rows 35 138 70 13 304 96 80 128 256), losses := [] }

theorem u7297 : Upper (D 6) (R 6) [34,136,66,5,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7297 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7298 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 35 138 70 25 276 96 65 164 292), lower := (rows 35 138 70 25 276 96 65 128 256), losses := [] }

theorem u7298 : Upper (D 6) (R 6) [34,136,66,17,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7299 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,5)], upper := (rows 35 138 70 25 276 96 68 161 289), lower := (rows 35 138 70 25 276 96 68 128 256), losses := [] }

theorem u7299 : Upper (D 6) (R 6) [34,136,66,17,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7300 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 35 138 70 25 276 96 96 133 261), lower := (rows 35 138 70 25 276 96 96 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 511 511 128 256), good := (rows 99 235 99 121 377 96 96 224 352) }] }

theorem u7300 : Upper (D 6) (R 6) [34,136,66,17,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7301 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 35 138 70 25 336 36 65 164 292), lower := (rows 35 138 70 25 336 36 65 128 256), losses := [] }

theorem u7301 : Upper (D 6) (R 6) [34,136,66,17,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7302 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,5)], upper := (rows 35 138 70 25 336 36 68 161 289), lower := (rows 35 138 70 25 336 36 68 128 256), losses := [] }

theorem u7302 : Upper (D 6) (R 6) [34,136,66,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7303 : Route 9 := (fun mask => (mask,id))

def c7303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7303 : Upper (D 6) (R 6) [34,136,66,17,320,4,32] 13 := by
  apply FastRouting.sound _ _ [34,136,66,17,320,4,32] 13 (by decide) (choices 1) [1,4] r7303 c7303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u565
  · exact u566

def b7304 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 35 138 70 265 21 96 68 176 304), lower := (rows 35 138 70 265 21 96 68 128 256), losses := [] }

theorem u7304 : Upper (D 6) (R 6) [34,136,66,257,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7305 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 70 265 21 96 80 164 292), lower := (rows 35 138 70 265 21 96 80 128 256), losses := [] }

theorem u7305 : Upper (D 6) (R 6) [34,136,66,257,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7305 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7306 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 138 70 265 21 96 96 148 276), lower := (rows 35 138 70 265 21 96 96 128 256), losses := [] }

theorem u7306 : Upper (D 6) (R 6) [34,136,66,257,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7307 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 35 138 70 265 81 36 68 176 304), lower := (rows 35 138 70 265 81 36 68 128 256), losses := [] }

theorem u7307 : Upper (D 6) (R 6) [34,136,66,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7308 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 70 265 81 36 80 164 292), lower := (rows 35 138 70 265 81 36 80 128 256), losses := [] }

theorem u7308 : Upper (D 6) (R 6) [34,136,66,257,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7308 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7309 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 70 265 81 36 96 148 276), lower := (rows 35 138 70 265 81 36 96 128 256), losses := [] }

theorem u7309 : Upper (D 6) (R 6) [34,136,66,257,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7310 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,6),(2,0),(4,6)], upper := (rows 35 138 70 280 21 33 96 196 324), lower := (rows 35 138 70 280 21 33 96 128 256), losses := [] }

theorem u7310 : Upper (D 6) (R 6) [34,136,66,272,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7311 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,6),(2,0),(4,6)], upper := (rows 35 138 70 280 21 36 96 193 321), lower := (rows 35 138 70 280 21 36 96 128 256), losses := [] }

theorem u7311 : Upper (D 6) (R 6) [34,136,66,272,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7312 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 138 70 280 21 96 96 133 261), lower := (rows 35 138 70 280 21 96 96 128 256), losses := [] }

theorem u7312 : Upper (D 6) (R 6) [34,136,66,272,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7313 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 138 84 13 273 96 66 164 292), lower := (rows 35 138 84 13 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 127 75 156 284), good := (rows 98 490 500 494 500 96 98 128 256) }] }

theorem u7313 : Upper (D 6) (R 6) [34,136,80,5,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7314 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 272, targets := 68 },{ cop := 4, region := 68, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 35 138 84 13 273 96 68 162 290), lower := (rows 35 138 84 13 273 96 68 128 256), losses := [] }

theorem u7314 : Upper (D 6) (R 6) [34,136,80,5,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7315 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 138 84 13 273 96 96 134 262), lower := (rows 35 138 84 13 273 96 96 128 256), losses := [] }

theorem u7315 : Upper (D 6) (R 6) [34,136,80,5,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7316 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 138 84 13 274 96 65 164 292), lower := (rows 35 138 84 13 274 96 65 128 256), losses := [{ target := 0, region := (rows 0 10 68 8 27 100 64 236 364), good := (rows 434 410 500 446 274 484 500 128 256) }] }

theorem u7316 : Upper (D 6) (R 6) [34,136,80,5,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7317 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 272, targets := 68 },{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 35 138 84 13 274 96 68 161 289), lower := (rows 35 138 84 13 274 96 68 128 256), losses := [] }

theorem u7317 : Upper (D 6) (R 6) [34,136,80,5,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7318 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 138 84 13 274 96 96 133 261), lower := (rows 35 138 84 13 274 96 96 128 256), losses := [] }

theorem u7318 : Upper (D 6) (R 6) [34,136,80,5,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7319 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 130, targets := 65 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(1,6)], upper := (rows 35 138 84 13 304 96 65 134 262), lower := (rows 35 138 84 13 304 96 65 128 256), losses := [] }

theorem u7319 : Upper (D 6) (R 6) [34,136,80,5,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7319
end Delivery.IrregularNine14.P06
