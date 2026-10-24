import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0058

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15240 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 37 28 304 36 66 194 322), lower := (rows 11 131 37 28 304 36 64 128 256), losses := [] }

theorem u15240 : Upper (D 6) (R 6) [10,129,33,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15241 : Route 9 := (fun mask => (mask,id))

def c15241 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15241 : Upper (D 6) (R 6) [10,129,33,20,288,64] 13 := by
  apply FastRouting.sound _ _ [10,129,33,20,288,64] 13 (by decide) (choices 1) [2,4] r15241 c15241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3517
  · exact u3518

def b15242 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 28 336 34 100 228 356), lower := (rows 11 131 37 28 336 34 64 128 256), losses := [] }

theorem u15242 : Upper (D 6) (R 6) [10,129,33,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15243 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 28 336 36 98 226 354), lower := (rows 11 131 37 28 336 36 64 128 256), losses := [] }

theorem u15243 : Upper (D 6) (R 6) [10,129,33,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15244 : Route 9 := (fun mask => (mask,id))

def c15244 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15244 : Upper (D 6) (R 6) [10,129,33,20,320,64] 13 := by
  apply FastRouting.sound _ _ [10,129,33,20,320,64] 13 (by decide) (choices 1) [2,4,32] r15244 c15244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3519
  · exact u3520
  · exact u3521

def b15245 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 56 336 34 68 196 324), lower := (rows 11 131 37 56 336 34 64 128 256), losses := [] }

theorem u15245 : Upper (D 6) (R 6) [10,129,33,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15246 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 56 336 36 70 198 326), lower := (rows 11 131 37 56 336 36 64 128 256), losses := [] }

theorem u15246 : Upper (D 6) (R 6) [10,129,33,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15247 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 37 56 336 96 70 134 262), lower := (rows 11 131 37 56 336 96 64 128 256), losses := [] }

theorem u15247 : Upper (D 6) (R 6) [10,129,33,48,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15248 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 131 37 76 22 48 352 480 352), lower := (rows 11 131 37 76 22 48 64 128 256), losses := [] }

theorem u15248 : Upper (D 6) (R 6) [10,129,33,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15248 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15249 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 4, region := 360, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 131 37 76 22 96 368 432 304), lower := (rows 11 131 37 76 22 96 64 128 256), losses := [] }

theorem u15249 : Upper (D 6) (R 6) [10,129,33,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15250 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 76 22 288 112 240 368), lower := (rows 11 131 37 76 22 288 64 128 256), losses := [] }

theorem u15250 : Upper (D 6) (R 6) [10,129,33,68,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15250 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15251 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 11 131 37 76 50 36 336 464 336), lower := (rows 11 131 37 76 50 36 64 128 256), losses := [] }

theorem u15251 : Upper (D 6) (R 6) [10,129,33,68,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15252 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 76 50 48 324 452 324), lower := (rows 11 131 37 76 50 48 64 128 256), losses := [] }

theorem u15252 : Upper (D 6) (R 6) [10,129,33,68,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15252 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15253 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 131 37 76 50 96 340 404 276), lower := (rows 11 131 37 76 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 108 68 132 260), good := (rows 58 146 508 492 50 96 96 128 256) }] }

theorem u15253 : Upper (D 6) (R 6) [10,129,33,68,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15254 : PairBound 9 := { available := 84, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 131 37 76 50 288 84 212 340), lower := (rows 11 131 37 76 50 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 300 68 132 260), good := (rows 58 146 508 492 50 288 64 128 288) }] }

theorem u15254 : Upper (D 6) (R 6) [10,129,33,68,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15254 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15255 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 76 82 36 368 432 304), lower := (rows 11 131 37 76 82 36 64 128 256), losses := [] }

theorem u15255 : Upper (D 6) (R 6) [10,129,33,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15256 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 76 82 48 356 420 292), lower := (rows 11 131 37 76 82 48 64 128 256), losses := [] }

theorem u15256 : Upper (D 6) (R 6) [10,129,33,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15256 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15257 : Route 9 := (fun mask => (mask,id))

def c15257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15257 : Upper (D 6) (R 6) [10,129,33,68,66,256] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,66,256] 13 (by decide) (choices 1) [4,16,32] r15257 c15257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3522
  · exact u3523
  · exact u3524

def b15258 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 76 112 34 340 404 276), lower := (rows 11 131 37 76 112 34 64 128 256), losses := [] }

theorem u15258 : Upper (D 6) (R 6) [10,129,33,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15259 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 76 112 36 338 402 274), lower := (rows 11 131 37 76 112 36 64 128 256), losses := [] }

theorem u15259 : Upper (D 6) (R 6) [10,129,33,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15260 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 76 112 48 326 390 262), lower := (rows 11 131 37 76 112 48 64 128 256), losses := [] }

theorem u15260 : Upper (D 6) (R 6) [10,129,33,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15260 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15261 : Route 9 := (fun mask => (mask,id))

def c15261 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15261 : Upper (D 6) (R 6) [10,129,33,68,96,256] 13 := by
  apply FastRouting.sound _ _ [10,129,33,68,96,256] 13 (by decide) (choices 1) [2,4,16] r15261 c15261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3525
  · exact u3526
  · exact u3527

def b15262 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 76 274 36 112 240 368), lower := (rows 11 131 37 76 274 36 64 128 256), losses := [] }

theorem u15262 : Upper (D 6) (R 6) [10,129,33,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15263 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 76 274 48 100 228 356), lower := (rows 11 131 37 76 274 48 64 128 256), losses := [] }

theorem u15263 : Upper (D 6) (R 6) [10,129,33,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15263 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15264 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 131 37 76 274 96 116 180 308), lower := (rows 11 131 37 76 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 133 37 108 272 96 96 128 256) }] }

theorem u15264 : Upper (D 6) (R 6) [10,129,33,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15265 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 76 276 34 112 240 368), lower := (rows 11 131 37 76 276 34 64 128 256), losses := [] }

theorem u15265 : Upper (D 6) (R 6) [10,129,33,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15266 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 194, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 11 131 37 76 276 48 98 226 354), lower := (rows 11 131 37 76 276 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 60 65 129 257), good := (rows 490 450 508 124 316 48 64 128 256) }] }

theorem u15266 : Upper (D 6) (R 6) [10,129,33,68,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15266 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15267 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 131 37 76 276 96 114 178 306), lower := (rows 11 131 37 76 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 133 37 108 276 96 96 128 256) }] }

theorem u15267 : Upper (D 6) (R 6) [10,129,33,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15268 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 76 304 34 84 212 340), lower := (rows 11 131 37 76 304 34 64 128 256), losses := [] }

theorem u15268 : Upper (D 6) (R 6) [10,129,33,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15269 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 76 304 36 82 210 338), lower := (rows 11 131 37 76 304 36 64 128 256), losses := [] }

theorem u15269 : Upper (D 6) (R 6) [10,129,33,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15270 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 131 37 76 304 48 70 198 326), lower := (rows 11 131 37 76 304 48 64 128 256), losses := [] }

theorem u15270 : Upper (D 6) (R 6) [10,129,33,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15270 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15271 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 131 37 76 304 96 86 150 278), lower := (rows 11 131 37 76 304 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 133 37 108 304 96 96 128 256) }] }

theorem u15271 : Upper (D 6) (R 6) [10,129,33,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15272 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 76 336 34 116 180 308), lower := (rows 11 131 37 76 336 34 64 128 256), losses := [] }

theorem u15272 : Upper (D 6) (R 6) [10,129,33,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15273 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 76 336 36 114 178 306), lower := (rows 11 131 37 76 336 36 64 128 256), losses := [] }

theorem u15273 : Upper (D 6) (R 6) [10,129,33,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15274 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 76 336 48 102 166 294), lower := (rows 11 131 37 76 336 48 64 128 256), losses := [{ target := 6, region := (rows 9 14 4 8 16 48 0 132 260), good := (rows 11 131 423 399 304 48 0 128 256) }] }

theorem u15274 : Upper (D 6) (R 6) [10,129,33,68,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15274 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15275 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 131 37 88 274 36 100 228 356), lower := (rows 11 131 37 88 274 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 55 119 183 311), good := (rows 493 485 485 504 508 484 64 128 256) }] }

theorem u15275 : Upper (D 6) (R 6) [10,129,33,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15276 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 131 37 88 274 96 100 164 292), lower := (rows 11 131 37 88 274 96 64 128 256), losses := [] }

theorem u15276 : Upper (D 6) (R 6) [10,129,33,80,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15277 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 88 276 34 100 228 356), lower := (rows 11 131 37 88 276 34 64 128 256), losses := [] }

theorem u15277 : Upper (D 6) (R 6) [10,129,33,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15278 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 88 276 36 98 226 354), lower := (rows 11 131 37 88 276 36 64 128 256), losses := [] }

theorem u15278 : Upper (D 6) (R 6) [10,129,33,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15279 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 131 37 88 276 96 102 166 294), lower := (rows 11 131 37 88 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 133 37 120 276 96 96 128 256) }] }

theorem u15279 : Upper (D 6) (R 6) [10,129,33,80,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15280 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 88 304 34 68 196 324), lower := (rows 11 131 37 88 304 34 64 128 256), losses := [] }

theorem u15280 : Upper (D 6) (R 6) [10,129,33,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15281 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 88 304 36 70 198 326), lower := (rows 11 131 37 88 304 36 64 128 256), losses := [] }

theorem u15281 : Upper (D 6) (R 6) [10,129,33,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15282 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 2, region := 130, targets := 32 }], pairs := [(1,5),(1,6),(4,6)], upper := (rows 11 131 37 88 304 96 70 134 262), lower := (rows 11 131 37 88 304 96 64 128 256), losses := [] }

theorem u15282 : Upper (D 6) (R 6) [10,129,33,80,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15283 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 104 82 36 340 404 276), lower := (rows 11 131 37 104 82 36 64 128 256), losses := [] }

theorem u15283 : Upper (D 6) (R 6) [10,129,33,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15284 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 104 82 48 324 388 260), lower := (rows 11 131 37 104 82 48 64 128 256), losses := [] }

theorem u15284 : Upper (D 6) (R 6) [10,129,33,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15284 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15285 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 131 37 104 82 288 84 148 276), lower := (rows 11 131 37 104 82 288 64 128 256), losses := [] }

theorem u15285 : Upper (D 6) (R 6) [10,129,33,96,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15285 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15286 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 104 84 34 340 404 276), lower := (rows 11 131 37 104 84 34 64 128 256), losses := [] }

theorem u15286 : Upper (D 6) (R 6) [10,129,33,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15287 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 104 84 36 338 402 274), lower := (rows 11 131 37 104 84 36 64 128 256), losses := [] }

theorem u15287 : Upper (D 6) (R 6) [10,129,33,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15288 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 104 84 48 326 390 262), lower := (rows 11 131 37 104 84 48 64 128 256), losses := [] }

theorem u15288 : Upper (D 6) (R 6) [10,129,33,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15288 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15289 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 131 37 104 84 288 86 150 278), lower := (rows 11 131 37 104 84 288 64 128 256), losses := [] }

theorem u15289 : Upper (D 6) (R 6) [10,129,33,96,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15289 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15290 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 104 274 36 84 212 340), lower := (rows 11 131 37 104 274 36 64 128 256), losses := [] }

theorem u15290 : Upper (D 6) (R 6) [10,129,33,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15291 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 104 274 48 68 196 324), lower := (rows 11 131 37 104 274 48 64 128 256), losses := [] }

theorem u15291 : Upper (D 6) (R 6) [10,129,33,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15291 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15292 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 37 104 274 96 84 148 276), lower := (rows 11 131 37 104 274 96 64 128 256), losses := [] }

theorem u15292 : Upper (D 6) (R 6) [10,129,33,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15293 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 104 276 34 84 212 340), lower := (rows 11 131 37 104 276 34 64 128 256), losses := [] }

theorem u15293 : Upper (D 6) (R 6) [10,129,33,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15294 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 104 276 36 82 210 338), lower := (rows 11 131 37 104 276 36 64 128 256), losses := [] }

theorem u15294 : Upper (D 6) (R 6) [10,129,33,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15295 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 131 37 104 276 48 70 198 326), lower := (rows 11 131 37 104 276 48 64 128 256), losses := [] }

theorem u15295 : Upper (D 6) (R 6) [10,129,33,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15295 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15296 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 37 104 276 96 86 150 278), lower := (rows 11 131 37 104 276 96 64 128 256), losses := [] }

theorem u15296 : Upper (D 6) (R 6) [10,129,33,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15297 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 104 336 34 84 148 276), lower := (rows 11 131 37 104 336 34 64 128 256), losses := [] }

theorem u15297 : Upper (D 6) (R 6) [10,129,33,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15298 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 104 336 36 86 150 278), lower := (rows 11 131 37 104 336 36 64 128 256), losses := [] }

theorem u15298 : Upper (D 6) (R 6) [10,129,33,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15299 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 104 336 48 70 134 262), lower := (rows 11 131 37 104 336 48 64 128 256), losses := [] }

theorem u15299 : Upper (D 6) (R 6) [10,129,33,96,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15299 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15299
end Delivery.IrregularNine14.P06
