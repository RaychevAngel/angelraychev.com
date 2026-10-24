import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5280 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 386 38 76 112 33 65 148 276), lower := (rows 11 386 38 76 112 33 65 128 256), losses := [] }

theorem u5280 : Upper (D 6) (R 6) [10,384,34,68,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5281 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 386 38 76 112 33 68 145 273), lower := (rows 11 386 38 76 112 33 68 128 256), losses := [] }

theorem u5281 : Upper (D 6) (R 6) [10,384,34,68,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5282 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 386 38 76 112 33 80 133 261), lower := (rows 11 386 38 76 112 33 80 128 256), losses := [] }

theorem u5282 : Upper (D 6) (R 6) [10,384,34,68,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5282 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5283 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 386 38 88 21 96 65 164 292), lower := (rows 11 386 38 88 21 96 65 128 256), losses := [] }

theorem u5283 : Upper (D 6) (R 6) [10,384,34,80,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5284 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 386 38 88 21 96 68 161 289), lower := (rows 11 386 38 88 21 96 68 128 256), losses := [] }

theorem u5284 : Upper (D 6) (R 6) [10,384,34,80,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5285 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 5 },{ cop := 4, region := 386, targets := 32 }], pairs := [(1,5),(3,0),(3,2)], upper := (rows 11 386 38 88 21 96 96 133 261), lower := (rows 11 386 38 88 21 96 96 128 256), losses := [] }

theorem u5285 : Upper (D 6) (R 6) [10,384,34,80,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5286 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 38 104 84 33 65 148 276), lower := (rows 11 386 38 104 84 33 65 128 256), losses := [] }

theorem u5286 : Upper (D 6) (R 6) [10,384,34,96,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5287 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 386 38 104 84 33 68 145 273), lower := (rows 11 386 38 104 84 33 68 128 256), losses := [] }

theorem u5287 : Upper (D 6) (R 6) [10,384,34,96,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5288 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 386 38 104 84 33 80 133 261), lower := (rows 11 386 38 104 84 33 80 128 256), losses := [] }

theorem u5288 : Upper (D 6) (R 6) [10,384,34,96,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5288 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5289 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 52 13 84 34 65 224 352), lower := (rows 11 386 52 13 84 34 65 128 256), losses := [] }

theorem u5289 : Upper (D 6) (R 6) [10,384,48,5,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5290 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 386 52 13 84 34 96 193 321), lower := (rows 11 386 52 13 84 34 96 128 256), losses := [] }

theorem u5290 : Upper (D 6) (R 6) [10,384,48,5,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5291 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 386 52 73 22 96 65 164 292), lower := (rows 11 386 52 73 22 96 65 128 256), losses := [] }

theorem u5291 : Upper (D 6) (R 6) [10,384,48,65,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5292 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 386 52 73 22 96 68 161 289), lower := (rows 11 386 52 73 22 96 68 128 256), losses := [] }

theorem u5292 : Upper (D 6) (R 6) [10,384,48,65,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5293 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 0, region := 104, targets := 2 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 11 386 52 73 22 96 96 133 261), lower := (rows 11 386 52 73 22 96 96 128 256), losses := [] }

theorem u5293 : Upper (D 6) (R 6) [10,384,48,65,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5294 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 386 52 73 84 34 65 164 292), lower := (rows 11 386 52 73 84 34 65 128 256), losses := [] }

theorem u5294 : Upper (D 6) (R 6) [10,384,48,65,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5295 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 419, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 386 52 73 84 34 68 161 289), lower := (rows 11 386 52 73 84 34 68 128 256), losses := [] }

theorem u5295 : Upper (D 6) (R 6) [10,384,48,65,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5296 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 386 52 73 84 34 96 133 261), lower := (rows 11 386 52 73 84 34 96 128 256), losses := [] }

theorem u5296 : Upper (D 6) (R 6) [10,384,48,65,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5297 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 386, targets := 65 },{ cop := 0, region := 80, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 386 52 76 82 33 65 164 292), lower := (rows 11 386 52 76 82 33 65 128 256), losses := [] }

theorem u5297 : Upper (D 6) (R 6) [10,384,48,68,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5298 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 386 52 76 82 33 68 161 289), lower := (rows 11 386 52 76 82 33 68 128 256), losses := [] }

theorem u5298 : Upper (D 6) (R 6) [10,384,48,68,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5299 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 386 52 76 82 33 96 133 261), lower := (rows 11 386 52 76 82 33 96 128 256), losses := [] }

theorem u5299 : Upper (D 6) (R 6) [10,384,48,68,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5300 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 52 104 22 33 65 196 324), lower := (rows 11 386 52 104 22 33 65 128 256), losses := [] }

theorem u5300 : Upper (D 6) (R 6) [10,384,48,96,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5301 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 386 52 104 22 33 68 193 321), lower := (rows 11 386 52 104 22 33 68 128 256), losses := [] }

theorem u5301 : Upper (D 6) (R 6) [10,384,48,96,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5302 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 386 52 104 82 33 65 132 260), lower := (rows 11 386 52 104 82 33 65 128 256), losses := [] }

theorem u5302 : Upper (D 6) (R 6) [10,384,48,96,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5303 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 11 386 52 104 82 33 68 133 261), lower := (rows 11 386 52 104 82 33 68 128 256), losses := [] }

theorem u5303 : Upper (D 6) (R 6) [10,384,48,96,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5304 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 100 41 82 36 65 148 276), lower := (rows 11 386 100 41 82 36 65 128 256), losses := [] }

theorem u5304 : Upper (D 6) (R 6) [10,384,96,33,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5305 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 386 100 41 82 36 68 145 273), lower := (rows 11 386 100 41 82 36 68 128 256), losses := [] }

theorem u5305 : Upper (D 6) (R 6) [10,384,96,33,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5306 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 386 100 41 82 36 80 133 261), lower := (rows 11 386 100 41 82 36 80 128 256), losses := [] }

theorem u5306 : Upper (D 6) (R 6) [10,384,96,33,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5306 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5307 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 400, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 35 69 14 400 34 96 196 324), lower := (rows 25 35 69 14 400 34 96 128 256), losses := [] }

theorem u5307 : Upper (D 6) (R 6) [24,33,65,6,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5308 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 464, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,2)], upper := (rows 25 35 69 14 400 36 96 194 322), lower := (rows 25 35 69 14 400 36 96 128 256), losses := [] }

theorem u5308 : Upper (D 6) (R 6) [24,33,65,6,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5309 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 401, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 35 69 14 400 96 96 134 262), lower := (rows 25 35 69 14 400 96 96 128 256), losses := [] }

theorem u5309 : Upper (D 6) (R 6) [24,33,65,6,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5310 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 2 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 69 138 274 96 68 164 292), lower := (rows 25 35 69 138 274 96 68 128 256), losses := [] }

theorem u5310 : Upper (D 6) (R 6) [24,33,65,130,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5311 : Route 9 := (fun mask => (mask,id))

def c5311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 2 | 16 => 2 | 32 => 2 | 64 => 2 | 256 => 2 | _ => 0)

theorem u5311 : Upper (D 6) (R 6) [24,33,65,130,258,64,32] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,258,64,32] 13 (by decide) (choices 1) [4] r5311 c5311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u386

def b5312 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 35 69 138 276 34 96 196 324), lower := (rows 25 35 69 138 276 34 96 128 256), losses := [] }

theorem u5312 : Upper (D 6) (R 6) [24,33,65,130,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5313 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 200, targets := 5 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(3,2)], upper := (rows 25 35 69 138 276 36 96 194 322), lower := (rows 25 35 69 138 276 36 96 128 256), losses := [] }

theorem u5313 : Upper (D 6) (R 6) [24,33,65,130,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5314 : Route 9 := (fun mask => (mask,id))

def c5314 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5314 : Upper (D 6) (R 6) [24,33,65,130,260,64,32] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,260,64,32] 13 (by decide) (choices 1) [2,4] r5314 c5314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u387
  · exact u388

def b5315 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,1)], upper := (rows 25 35 69 138 336 36 66 164 292), lower := (rows 25 35 69 138 336 36 66 128 256), losses := [] }

theorem u5315 : Upper (D 6) (R 6) [24,33,65,130,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5316 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 136, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 69 138 336 36 68 162 290), lower := (rows 25 35 69 138 336 36 68 128 256), losses := [] }

theorem u5316 : Upper (D 6) (R 6) [24,33,65,130,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5317 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 170, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(3,6)], upper := (rows 25 35 69 138 336 36 96 134 262), lower := (rows 25 35 69 138 336 36 96 128 256), losses := [] }

theorem u5317 : Upper (D 6) (R 6) [24,33,65,130,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5318 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 1, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 70 137 274 96 68 164 292), lower := (rows 25 35 70 137 274 96 68 128 256), losses := [] }

theorem u5318 : Upper (D 6) (R 6) [24,33,66,129,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5319 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 409, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 35 70 137 274 96 96 132 260), lower := (rows 25 35 70 137 274 96 96 128 256), losses := [] }

theorem u5319 : Upper (D 6) (R 6) [24,33,66,129,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5320 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 35 70 137 276 96 66 164 292), lower := (rows 25 35 70 137 276 96 66 128 256), losses := [] }

theorem u5320 : Upper (D 6) (R 6) [24,33,66,129,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5321 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 1, region := 136, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 70 137 276 96 68 162 290), lower := (rows 25 35 70 137 276 96 68 128 256), losses := [] }

theorem u5321 : Upper (D 6) (R 6) [24,33,66,129,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5322 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 409, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 35 70 137 276 96 96 134 262), lower := (rows 25 35 70 137 276 96 96 128 256), losses := [] }

theorem u5322 : Upper (D 6) (R 6) [24,33,66,129,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5323 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 35 70 137 336 36 66 164 292), lower := (rows 25 35 70 137 336 36 66 128 256), losses := [] }

theorem u5323 : Upper (D 6) (R 6) [24,33,66,129,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5324 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 1, region := 136, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 70 137 336 36 68 162 290), lower := (rows 25 35 70 137 336 36 68 128 256), losses := [] }

theorem u5324 : Upper (D 6) (R 6) [24,33,66,129,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5325 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 35 70 137 336 36 96 134 262), lower := (rows 25 35 70 137 336 36 96 128 256), losses := [] }

theorem u5325 : Upper (D 6) (R 6) [24,33,66,129,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5326 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 25 35 70 138 276 96 65 164 292), lower := (rows 25 35 70 138 276 96 65 128 256), losses := [] }

theorem u5326 : Upper (D 6) (R 6) [24,33,66,130,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5327 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 136, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(3,2),(3,6)], upper := (rows 25 35 70 138 276 96 68 161 289), lower := (rows 25 35 70 138 276 96 68 128 256), losses := [] }

theorem u5327 : Upper (D 6) (R 6) [24,33,66,130,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5328 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 35 70 138 276 96 96 133 261), lower := (rows 25 35 70 138 276 96 96 128 256), losses := [] }

theorem u5328 : Upper (D 6) (R 6) [24,33,66,130,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5329 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 2, region := 136, targets := 1 }], pairs := [(2,5),(3,0),(3,5)], upper := (rows 25 35 70 138 304 36 65 196 324), lower := (rows 25 35 70 138 304 36 65 128 256), losses := [] }

theorem u5329 : Upper (D 6) (R 6) [24,33,66,130,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5330 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(3,5)], upper := (rows 25 35 70 138 304 36 68 193 321), lower := (rows 25 35 70 138 304 36 68 128 256), losses := [] }

theorem u5330 : Upper (D 6) (R 6) [24,33,66,130,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5331 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 2, region := 136, targets := 1 }], pairs := [(2,5),(3,0),(3,5)], upper := (rows 25 35 70 138 304 96 65 132 260), lower := (rows 25 35 70 138 304 96 65 128 256), losses := [] }

theorem u5331 : Upper (D 6) (R 6) [24,33,66,130,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5332 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(3,5)], upper := (rows 25 35 70 138 304 96 68 133 261), lower := (rows 25 35 70 138 304 96 68 128 256), losses := [] }

theorem u5332 : Upper (D 6) (R 6) [24,33,66,130,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5333 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 1 },{ cop := 1, region := 68, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 25 35 70 138 336 36 65 164 292), lower := (rows 25 35 70 138 336 36 65 128 256), losses := [] }

theorem u5333 : Upper (D 6) (R 6) [24,33,66,130,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5334 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 136, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(3,2),(3,6)], upper := (rows 25 35 70 138 336 36 68 161 289), lower := (rows 25 35 70 138 336 36 68 128 256), losses := [] }

theorem u5334 : Upper (D 6) (R 6) [24,33,66,130,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5335 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 35 70 138 336 36 96 133 261), lower := (rows 25 35 70 138 336 36 96 128 256), losses := [] }

theorem u5335 : Upper (D 6) (R 6) [24,33,66,130,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5336 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 2, region := 136, targets := 1 }], pairs := [(2,5),(3,0),(3,5)], upper := (rows 25 35 70 140 304 96 65 134 262), lower := (rows 25 35 70 140 304 96 65 128 256), losses := [] }

theorem u5336 : Upper (D 6) (R 6) [24,33,66,132,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5337 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 35 70 140 304 96 66 133 261), lower := (rows 25 35 70 140 304 96 66 128 256), losses := [] }

theorem u5337 : Upper (D 6) (R 6) [24,33,66,132,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5338 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 1, region := 68, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 25 35 70 140 304 96 68 131 259), lower := (rows 25 35 70 140 304 96 68 128 256), losses := [] }

theorem u5338 : Upper (D 6) (R 6) [24,33,66,132,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5339 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 1 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 25 35 70 140 336 34 65 164 292), lower := (rows 25 35 70 140 336 34 65 128 256), losses := [] }

theorem u5339 : Upper (D 6) (R 6) [24,33,66,132,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5339
end Delivery.IrregularNine14.P06
