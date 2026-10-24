import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0097

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19380 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 138 21 96 340 404 276), lower := (rows 35 67 44 138 21 96 64 128 256), losses := [] }

theorem u19380 : Upper (D 6) (R 6) [34,65,40,130,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19381 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 44 138 21 288 84 212 340), lower := (rows 35 67 44 138 21 288 64 128 256), losses := [] }

theorem u19381 : Upper (D 6) (R 6) [34,65,40,130,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19381 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19382 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 138 84 33 340 404 276), lower := (rows 35 67 44 138 84 33 64 128 256), losses := [] }

theorem u19382 : Upper (D 6) (R 6) [34,65,40,130,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19383 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 44 138 84 36 337 401 273), lower := (rows 35 67 44 138 84 36 64 128 256), losses := [] }

theorem u19383 : Upper (D 6) (R 6) [34,65,40,130,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19384 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 138 84 48 325 389 261), lower := (rows 35 67 44 138 84 48 64 128 256), losses := [] }

theorem u19384 : Upper (D 6) (R 6) [34,65,40,130,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19384 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19385 : Route 9 := (fun mask => (mask,id))

def c19385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19385 : Upper (D 6) (R 6) [34,65,40,130,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,68,256] 13 (by decide) (choices 1) [1,4,16] r19385 c19385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5826
  · exact u5827
  · exact u5828

def b19386 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 44 138 273 36 84 212 340), lower := (rows 35 67 44 138 273 36 64 128 256), losses := [] }

theorem u19386 : Upper (D 6) (R 6) [34,65,40,130,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19387 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 138 273 48 68 196 324), lower := (rows 35 67 44 138 273 48 64 128 256), losses := [] }

theorem u19387 : Upper (D 6) (R 6) [34,65,40,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19387 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19388 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 138 273 96 84 148 276), lower := (rows 35 67 44 138 273 96 64 128 256), losses := [] }

theorem u19388 : Upper (D 6) (R 6) [34,65,40,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19389 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 138 276 33 84 212 340), lower := (rows 35 67 44 138 276 33 64 128 256), losses := [] }

theorem u19389 : Upper (D 6) (R 6) [34,65,40,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19390 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 44 138 276 36 81 209 337), lower := (rows 35 67 44 138 276 36 64 128 256), losses := [] }

theorem u19390 : Upper (D 6) (R 6) [34,65,40,130,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19391 : Route 9 := (fun mask => (mask,id))

def c19391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19391 : Upper (D 6) (R 6) [34,65,40,130,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,260,16] 13 (by decide) (choices 1) [1,4] r19391 c19391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5829
  · exact u5830

def b19392 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 138 276 96 85 149 277), lower := (rows 35 67 44 138 276 96 64 128 256), losses := [] }

theorem u19392 : Upper (D 6) (R 6) [34,65,40,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19393 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 138 336 33 84 148 276), lower := (rows 35 67 44 138 336 33 64 128 256), losses := [] }

theorem u19393 : Upper (D 6) (R 6) [34,65,40,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19394 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 44 138 336 36 85 149 277), lower := (rows 35 67 44 138 336 36 64 128 256), losses := [] }

theorem u19394 : Upper (D 6) (R 6) [34,65,40,130,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19395 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 138 336 48 69 133 261), lower := (rows 35 67 44 138 336 48 64 128 256), losses := [] }

theorem u19395 : Upper (D 6) (R 6) [34,65,40,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19395 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19396 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 140 22 33 336 464 336), lower := (rows 35 67 44 140 22 33 64 128 256), losses := [] }

theorem u19396 : Upper (D 6) (R 6) [34,65,40,132,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19397 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 140 22 48 321 449 321), lower := (rows 35 67 44 140 22 48 64 128 256), losses := [] }

theorem u19397 : Upper (D 6) (R 6) [34,65,40,132,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19397 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19398 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 140 22 96 337 401 273), lower := (rows 35 67 44 140 22 96 64 128 256), losses := [] }

theorem u19398 : Upper (D 6) (R 6) [34,65,40,132,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19399 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 140 22 288 81 209 337), lower := (rows 35 67 44 140 22 288 64 128 256), losses := [] }

theorem u19399 : Upper (D 6) (R 6) [34,65,40,132,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19399 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19400 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 140 84 33 338 402 274), lower := (rows 35 67 44 140 84 33 64 128 256), losses := [] }

theorem u19400 : Upper (D 6) (R 6) [34,65,40,132,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19401 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 140 84 34 337 401 273), lower := (rows 35 67 44 140 84 34 64 128 256), losses := [] }

theorem u19401 : Upper (D 6) (R 6) [34,65,40,132,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19402 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 322, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 67 44 140 84 48 323 387 259), lower := (rows 35 67 44 140 84 48 64 128 256), losses := [] }

theorem u19402 : Upper (D 6) (R 6) [34,65,40,132,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19402 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19403 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 140 84 288 83 147 275), lower := (rows 35 67 44 140 84 288 64 128 256), losses := [] }

theorem u19403 : Upper (D 6) (R 6) [34,65,40,132,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19403 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19404 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 140 273 34 84 212 340), lower := (rows 35 67 44 140 273 34 64 128 256), losses := [] }

theorem u19404 : Upper (D 6) (R 6) [34,65,40,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19405 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 140 273 36 82 210 338), lower := (rows 35 67 44 140 273 36 64 128 256), losses := [] }

theorem u19405 : Upper (D 6) (R 6) [34,65,40,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19406 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 140 273 48 70 198 326), lower := (rows 35 67 44 140 273 48 64 128 256), losses := [] }

theorem u19406 : Upper (D 6) (R 6) [34,65,40,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19406 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19407 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 140 273 96 86 150 278), lower := (rows 35 67 44 140 273 96 64 128 256), losses := [] }

theorem u19407 : Upper (D 6) (R 6) [34,65,40,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19408 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 140 274 33 84 212 340), lower := (rows 35 67 44 140 274 33 64 128 256), losses := [] }

theorem u19408 : Upper (D 6) (R 6) [34,65,40,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19409 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 140 274 36 81 209 337), lower := (rows 35 67 44 140 274 36 64 128 256), losses := [] }

theorem u19409 : Upper (D 6) (R 6) [34,65,40,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19410 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 140 274 48 69 197 325), lower := (rows 35 67 44 140 274 48 64 128 256), losses := [] }

theorem u19410 : Upper (D 6) (R 6) [34,65,40,132,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19410 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19411 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 140 274 96 85 149 277), lower := (rows 35 67 44 140 274 96 64 128 256), losses := [] }

theorem u19411 : Upper (D 6) (R 6) [34,65,40,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19412 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 140 276 33 82 210 338), lower := (rows 35 67 44 140 276 33 64 128 256), losses := [] }

theorem u19412 : Upper (D 6) (R 6) [34,65,40,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19413 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 140 276 34 81 209 337), lower := (rows 35 67 44 140 276 34 64 128 256), losses := [] }

theorem u19413 : Upper (D 6) (R 6) [34,65,40,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19414 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 66, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 67 44 140 276 48 67 195 323), lower := (rows 35 67 44 140 276 48 64 128 256), losses := [] }

theorem u19414 : Upper (D 6) (R 6) [34,65,40,132,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19414 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19415 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 140 276 96 83 147 275), lower := (rows 35 67 44 140 276 96 64 128 256), losses := [] }

theorem u19415 : Upper (D 6) (R 6) [34,65,40,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19416 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 140 336 33 86 150 278), lower := (rows 35 67 44 140 336 33 64 128 256), losses := [] }

theorem u19416 : Upper (D 6) (R 6) [34,65,40,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19417 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 140 336 34 85 149 277), lower := (rows 35 67 44 140 336 34 64 128 256), losses := [] }

theorem u19417 : Upper (D 6) (R 6) [34,65,40,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19418 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 140 336 36 83 147 275), lower := (rows 35 67 44 140 336 36 64 128 256), losses := [] }

theorem u19418 : Upper (D 6) (R 6) [34,65,40,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19419 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 140 336 48 71 135 263), lower := (rows 35 67 44 140 336 48 64 128 256), losses := [] }

theorem u19419 : Upper (D 6) (R 6) [34,65,40,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19419 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19420 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 152 21 34 324 452 324), lower := (rows 35 67 44 152 21 34 64 128 256), losses := [] }

theorem u19420 : Upper (D 6) (R 6) [34,65,40,144,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19421 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 67 44 152 21 36 322 450 322), lower := (rows 35 67 44 152 21 36 64 128 256), losses := [] }

theorem u19421 : Upper (D 6) (R 6) [34,65,40,144,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19422 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 152 21 96 326 390 262), lower := (rows 35 67 44 152 21 96 64 128 256), losses := [] }

theorem u19422 : Upper (D 6) (R 6) [34,65,40,144,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19423 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 44 152 21 288 70 198 326), lower := (rows 35 67 44 152 21 288 64 128 256), losses := [] }

theorem u19423 : Upper (D 6) (R 6) [34,65,40,144,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19423 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19424 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 152 22 33 324 452 324), lower := (rows 35 67 44 152 22 33 64 128 256), losses := [] }

theorem u19424 : Upper (D 6) (R 6) [34,65,40,144,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19425 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 22 36 321 449 321), lower := (rows 35 67 44 152 22 36 64 128 256), losses := [] }

theorem u19425 : Upper (D 6) (R 6) [34,65,40,144,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19426 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 152 22 96 325 389 261), lower := (rows 35 67 44 152 22 96 64 128 256), losses := [] }

theorem u19426 : Upper (D 6) (R 6) [34,65,40,144,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19427 : Route 9 := (fun mask => (mask,id))

def c19427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19427 : Upper (D 6) (R 6) [34,65,40,144,6,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,6,256] 13 (by decide) (choices 1) [1,4] r19427 c19427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5831
  · exact u5832

def b19428 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 152 84 33 326 390 262), lower := (rows 35 67 44 152 84 33 64 128 256), losses := [] }

theorem u19428 : Upper (D 6) (R 6) [34,65,40,144,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19429 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 152 84 34 325 389 261), lower := (rows 35 67 44 152 84 34 64 128 256), losses := [] }

theorem u19429 : Upper (D 6) (R 6) [34,65,40,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19430 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 84 36 323 387 259), lower := (rows 35 67 44 152 84 36 64 128 256), losses := [] }

theorem u19430 : Upper (D 6) (R 6) [34,65,40,144,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19431 : Route 9 := (fun mask => (mask,id))

def c19431 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19431 : Upper (D 6) (R 6) [34,65,40,144,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,68,256] 13 (by decide) (choices 1) [1,2,4] r19431 c19431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5833
  · exact u5834
  · exact u5835

def b19432 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 152 273 34 68 196 324), lower := (rows 35 67 44 152 273 34 64 128 256), losses := [] }

theorem u19432 : Upper (D 6) (R 6) [34,65,40,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19433 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 273 36 70 198 326), lower := (rows 35 67 44 152 273 36 64 128 256), losses := [] }

theorem u19433 : Upper (D 6) (R 6) [34,65,40,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19434 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 152 273 96 70 134 262), lower := (rows 35 67 44 152 273 96 64 128 256), losses := [] }

theorem u19434 : Upper (D 6) (R 6) [34,65,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19435 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 152 274 33 68 196 324), lower := (rows 35 67 44 152 274 33 64 128 256), losses := [] }

theorem u19435 : Upper (D 6) (R 6) [34,65,40,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19436 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 274 36 69 197 325), lower := (rows 35 67 44 152 274 36 64 128 256), losses := [] }

theorem u19436 : Upper (D 6) (R 6) [34,65,40,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19437 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 152 274 96 69 133 261), lower := (rows 35 67 44 152 274 96 64 128 256), losses := [] }

theorem u19437 : Upper (D 6) (R 6) [34,65,40,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19438 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 152 276 33 70 198 326), lower := (rows 35 67 44 152 276 33 64 128 256), losses := [] }

theorem u19438 : Upper (D 6) (R 6) [34,65,40,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19439 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 152 276 34 69 197 325), lower := (rows 35 67 44 152 276 34 64 128 256), losses := [] }

theorem u19439 : Upper (D 6) (R 6) [34,65,40,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19439
end Delivery.IrregularNine14.P06
