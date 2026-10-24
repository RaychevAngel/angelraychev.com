import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0045

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r13380 : Route 9 := (fun mask => (mask,id))

def c13380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13380 : Upper (D 6) (R 6) [10,36,129,20,320,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,320,64] 13 (by decide) (choices 1) [1,2,32] r13380 c13380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2711
  · exact u2712
  · exact u2713

def b13381 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 133 56 84 33 322 450 322), lower := (rows 11 38 133 56 84 33 64 128 256), losses := [] }

theorem u13381 : Upper (D 6) (R 6) [10,36,129,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13382 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 56 84 34 321 449 321), lower := (rows 11 38 133 56 84 34 64 128 256), losses := [] }

theorem u13382 : Upper (D 6) (R 6) [10,36,129,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13383 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 56 84 96 323 387 259), lower := (rows 11 38 133 56 84 96 64 128 256), losses := [] }

theorem u13383 : Upper (D 6) (R 6) [10,36,129,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13384 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 56 84 288 67 195 323), lower := (rows 11 38 133 56 84 288 64 128 256), losses := [] }

theorem u13384 : Upper (D 6) (R 6) [10,36,129,48,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13384 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13385 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 133 56 276 33 66 194 322), lower := (rows 11 38 133 56 276 33 64 128 256), losses := [] }

theorem u13385 : Upper (D 6) (R 6) [10,36,129,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13386 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 56 276 34 65 193 321), lower := (rows 11 38 133 56 276 34 64 128 256), losses := [] }

theorem u13386 : Upper (D 6) (R 6) [10,36,129,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13387 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,2),(4,5)], upper := (rows 11 38 133 56 276 96 67 195 323), lower := (rows 11 38 133 56 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 101 65 129 257), good := (rows 491 34 481 56 312 96 96 128 256) }] }

theorem u13387 : Upper (D 6) (R 6) [10,36,129,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13388 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 344, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 133 56 336 33 70 198 326), lower := (rows 11 38 133 56 336 33 64 128 256), losses := [] }

theorem u13388 : Upper (D 6) (R 6) [10,36,129,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13389 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 56 336 34 69 197 325), lower := (rows 11 38 133 56 336 34 64 128 256), losses := [] }

theorem u13389 : Upper (D 6) (R 6) [10,36,129,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13390 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 56 336 36 67 195 323), lower := (rows 11 38 133 56 336 36 64 128 256), losses := [] }

theorem u13390 : Upper (D 6) (R 6) [10,36,129,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13391 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 56 336 96 71 135 263), lower := (rows 11 38 133 56 336 96 64 128 256), losses := [] }

theorem u13391 : Upper (D 6) (R 6) [10,36,129,48,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13392 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 73 112 34 340 404 276), lower := (rows 11 38 133 73 112 34 64 128 256), losses := [] }

theorem u13392 : Upper (D 6) (R 6) [10,36,129,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13393 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 73 112 36 338 402 274), lower := (rows 11 38 133 73 112 36 64 128 256), losses := [] }

theorem u13393 : Upper (D 6) (R 6) [10,36,129,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13394 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 73 112 48 326 390 262), lower := (rows 11 38 133 73 112 48 64 128 256), losses := [] }

theorem u13394 : Upper (D 6) (R 6) [10,36,129,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13394 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13395 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 133 73 112 288 86 150 278), lower := (rows 11 38 133 73 112 288 64 128 256), losses := [] }

theorem u13395 : Upper (D 6) (R 6) [10,36,129,65,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13395 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13396 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 73 274 36 112 240 368), lower := (rows 11 38 133 73 274 36 64 128 256), losses := [] }

theorem u13396 : Upper (D 6) (R 6) [10,36,129,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13397 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 133 73 274 48 100 228 356), lower := (rows 11 38 133 73 274 48 64 128 256), losses := [] }

theorem u13397 : Upper (D 6) (R 6) [10,36,129,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13397 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13398 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 133 73 274 96 116 180 308), lower := (rows 11 38 133 73 274 96 64 128 256), losses := [] }

theorem u13398 : Upper (D 6) (R 6) [10,36,129,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13399 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 73 276 34 112 240 368), lower := (rows 11 38 133 73 276 34 64 128 256), losses := [] }

theorem u13399 : Upper (D 6) (R 6) [10,36,129,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13400 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 133 73 276 48 98 226 354), lower := (rows 11 38 133 73 276 48 64 128 256), losses := [] }

theorem u13400 : Upper (D 6) (R 6) [10,36,129,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13400 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13401 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 133 73 276 96 114 178 306), lower := (rows 11 38 133 73 276 96 64 128 256), losses := [] }

theorem u13401 : Upper (D 6) (R 6) [10,36,129,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13402 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 73 304 34 84 212 340), lower := (rows 11 38 133 73 304 34 64 128 256), losses := [] }

theorem u13402 : Upper (D 6) (R 6) [10,36,129,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13403 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 73 304 36 82 210 338), lower := (rows 11 38 133 73 304 36 64 128 256), losses := [] }

theorem u13403 : Upper (D 6) (R 6) [10,36,129,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13404 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 133 73 304 48 70 198 326), lower := (rows 11 38 133 73 304 48 64 128 256), losses := [] }

theorem u13404 : Upper (D 6) (R 6) [10,36,129,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13404 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13405 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 133 73 304 96 86 150 278), lower := (rows 11 38 133 73 304 96 64 128 256), losses := [] }

theorem u13405 : Upper (D 6) (R 6) [10,36,129,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13406 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 73 336 34 116 180 308), lower := (rows 11 38 133 73 336 34 64 128 256), losses := [] }

theorem u13406 : Upper (D 6) (R 6) [10,36,129,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13407 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 73 336 36 114 178 306), lower := (rows 11 38 133 73 336 36 64 128 256), losses := [] }

theorem u13407 : Upper (D 6) (R 6) [10,36,129,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13408 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 133 73 336 48 102 166 294), lower := (rows 11 38 133 73 336 48 64 128 256), losses := [] }

theorem u13408 : Upper (D 6) (R 6) [10,36,129,65,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13408 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13409 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 133 76 49 34 336 464 336), lower := (rows 11 38 133 76 49 34 64 128 256), losses := [] }

theorem u13409 : Upper (D 6) (R 6) [10,36,129,68,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13410 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 76 49 48 322 450 322), lower := (rows 11 38 133 76 49 48 64 128 256), losses := [] }

theorem u13410 : Upper (D 6) (R 6) [10,36,129,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13410 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13411 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 390, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 11 38 133 76 49 96 338 402 274), lower := (rows 11 38 133 76 49 96 64 128 256), losses := [] }

theorem u13411 : Upper (D 6) (R 6) [10,36,129,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13412 : Route 9 := (fun mask => (mask,id))

def c13412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13412 : Upper (D 6) (R 6) [10,36,129,68,33,256] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,33,256] 13 (by decide) (choices 1) [2,16] r13412 c13412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2714
  · exact u2715

def b13413 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 76 82 33 368 432 304), lower := (rows 11 38 133 76 82 33 64 128 256), losses := [] }

theorem u13413 : Upper (D 6) (R 6) [10,36,129,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13414 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 133 76 82 48 353 417 289), lower := (rows 11 38 133 76 82 48 64 128 256), losses := [] }

theorem u13414 : Upper (D 6) (R 6) [10,36,129,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13414 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13415 : Route 9 := (fun mask => (mask,id))

def c13415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13415 : Upper (D 6) (R 6) [10,36,129,68,66,256] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,66,256] 13 (by decide) (choices 1) [1,16,32] r13415 c13415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2716
  · exact u2717
  · exact u2718

def b13416 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 76 112 33 338 402 274), lower := (rows 11 38 133 76 112 33 64 128 256), losses := [] }

theorem u13416 : Upper (D 6) (R 6) [10,36,129,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13417 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 133 76 112 34 337 401 273), lower := (rows 11 38 133 76 112 34 64 128 256), losses := [] }

theorem u13417 : Upper (D 6) (R 6) [10,36,129,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13418 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 76 112 48 323 387 259), lower := (rows 11 38 133 76 112 48 64 128 256), losses := [] }

theorem u13418 : Upper (D 6) (R 6) [10,36,129,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13418 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13419 : Route 9 := (fun mask => (mask,id))

def c13419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13419 : Upper (D 6) (R 6) [10,36,129,68,96,256] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,96,256] 13 (by decide) (choices 1) [1,2,16] r13419 c13419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2719
  · exact u2720
  · exact u2721

def b13420 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 133 76 273 34 112 240 368), lower := (rows 11 38 133 76 273 34 64 128 256), losses := [] }

theorem u13420 : Upper (D 6) (R 6) [10,36,129,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13421 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0),(4,2)], upper := (rows 11 38 133 76 273 48 98 226 354), lower := (rows 11 38 133 76 273 48 64 128 256), losses := [] }

theorem u13421 : Upper (D 6) (R 6) [10,36,129,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13421 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13422 : Route 9 := (fun mask => (mask,id))

def c13422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13422 : Upper (D 6) (R 6) [10,36,129,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,257,64] 13 (by decide) (choices 1) [2,16,32] r13422 c13422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2722
  · exact u2723
  · exact u2724

def b13423 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 76 274 33 112 240 368), lower := (rows 11 38 133 76 274 33 64 128 256), losses := [] }

theorem u13423 : Upper (D 6) (R 6) [10,36,129,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13424 : Route 9 := (fun mask => (mask,id))

def c13424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13424 : Upper (D 6) (R 6) [10,36,129,68,258,16] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,258,16] 13 (by decide) (choices 1) [1,32] r13424 c13424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2725
  · exact u2726

def r13425 : Route 9 := (fun mask => (mask,id))

def c13425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13425 : Upper (D 6) (R 6) [10,36,129,68,258,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,258,64] 13 (by decide) (choices 1) [1,16,32] r13425 c13425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2727
  · exact u2728
  · exact u2729

def b13426 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 76 304 33 82 210 338), lower := (rows 11 38 133 76 304 33 64 128 256), losses := [] }

theorem u13426 : Upper (D 6) (R 6) [10,36,129,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13427 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 133 76 304 34 81 209 337), lower := (rows 11 38 133 76 304 34 64 128 256), losses := [] }

theorem u13427 : Upper (D 6) (R 6) [10,36,129,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13428 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 133 76 304 48 67 195 323), lower := (rows 11 38 133 76 304 48 64 128 256), losses := [] }

theorem u13428 : Upper (D 6) (R 6) [10,36,129,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13428 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13429 : Route 9 := (fun mask => (mask,id))

def c13429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13429 : Upper (D 6) (R 6) [10,36,129,68,288,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,288,64] 13 (by decide) (choices 1) [1,2,16] r13429 c13429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2730
  · exact u2731
  · exact u2732

def b13430 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 76 336 33 114 178 306), lower := (rows 11 38 133 76 336 33 64 128 256), losses := [] }

theorem u13430 : Upper (D 6) (R 6) [10,36,129,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13431 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 133 76 336 34 113 177 305), lower := (rows 11 38 133 76 336 34 64 128 256), losses := [] }

theorem u13431 : Upper (D 6) (R 6) [10,36,129,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13432 : Route 9 := (fun mask => (mask,id))

def c13432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13432 : Upper (D 6) (R 6) [10,36,129,68,320,16] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,320,16] 13 (by decide) (choices 1) [1,2,32] r13432 c13432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2733
  · exact u2734
  · exact u2735

def b13433 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 34, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 38 133 88 273 34 100 228 356), lower := (rows 11 38 133 88 273 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 17 32 66 130 258), good := (rows 477 484 157 88 285 480 64 128 256) }] }

theorem u13433 : Upper (D 6) (R 6) [10,36,129,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13434 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 88 273 36 98 226 354), lower := (rows 11 38 133 88 273 36 64 128 256), losses := [] }

theorem u13434 : Upper (D 6) (R 6) [10,36,129,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13435 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 38 133 88 273 96 102 166 294), lower := (rows 11 38 133 88 273 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 17 32 0 130 258), good := (rows 415 422 149 24 277 32 0 128 256) }] }

theorem u13435 : Upper (D 6) (R 6) [10,36,129,80,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13436 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 38 133 88 274 33 100 228 356), lower := (rows 11 38 133 88 274 33 64 128 256), losses := [] }

theorem u13436 : Upper (D 6) (R 6) [10,36,129,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13437 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 88 274 36 97 225 353), lower := (rows 11 38 133 88 274 36 64 128 256), losses := [] }

theorem u13437 : Upper (D 6) (R 6) [10,36,129,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13438 : Route 9 := (fun mask => (mask,id))

def c13438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13438 : Upper (D 6) (R 6) [10,36,129,80,258,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,80,258,64] 13 (by decide) (choices 1) [1,4,32] r13438 c13438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2736
  · exact u2737
  · exact u2738

def b13439 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 133 88 276 33 98 226 354), lower := (rows 11 38 133 88 276 33 64 128 256), losses := [] }

theorem u13439 : Upper (D 6) (R 6) [10,36,129,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13439
end Delivery.IrregularNine14.P06
