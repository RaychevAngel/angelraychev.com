import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0039

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12360 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 140 276 96 83 147 275), lower := (rows 11 35 100 140 276 96 64 128 256), losses := [] }

theorem u12360 : Upper (D 6) (R 6) [10,33,96,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12361 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 140 336 33 86 150 278), lower := (rows 11 35 100 140 336 33 64 128 256), losses := [] }

theorem u12361 : Upper (D 6) (R 6) [10,33,96,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12362 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 140 336 34 85 149 277), lower := (rows 11 35 100 140 336 34 64 128 256), losses := [] }

theorem u12362 : Upper (D 6) (R 6) [10,33,96,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12363 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 100 140 336 36 83 147 275), lower := (rows 11 35 100 140 336 36 64 128 256), losses := [] }

theorem u12363 : Upper (D 6) (R 6) [10,33,96,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12364 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 140 336 48 71 135 263), lower := (rows 11 35 100 140 336 48 64 128 256), losses := [] }

theorem u12364 : Upper (D 6) (R 6) [10,33,96,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12364 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12365 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 21 34 324 452 324), lower := (rows 11 35 100 152 21 34 64 128 256), losses := [] }

theorem u12365 : Upper (D 6) (R 6) [10,33,96,144,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12366 : PairBound 9 := { available := 322, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 35 100 152 21 36 322 450 322), lower := (rows 11 35 100 152 21 36 64 128 256), losses := [] }

theorem u12366 : Upper (D 6) (R 6) [10,33,96,144,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12367 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 152 21 96 326 390 262), lower := (rows 11 35 100 152 21 96 64 128 256), losses := [] }

theorem u12367 : Upper (D 6) (R 6) [10,33,96,144,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12368 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 100 152 21 288 70 198 326), lower := (rows 11 35 100 152 21 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 307 67 131 259), good := (rows 494 486 100 188 508 288 64 128 288) }] }

theorem u12368 : Upper (D 6) (R 6) [10,33,96,144,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12368 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12369 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 81 34 324 388 260), lower := (rows 11 35 100 152 81 34 64 128 256), losses := [] }

theorem u12369 : Upper (D 6) (R 6) [10,33,96,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12370 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 152 81 36 326 390 262), lower := (rows 11 35 100 152 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 87 24 16 127 67 131 259), good := (rows 494 486 100 188 508 36 100 128 256) }] }

theorem u12370 : Upper (D 6) (R 6) [10,33,96,144,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12371 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 100 152 81 288 70 134 262), lower := (rows 11 35 100 152 81 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 307 67 131 259), good := (rows 494 486 100 188 508 288 64 128 288) }] }

theorem u12371 : Upper (D 6) (R 6) [10,33,96,144,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12371 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12372 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 82 33 324 388 260), lower := (rows 11 35 100 152 82 33 64 128 256), losses := [] }

theorem u12372 : Upper (D 6) (R 6) [10,33,96,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12373 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 35 100 152 82 36 325 389 261), lower := (rows 11 35 100 152 82 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 127 67 131 259), good := (rows 493 485 100 188 508 36 100 128 256) }] }

theorem u12373 : Upper (D 6) (R 6) [10,33,96,144,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12374 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 100 152 82 288 69 133 261), lower := (rows 11 35 100 152 82 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 307 67 131 259), good := (rows 493 485 100 188 508 288 64 128 288) }] }

theorem u12374 : Upper (D 6) (R 6) [10,33,96,144,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12374 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12375 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 273 34 68 196 324), lower := (rows 11 35 100 152 273 34 64 128 256), losses := [] }

theorem u12375 : Upper (D 6) (R 6) [10,33,96,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12376 : PairBound 9 := { available := 70, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 152 273 36 70 198 326), lower := (rows 11 35 100 152 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 87 24 16 127 67 131 259), good := (rows 494 486 100 188 508 36 100 128 256) }] }

theorem u12376 : Upper (D 6) (R 6) [10,33,96,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12377 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 152 273 96 70 134 262), lower := (rows 11 35 100 152 273 96 64 128 256), losses := [] }

theorem u12377 : Upper (D 6) (R 6) [10,33,96,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12378 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 274 33 68 196 324), lower := (rows 11 35 100 152 274 33 64 128 256), losses := [] }

theorem u12378 : Upper (D 6) (R 6) [10,33,96,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12379 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 35 100 152 274 36 69 197 325), lower := (rows 11 35 100 152 274 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 127 67 131 259), good := (rows 493 485 100 188 508 36 100 128 256) }] }

theorem u12379 : Upper (D 6) (R 6) [10,33,96,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12380 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 152 274 96 69 133 261), lower := (rows 11 35 100 152 274 96 64 128 256), losses := [] }

theorem u12380 : Upper (D 6) (R 6) [10,33,96,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12381 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 276 33 70 198 326), lower := (rows 11 35 100 152 276 33 64 128 256), losses := [] }

theorem u12381 : Upper (D 6) (R 6) [10,33,96,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12382 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 276 34 69 197 325), lower := (rows 11 35 100 152 276 34 64 128 256), losses := [] }

theorem u12382 : Upper (D 6) (R 6) [10,33,96,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12383 : PairBound 9 := { available := 67, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 11 35 100 152 276 36 67 195 323), lower := (rows 11 35 100 152 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 10 4 8 16 52 0 128 256), good := (rows 11 35 36 187 308 36 0 128 256) }] }

theorem u12383 : Upper (D 6) (R 6) [10,33,96,144,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12384 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 152 276 96 71 135 263), lower := (rows 11 35 100 152 276 96 64 128 256), losses := [] }

theorem u12384 : Upper (D 6) (R 6) [10,33,96,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12385 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 336 33 70 134 262), lower := (rows 11 35 100 152 336 33 64 128 256), losses := [] }

theorem u12385 : Upper (D 6) (R 6) [10,33,96,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12386 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 152 336 34 69 133 261), lower := (rows 11 35 100 152 336 34 64 128 256), losses := [] }

theorem u12386 : Upper (D 6) (R 6) [10,33,96,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12387 : Route 9 := (fun mask => (mask,id))

def c12387 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12387 : Upper (D 6) (R 6) [10,33,96,144,320,4] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,320,4] 13 (by decide) (choices 1) [1,2,4] r12387 c12387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2363
  · exact u2364
  · exact u2365

def b12388 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 200 21 34 340 404 276), lower := (rows 11 35 100 200 21 34 64 128 256), losses := [] }

theorem u12388 : Upper (D 6) (R 6) [10,33,96,192,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12389 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 35 100 200 21 36 338 402 274), lower := (rows 11 35 100 200 21 36 64 128 256), losses := [] }

theorem u12389 : Upper (D 6) (R 6) [10,33,96,192,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12390 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 100 200 21 48 326 390 262), lower := (rows 11 35 100 200 21 48 64 128 256), losses := [] }

theorem u12390 : Upper (D 6) (R 6) [10,33,96,192,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12390 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12391 : Route 9 := (fun mask => (mask,id))

def c12391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12391 : Upper (D 6) (R 6) [10,33,96,192,5,256] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,5,256] 13 (by decide) (choices 1) [2,4,16] r12391 c12391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2366
  · exact u2367
  · exact u2368

def b12392 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 200 22 33 340 404 276), lower := (rows 11 35 100 200 22 33 64 128 256), losses := [] }

theorem u12392 : Upper (D 6) (R 6) [10,33,96,192,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12393 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 100 200 22 36 337 401 273), lower := (rows 11 35 100 200 22 36 64 128 256), losses := [] }

theorem u12393 : Upper (D 6) (R 6) [10,33,96,192,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12394 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 100 200 22 48 325 389 261), lower := (rows 11 35 100 200 22 48 64 128 256), losses := [] }

theorem u12394 : Upper (D 6) (R 6) [10,33,96,192,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12394 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12395 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 201, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 100 200 22 288 85 149 277), lower := (rows 11 35 100 200 22 288 64 128 256), losses := [] }

theorem u12395 : Upper (D 6) (R 6) [10,33,96,192,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12395 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12396 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 200 273 34 84 148 276), lower := (rows 11 35 100 200 273 34 64 128 256), losses := [] }

theorem u12396 : Upper (D 6) (R 6) [10,33,96,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12397 : Route 9 := (fun mask => (mask,id))

def c12397 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12397 : Upper (D 6) (R 6) [10,33,96,192,257,4] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,257,4] 13 (by decide) (choices 1) [2,4,16] r12397 c12397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2369
  · exact u2370
  · exact u2371

def b12398 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 100 200 273 48 70 134 262), lower := (rows 11 35 100 200 273 48 64 128 256), losses := [] }

theorem u12398 : Upper (D 6) (R 6) [10,33,96,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12398 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12399 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 200 274 33 84 148 276), lower := (rows 11 35 100 200 274 33 64 128 256), losses := [] }

theorem u12399 : Upper (D 6) (R 6) [10,33,96,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12400 : Route 9 := (fun mask => (mask,id))

def c12400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12400 : Upper (D 6) (R 6) [10,33,96,192,258,4] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,258,4] 13 (by decide) (choices 1) [1,4,16] r12400 c12400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2372
  · exact u2373
  · exact u2374

def b12401 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 100 200 274 48 69 133 261), lower := (rows 11 35 100 200 274 48 64 128 256), losses := [] }

theorem u12401 : Upper (D 6) (R 6) [10,33,96,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12401 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12402 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 200 276 33 86 150 278), lower := (rows 11 35 100 200 276 33 64 128 256), losses := [] }

theorem u12402 : Upper (D 6) (R 6) [10,33,96,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12403 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 200 276 34 85 149 277), lower := (rows 11 35 100 200 276 34 64 128 256), losses := [] }

theorem u12403 : Upper (D 6) (R 6) [10,33,96,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12404 : Route 9 := (fun mask => (mask,id))

def c12404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12404 : Upper (D 6) (R 6) [10,33,96,192,260,4] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,260,4] 13 (by decide) (choices 1) [1,2,16] r12404 c12404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2375
  · exact u2376
  · exact u2377

def r12405 : Route 9 := (fun mask => (mask,id))

def c12405 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12405 : Upper (D 6) (R 6) [10,33,96,192,260,16] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,260,16] 13 (by decide) (choices 1) [1,2,4] r12405 c12405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2378
  · exact u2379
  · exact u2380

def b12406 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 392 21 34 84 212 340), lower := (rows 11 35 100 392 21 34 64 128 256), losses := [] }

theorem u12406 : Upper (D 6) (R 6) [10,33,96,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12407 : PairBound 9 := { available := 82, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 35 100 392 21 36 82 210 338), lower := (rows 11 35 100 392 21 36 64 128 256), losses := [] }

theorem u12407 : Upper (D 6) (R 6) [10,33,96,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12408 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 100 392 21 48 70 198 326), lower := (rows 11 35 100 392 21 48 64 128 256), losses := [] }

theorem u12408 : Upper (D 6) (R 6) [10,33,96,384,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12408 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12409 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 392 21 96 86 150 278), lower := (rows 11 35 100 392 21 96 64 128 256), losses := [] }

theorem u12409 : Upper (D 6) (R 6) [10,33,96,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12410 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 392 22 33 84 212 340), lower := (rows 11 35 100 392 22 33 64 128 256), losses := [] }

theorem u12410 : Upper (D 6) (R 6) [10,33,96,384,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12411 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 100 392 22 36 81 209 337), lower := (rows 11 35 100 392 22 36 64 128 256), losses := [] }

theorem u12411 : Upper (D 6) (R 6) [10,33,96,384,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12412 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 100 392 22 48 69 197 325), lower := (rows 11 35 100 392 22 48 64 128 256), losses := [] }

theorem u12412 : Upper (D 6) (R 6) [10,33,96,384,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12412 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12413 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 392 22 96 85 149 277), lower := (rows 11 35 100 392 22 96 64 128 256), losses := [] }

theorem u12413 : Upper (D 6) (R 6) [10,33,96,384,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12414 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 392 81 34 84 148 276), lower := (rows 11 35 100 392 81 34 64 128 256), losses := [] }

theorem u12414 : Upper (D 6) (R 6) [10,33,96,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12415 : Route 9 := (fun mask => (mask,id))

def c12415 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12415 : Upper (D 6) (R 6) [10,33,96,384,65,4] 13 := by
  apply FastRouting.sound _ _ [10,33,96,384,65,4] 13 (by decide) (choices 1) [2,4,16] r12415 c12415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2381
  · exact u2382
  · exact u2383

def b12416 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 392 81 48 70 134 262), lower := (rows 11 35 100 392 81 48 64 128 256), losses := [] }

theorem u12416 : Upper (D 6) (R 6) [10,33,96,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12416 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12417 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 392 82 33 84 148 276), lower := (rows 11 35 100 392 82 33 64 128 256), losses := [] }

theorem u12417 : Upper (D 6) (R 6) [10,33,96,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12418 : Route 9 := (fun mask => (mask,id))

def c12418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12418 : Upper (D 6) (R 6) [10,33,96,384,66,4] 13 := by
  apply FastRouting.sound _ _ [10,33,96,384,66,4] 13 (by decide) (choices 1) [1,4,16] r12418 c12418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2384
  · exact u2385
  · exact u2386

def b12419 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 392 82 48 69 133 261), lower := (rows 11 35 100 392 82 48 64 128 256), losses := [] }

theorem u12419 : Upper (D 6) (R 6) [10,33,96,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12419 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12419
end Delivery.IrregularNine14.P06
