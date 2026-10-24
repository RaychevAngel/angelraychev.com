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

def b12300 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 100 28 145 288 70 198 326), lower := (rows 11 35 100 28 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 307 67 131 259), good := (rows 494 486 100 60 508 288 64 128 288) }] }

theorem u12300 : Upper (D 6) (R 6) [10,33,96,20,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12300 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12301 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 28 146 33 324 452 324), lower := (rows 11 35 100 28 146 33 64 128 256), losses := [] }

theorem u12301 : Upper (D 6) (R 6) [10,33,96,20,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12302 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 100 28 146 36 321 449 321), lower := (rows 11 35 100 28 146 36 64 128 256), losses := [] }

theorem u12302 : Upper (D 6) (R 6) [10,33,96,20,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12303 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 28 146 96 325 389 261), lower := (rows 11 35 100 28 146 96 64 128 256), losses := [] }

theorem u12303 : Upper (D 6) (R 6) [10,33,96,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12304 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 100 28 146 288 69 197 325), lower := (rows 11 35 100 28 146 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 307 67 131 259), good := (rows 493 485 100 60 508 288 64 128 288) }] }

theorem u12304 : Upper (D 6) (R 6) [10,33,96,20,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12304 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12305 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 100 28 208 33 326 390 262), lower := (rows 11 35 100 28 208 33 64 128 256), losses := [] }

theorem u12305 : Upper (D 6) (R 6) [10,33,96,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12306 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 100 28 208 34 325 389 261), lower := (rows 11 35 100 28 208 34 64 128 256), losses := [] }

theorem u12306 : Upper (D 6) (R 6) [10,33,96,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12307 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 28 208 36 323 387 259), lower := (rows 11 35 100 28 208 36 64 128 256), losses := [] }

theorem u12307 : Upper (D 6) (R 6) [10,33,96,20,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12308 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 28 208 288 71 135 263), lower := (rows 11 35 100 28 208 288 64 128 256), losses := [] }

theorem u12308 : Upper (D 6) (R 6) [10,33,96,20,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12308 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12309 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 28 400 33 70 198 326), lower := (rows 11 35 100 28 400 33 64 128 256), losses := [] }

theorem u12309 : Upper (D 6) (R 6) [10,33,96,20,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12310 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 28 400 34 69 197 325), lower := (rows 11 35 100 28 400 34 64 128 256), losses := [] }

theorem u12310 : Upper (D 6) (R 6) [10,33,96,20,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12311 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 100 28 400 36 67 195 323), lower := (rows 11 35 100 28 400 36 64 128 256), losses := [] }

theorem u12311 : Upper (D 6) (R 6) [10,33,96,20,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12312 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 28 400 96 71 135 263), lower := (rows 11 35 100 28 400 96 64 128 256), losses := [] }

theorem u12312 : Upper (D 6) (R 6) [10,33,96,20,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12313 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 88 145 34 324 388 260), lower := (rows 11 35 100 88 145 34 64 128 256), losses := [] }

theorem u12313 : Upper (D 6) (R 6) [10,33,96,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12314 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 88 145 36 326 390 262), lower := (rows 11 35 100 88 145 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 95 24 16 127 67 131 259), good := (rows 494 486 100 124 508 36 100 128 256) }] }

theorem u12314 : Upper (D 6) (R 6) [10,33,96,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12315 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 100 88 145 288 70 134 262), lower := (rows 11 35 100 88 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 31 24 16 307 67 131 259), good := (rows 494 486 100 124 508 288 64 128 288) }] }

theorem u12315 : Upper (D 6) (R 6) [10,33,96,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12315 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12316 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 88 146 33 324 388 260), lower := (rows 11 35 100 88 146 33 64 128 256), losses := [] }

theorem u12316 : Upper (D 6) (R 6) [10,33,96,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12317 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 35 100 88 146 36 325 389 261), lower := (rows 11 35 100 88 146 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 95 24 16 127 67 131 259), good := (rows 493 485 100 124 508 36 100 128 256) }] }

theorem u12317 : Upper (D 6) (R 6) [10,33,96,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12318 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 100 88 146 288 69 133 261), lower := (rows 11 35 100 88 146 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 31 24 16 307 67 131 259), good := (rows 493 485 100 124 508 288 64 128 288) }] }

theorem u12318 : Upper (D 6) (R 6) [10,33,96,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12318 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12319 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 88 148 33 326 390 262), lower := (rows 11 35 100 88 148 33 64 128 256), losses := [] }

theorem u12319 : Upper (D 6) (R 6) [10,33,96,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12320 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 88 148 34 325 389 261), lower := (rows 11 35 100 88 148 34 64 128 256), losses := [] }

theorem u12320 : Upper (D 6) (R 6) [10,33,96,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12321 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 11 35 100 88 148 36 323 387 259), lower := (rows 11 35 100 88 148 36 64 128 256), losses := [{ target := 6, region := (rows 9 10 4 8 16 52 0 139 267), good := (rows 395 419 36 443 180 36 0 128 256) }] }

theorem u12321 : Upper (D 6) (R 6) [10,33,96,80,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12322 : Route 9 := (fun mask => (mask,id))

def c12322 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12322 : Upper (D 6) (R 6) [10,33,96,80,132,256] 13 := by
  apply FastRouting.sound _ _ [10,33,96,80,132,256] 13 (by decide) (choices 1) [1,2,4] r12322 c12322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2347
  · exact u2348
  · exact u2349

def b12323 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 88 400 33 70 134 262), lower := (rows 11 35 100 88 400 33 64 128 256), losses := [] }

theorem u12323 : Upper (D 6) (R 6) [10,33,96,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12324 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 88 400 34 69 133 261), lower := (rows 11 35 100 88 400 34 64 128 256), losses := [] }

theorem u12324 : Upper (D 6) (R 6) [10,33,96,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12325 : Route 9 := (fun mask => (mask,id))

def c12325 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12325 : Upper (D 6) (R 6) [10,33,96,80,384,4] 13 := by
  apply FastRouting.sound _ _ [10,33,96,80,384,4] 13 (by decide) (choices 1) [1,2,4] r12325 c12325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2350
  · exact u2351
  · exact u2352

def b12326 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 137 276 34 84 212 340), lower := (rows 11 35 100 137 276 34 64 128 256), losses := [] }

theorem u12326 : Upper (D 6) (R 6) [10,33,96,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12327 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 100 137 276 36 82 210 338), lower := (rows 11 35 100 137 276 36 64 128 256), losses := [] }

theorem u12327 : Upper (D 6) (R 6) [10,33,96,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12328 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 100 137 276 48 70 198 326), lower := (rows 11 35 100 137 276 48 64 128 256), losses := [] }

theorem u12328 : Upper (D 6) (R 6) [10,33,96,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12328 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12329 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 137 276 96 86 150 278), lower := (rows 11 35 100 137 276 96 64 128 256), losses := [] }

theorem u12329 : Upper (D 6) (R 6) [10,33,96,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12330 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 137 336 34 84 148 276), lower := (rows 11 35 100 137 336 34 64 128 256), losses := [] }

theorem u12330 : Upper (D 6) (R 6) [10,33,96,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12331 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 100 137 336 36 86 150 278), lower := (rows 11 35 100 137 336 36 64 128 256), losses := [] }

theorem u12331 : Upper (D 6) (R 6) [10,33,96,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12332 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 137 336 48 70 134 262), lower := (rows 11 35 100 137 336 48 64 128 256), losses := [] }

theorem u12332 : Upper (D 6) (R 6) [10,33,96,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12332 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12333 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 100 140 21 34 336 464 336), lower := (rows 11 35 100 140 21 34 64 128 256), losses := [] }

theorem u12333 : Upper (D 6) (R 6) [10,33,96,132,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12334 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 140 21 48 322 450 322), lower := (rows 11 35 100 140 21 48 64 128 256), losses := [] }

theorem u12334 : Upper (D 6) (R 6) [10,33,96,132,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12334 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12335 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 140 21 96 338 402 274), lower := (rows 11 35 100 140 21 96 64 128 256), losses := [] }

theorem u12335 : Upper (D 6) (R 6) [10,33,96,132,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12336 : Route 9 := (fun mask => (mask,id))

def c12336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12336 : Upper (D 6) (R 6) [10,33,96,132,5,256] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,5,256] 13 (by decide) (choices 1) [2,16] r12336 c12336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2353
  · exact u2354

def b12337 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 100 140 22 33 336 464 336), lower := (rows 11 35 100 140 22 33 64 128 256), losses := [] }

theorem u12337 : Upper (D 6) (R 6) [10,33,96,132,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12338 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 140 22 48 321 449 321), lower := (rows 11 35 100 140 22 48 64 128 256), losses := [] }

theorem u12338 : Upper (D 6) (R 6) [10,33,96,132,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12338 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12339 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 140 22 96 337 401 273), lower := (rows 11 35 100 140 22 96 64 128 256), losses := [] }

theorem u12339 : Upper (D 6) (R 6) [10,33,96,132,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12340 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 201, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 100 140 22 288 81 209 337), lower := (rows 11 35 100 140 22 288 64 128 256), losses := [] }

theorem u12340 : Upper (D 6) (R 6) [10,33,96,132,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12340 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12341 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 140 81 34 340 404 276), lower := (rows 11 35 100 140 81 34 64 128 256), losses := [] }

theorem u12341 : Upper (D 6) (R 6) [10,33,96,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12342 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 100 140 81 36 338 402 274), lower := (rows 11 35 100 140 81 36 64 128 256), losses := [] }

theorem u12342 : Upper (D 6) (R 6) [10,33,96,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12343 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 140 81 48 326 390 262), lower := (rows 11 35 100 140 81 48 64 128 256), losses := [] }

theorem u12343 : Upper (D 6) (R 6) [10,33,96,132,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12343 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12344 : Route 9 := (fun mask => (mask,id))

def c12344 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12344 : Upper (D 6) (R 6) [10,33,96,132,65,256] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,65,256] 13 (by decide) (choices 1) [2,4,16] r12344 c12344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2355
  · exact u2356
  · exact u2357

def b12345 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 140 82 33 340 404 276), lower := (rows 11 35 100 140 82 33 64 128 256), losses := [] }

theorem u12345 : Upper (D 6) (R 6) [10,33,96,132,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12346 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 100 140 82 36 337 401 273), lower := (rows 11 35 100 140 82 36 64 128 256), losses := [] }

theorem u12346 : Upper (D 6) (R 6) [10,33,96,132,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12347 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 140 82 48 325 389 261), lower := (rows 11 35 100 140 82 48 64 128 256), losses := [] }

theorem u12347 : Upper (D 6) (R 6) [10,33,96,132,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12347 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12348 : Route 9 := (fun mask => (mask,id))

def c12348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12348 : Upper (D 6) (R 6) [10,33,96,132,66,256] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,66,256] 13 (by decide) (choices 1) [1,4,16] r12348 c12348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2358
  · exact u2359
  · exact u2360

def b12349 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 140 273 34 84 212 340), lower := (rows 11 35 100 140 273 34 64 128 256), losses := [] }

theorem u12349 : Upper (D 6) (R 6) [10,33,96,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12350 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 100 140 273 36 82 210 338), lower := (rows 11 35 100 140 273 36 64 128 256), losses := [] }

theorem u12350 : Upper (D 6) (R 6) [10,33,96,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12351 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 100 140 273 48 70 198 326), lower := (rows 11 35 100 140 273 48 64 128 256), losses := [] }

theorem u12351 : Upper (D 6) (R 6) [10,33,96,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12351 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12352 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 140 273 96 86 150 278), lower := (rows 11 35 100 140 273 96 64 128 256), losses := [] }

theorem u12352 : Upper (D 6) (R 6) [10,33,96,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12353 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 140 274 33 84 212 340), lower := (rows 11 35 100 140 274 33 64 128 256), losses := [] }

theorem u12353 : Upper (D 6) (R 6) [10,33,96,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12354 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 100 140 274 36 81 209 337), lower := (rows 11 35 100 140 274 36 64 128 256), losses := [] }

theorem u12354 : Upper (D 6) (R 6) [10,33,96,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12355 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 100 140 274 48 69 197 325), lower := (rows 11 35 100 140 274 48 64 128 256), losses := [] }

theorem u12355 : Upper (D 6) (R 6) [10,33,96,132,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12355 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12356 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 140 274 96 85 149 277), lower := (rows 11 35 100 140 274 96 64 128 256), losses := [] }

theorem u12356 : Upper (D 6) (R 6) [10,33,96,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12357 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 140 276 33 82 210 338), lower := (rows 11 35 100 140 276 33 64 128 256), losses := [] }

theorem u12357 : Upper (D 6) (R 6) [10,33,96,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12358 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 140 276 34 81 209 337), lower := (rows 11 35 100 140 276 34 64 128 256), losses := [] }

theorem u12358 : Upper (D 6) (R 6) [10,33,96,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12359 : Route 9 := (fun mask => (mask,id))

def c12359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12359 : Upper (D 6) (R 6) [10,33,96,132,260,16] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,260,16] 13 (by decide) (choices 1) [1,2] r12359 c12359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2361
  · exact u2362

#print axioms u12359
end Delivery.IrregularNine14.P06
