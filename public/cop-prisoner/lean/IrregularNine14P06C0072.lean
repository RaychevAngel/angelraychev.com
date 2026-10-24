import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0005

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4320 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 104 336 36 65 133 261), lower := (rows 11 146 38 104 336 36 65 128 256), losses := [] }

theorem u4320 : Upper (D 6) (R 6) [10,144,34,96,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4321 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 403, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 146 38 104 336 36 68 129 257), lower := (rows 11 146 38 104 336 36 68 128 256), losses := [] }

theorem u4321 : Upper (D 6) (R 6) [10,144,34,96,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4322 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 146 38 268 21 96 65 224 352), lower := (rows 11 146 38 268 21 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 96 64 224 352), good := (rows 10 146 430 268 28 480 480 128 256) }] }

theorem u4322 : Upper (D 6) (R 6) [10,144,34,260,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4323 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 100, targets := 1 },{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,0),(3,1)], upper := (rows 11 146 38 268 21 96 96 193 321), lower := (rows 11 146 38 268 21 96 96 128 256), losses := [] }

theorem u4323 : Upper (D 6) (R 6) [10,144,34,260,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4324 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 2, region := 329, targets := 32 }], pairs := [(0,5),(4,1),(4,2)], upper := (rows 11 146 38 268 49 96 65 196 324), lower := (rows 11 146 38 268 49 96 65 128 256), losses := [] }

theorem u4324 : Upper (D 6) (R 6) [10,144,34,260,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4325 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 0, region := 100, targets := 1 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 146 38 268 49 96 68 193 321), lower := (rows 11 146 38 268 49 96 68 128 256), losses := [] }

theorem u4325 : Upper (D 6) (R 6) [10,144,34,260,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4326 : Route 9 := (fun mask => (mask,id))

def c4326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4326 : Upper (D 6) (R 6) [10,144,34,288,5,64,1] 13 := by
  apply FastRouting.sound _ _ [10,144,34,288,5,64,1] 13 (by decide) (choices 1) [4,64] r4326 c4326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u320
  · exact u321

def b4327 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 100, targets := 1 },{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,1)], upper := (rows 11 146 38 296 21 96 68 193 321), lower := (rows 11 146 38 296 21 96 68 128 256), losses := [] }

theorem u4327 : Upper (D 6) (R 6) [10,144,34,288,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4328 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 146 38 296 81 36 65 196 324), lower := (rows 11 146 38 296 81 36 65 128 256), losses := [] }

theorem u4328 : Upper (D 6) (R 6) [10,144,34,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4329 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 130, targets := 36 },{ cop := 0, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 11 146 38 296 81 36 68 193 321), lower := (rows 11 146 38 296 81 36 68 128 256), losses := [] }

theorem u4329 : Upper (D 6) (R 6) [10,144,34,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4330 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 130, targets := 33 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(1,5),(2,6)], upper := (rows 11 146 38 296 84 33 65 196 324), lower := (rows 11 146 38 296 84 33 65 128 256), losses := [] }

theorem u4330 : Upper (D 6) (R 6) [10,144,34,288,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4331 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 146 38 296 84 33 68 193 321), lower := (rows 11 146 38 296 84 33 68 128 256), losses := [] }

theorem u4331 : Upper (D 6) (R 6) [10,144,34,288,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4332 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 146 38 328 21 96 65 164 292), lower := (rows 11 146 38 328 21 96 65 128 256), losses := [{ target := 0, region := (rows 0 18 5 104 16 104 64 197 325), good := (rows 430 146 430 488 406 488 492 128 256) }] }

theorem u4332 : Upper (D 6) (R 6) [10,144,34,320,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4333 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 100, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(0,2),(2,0),(3,1)], upper := (rows 11 146 38 328 21 96 68 161 289), lower := (rows 11 146 38 328 21 96 68 128 256), losses := [{ target := 2, region := (rows 5 18 0 104 16 104 64 197 325), good := (rows 427 146 427 488 403 488 489 128 256) }] }

theorem u4333 : Upper (D 6) (R 6) [10,144,34,320,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4334 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 146 38 328 21 96 96 133 261), lower := (rows 11 146 38 328 21 96 96 128 256), losses := [] }

theorem u4334 : Upper (D 6) (R 6) [10,144,34,320,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4335 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(2,6),(3,0)], upper := (rows 11 146 38 328 84 33 65 164 292), lower := (rows 11 146 38 328 84 33 65 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 32 64 132 260), good := (rows 10 154 422 328 478 32 64 128 256) }] }

theorem u4335 : Upper (D 6) (R 6) [10,144,34,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4336 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 146 38 328 84 33 68 161 289), lower := (rows 11 146 38 328 84 33 68 128 256), losses := [] }

theorem u4336 : Upper (D 6) (R 6) [10,144,34,320,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4337 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 38 328 84 33 96 133 261), lower := (rows 11 146 38 328 84 33 96 128 256), losses := [] }

theorem u4337 : Upper (D 6) (R 6) [10,144,34,320,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4338 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 276 33 66 224 352), lower := (rows 11 146 100 13 276 33 66 128 256), losses := [] }

theorem u4338 : Upper (D 6) (R 6) [10,144,96,5,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4339 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 100 13 276 34 96 193 321), lower := (rows 11 146 100 13 276 34 96 128 256), losses := [] }

theorem u4339 : Upper (D 6) (R 6) [10,144,96,5,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4340 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 304 34 65 196 324), lower := (rows 11 146 100 13 304 34 65 128 256), losses := [] }

theorem u4340 : Upper (D 6) (R 6) [10,144,96,5,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4341 : Route 9 := (fun mask => (mask,id))

def c4341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4341 : Upper (D 6) (R 6) [10,144,96,5,288,2,4] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,288,2,4] 13 (by decide) (choices 1) [1,64] r4341 c4341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u322
  · exact u323

def b4342 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 304 36 65 194 322), lower := (rows 11 146 100 13 304 36 65 128 256), losses := [] }

theorem u4342 : Upper (D 6) (R 6) [10,144,96,5,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4343 : Route 9 := (fun mask => (mask,id))

def c4343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4343 : Upper (D 6) (R 6) [10,144,96,5,288,4,2] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,288,4,2] 13 (by decide) (choices 1) [1,64] r4343 c4343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u324
  · exact u325

def b4344 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 264, targets := 3 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 146 100 268 21 33 66 224 352), lower := (rows 11 146 100 268 21 33 66 128 256), losses := [] }

theorem u4344 : Upper (D 6) (R 6) [10,144,96,260,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4345 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 100 268 21 33 96 194 322), lower := (rows 11 146 100 268 21 33 96 128 256), losses := [] }

theorem u4345 : Upper (D 6) (R 6) [10,144,96,260,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4346 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 100 268 21 34 96 193 321), lower := (rows 11 146 100 268 21 34 96 128 256), losses := [] }

theorem u4346 : Upper (D 6) (R 6) [10,144,96,260,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4347 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 100 268 22 33 65 224 352), lower := (rows 11 146 100 268 22 33 65 128 256), losses := [] }

theorem u4347 : Upper (D 6) (R 6) [10,144,96,260,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4348 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 100 268 22 33 96 193 321), lower := (rows 11 146 100 268 22 33 96 128 256), losses := [] }

theorem u4348 : Upper (D 6) (R 6) [10,144,96,260,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4349 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 264, targets := 3 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(3,0),(3,1)], upper := (rows 11 146 100 296 21 33 66 196 324), lower := (rows 11 146 100 296 21 33 66 128 256), losses := [] }

theorem u4349 : Upper (D 6) (R 6) [10,144,96,288,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4350 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 146 100 296 21 33 68 194 322), lower := (rows 11 146 100 296 21 33 68 128 256), losses := [] }

theorem u4350 : Upper (D 6) (R 6) [10,144,96,288,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4351 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 264, targets := 3 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 146 100 296 21 34 65 196 324), lower := (rows 11 146 100 296 21 34 65 128 256), losses := [] }

theorem u4351 : Upper (D 6) (R 6) [10,144,96,288,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4352 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(2,1)], upper := (rows 11 146 100 296 21 34 68 193 321), lower := (rows 11 146 100 296 21 34 68 128 256), losses := [] }

theorem u4352 : Upper (D 6) (R 6) [10,144,96,288,5,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4353 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 100 296 22 33 65 196 324), lower := (rows 11 146 100 296 22 33 65 128 256), losses := [] }

theorem u4353 : Upper (D 6) (R 6) [10,144,96,288,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4354 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 296 22 33 68 193 321), lower := (rows 11 146 100 296 22 33 68 128 256), losses := [] }

theorem u4354 : Upper (D 6) (R 6) [10,144,96,288,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4355 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 264, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 146 100 296 81 33 66 132 260), lower := (rows 11 146 100 296 81 33 66 128 256), losses := [] }

theorem u4355 : Upper (D 6) (R 6) [10,144,96,288,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4356 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 11 146 100 296 81 33 68 134 262), lower := (rows 11 146 100 296 81 33 68 128 256), losses := [] }

theorem u4356 : Upper (D 6) (R 6) [10,144,96,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4357 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 264, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 146 100 296 81 34 65 132 260), lower := (rows 11 146 100 296 81 34 65 128 256), losses := [] }

theorem u4357 : Upper (D 6) (R 6) [10,144,96,288,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4358 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 11 146 100 296 81 34 68 133 261), lower := (rows 11 146 100 296 81 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 44 8 17 32 109 129 257), good := (rows 477 144 100 364 465 100 68 128 256) }] }

theorem u4358 : Upper (D 6) (R 6) [10,144,96,288,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4359 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 146 100 296 81 36 65 134 262), lower := (rows 11 146 100 296 81 36 65 128 256), losses := [] }

theorem u4359 : Upper (D 6) (R 6) [10,144,96,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4360 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 146 100 296 81 36 66 133 261), lower := (rows 11 146 100 296 81 36 66 128 256), losses := [] }

theorem u4360 : Upper (D 6) (R 6) [10,144,96,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4361 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 146 100 296 81 36 68 131 259), lower := (rows 11 146 100 296 81 36 68 128 256), losses := [] }

theorem u4361 : Upper (D 6) (R 6) [10,144,96,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4362 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 100 296 82 33 65 132 260), lower := (rows 11 146 100 296 82 33 65 128 256), losses := [] }

theorem u4362 : Upper (D 6) (R 6) [10,144,96,288,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4363 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 296 82 33 68 133 261), lower := (rows 11 146 100 296 82 33 68 128 256), losses := [] }

theorem u4363 : Upper (D 6) (R 6) [10,144,96,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4364 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 454, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,5),(2,5),(4,2)], upper := (rows 11 146 261 44 49 96 66 196 324), lower := (rows 11 146 261 44 49 96 66 128 256), losses := [] }

theorem u4364 : Upper (D 6) (R 6) [10,144,257,36,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4365 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 146 261 44 49 96 68 194 322), lower := (rows 11 146 261 44 49 96 68 128 256), losses := [] }

theorem u4365 : Upper (D 6) (R 6) [10,144,257,36,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4366 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 146 261 44 81 96 66 164 292), lower := (rows 11 146 261 44 81 96 66 128 256), losses := [] }

theorem u4366 : Upper (D 6) (R 6) [10,144,257,36,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4367 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 146 261 44 81 96 68 162 290), lower := (rows 11 146 261 44 81 96 68 128 256), losses := [] }

theorem u4367 : Upper (D 6) (R 6) [10,144,257,36,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4368 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 11 146 261 44 81 96 96 134 262), lower := (rows 11 146 261 44 81 96 96 128 256), losses := [] }

theorem u4368 : Upper (D 6) (R 6) [10,144,257,36,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4369 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 146 261 44 82 96 65 164 292), lower := (rows 11 146 261 44 82 96 65 128 256), losses := [] }

theorem u4369 : Upper (D 6) (R 6) [10,144,257,36,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4370 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 146 261 44 82 96 68 161 289), lower := (rows 11 146 261 44 82 96 68 128 256), losses := [] }

theorem u4370 : Upper (D 6) (R 6) [10,144,257,36,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4371 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 114, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 146 261 44 82 96 96 133 261), lower := (rows 11 146 261 44 82 96 96 128 256), losses := [] }

theorem u4371 : Upper (D 6) (R 6) [10,144,257,36,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4372 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 146 261 44 84 96 65 162 290), lower := (rows 11 146 261 44 84 96 65 128 256), losses := [] }

theorem u4372 : Upper (D 6) (R 6) [10,144,257,36,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4373 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 146 261 44 84 96 66 161 289), lower := (rows 11 146 261 44 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 119 67 128 256), good := (rows 106 250 380 60 124 96 98 128 256) }] }

theorem u4373 : Upper (D 6) (R 6) [10,144,257,36,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4374 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 146 261 44 84 96 96 131 259), lower := (rows 11 146 261 44 84 96 96 128 256), losses := [] }

theorem u4374 : Upper (D 6) (R 6) [10,144,257,36,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4375 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1),(3,2)], upper := (rows 11 146 261 104 22 33 68 224 352), lower := (rows 11 146 261 104 22 33 68 128 256), losses := [{ target := 2, region := (rows 1 2 0 72 16 37 64 200 328), good := (rows 427 146 289 488 50 33 488 128 256) }] }

theorem u4375 : Upper (D 6) (R 6) [10,144,257,96,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4376 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 146 261 104 22 33 96 196 324), lower := (rows 11 146 261 104 22 33 96 128 256), losses := [] }

theorem u4376 : Upper (D 6) (R 6) [10,144,257,96,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4377 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 146 261 104 22 36 96 193 321), lower := (rows 11 146 261 104 22 36 96 128 256), losses := [] }

theorem u4377 : Upper (D 6) (R 6) [10,144,257,96,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4378 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 262 41 52 96 65 196 324), lower := (rows 11 146 262 41 52 96 65 128 256), losses := [] }

theorem u4378 : Upper (D 6) (R 6) [10,144,258,33,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4379 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 146 262 41 52 96 68 193 321), lower := (rows 11 146 262 41 52 96 68 128 256), losses := [] }

theorem u4379 : Upper (D 6) (R 6) [10,144,258,33,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4379
end Delivery.IrregularNine14.P06
