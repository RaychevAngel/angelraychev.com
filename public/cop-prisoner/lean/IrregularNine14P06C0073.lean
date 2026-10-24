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

def b4380 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 262 41 84 36 65 224 352), lower := (rows 11 146 262 41 84 36 65 128 256), losses := [] }

theorem u4380 : Upper (D 6) (R 6) [10,144,258,33,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4381 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 11 146 262 41 84 36 96 193 321), lower := (rows 11 146 262 41 84 36 96 128 256), losses := [] }

theorem u4381 : Upper (D 6) (R 6) [10,144,258,33,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4382 : Route 9 := (fun mask => (mask,id))

def c4382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4382 : Upper (D 6) (R 6) [10,144,258,36,5,64,1] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,5,64,1] 13 (by decide) (choices 1) [32,64] r4382 c4382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u326
  · exact u327

def b4383 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 146 262 44 21 96 96 193 321), lower := (rows 11 146 262 44 21 96 96 128 256), losses := [] }

theorem u4383 : Upper (D 6) (R 6) [10,144,258,36,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4384 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(4,1),(4,2)], upper := (rows 11 146 262 44 49 96 65 196 324), lower := (rows 11 146 262 44 49 96 65 128 256), losses := [] }

theorem u4384 : Upper (D 6) (R 6) [10,144,258,36,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4385 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 146 262 44 49 96 68 193 321), lower := (rows 11 146 262 44 49 96 68 128 256), losses := [] }

theorem u4385 : Upper (D 6) (R 6) [10,144,258,36,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4386 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 146 262 44 81 96 65 164 292), lower := (rows 11 146 262 44 81 96 65 128 256), losses := [] }

theorem u4386 : Upper (D 6) (R 6) [10,144,258,36,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4387 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 146 262 44 81 96 68 161 289), lower := (rows 11 146 262 44 81 96 68 128 256), losses := [] }

theorem u4387 : Upper (D 6) (R 6) [10,144,258,36,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4388 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 11 146 262 44 81 96 96 133 261), lower := (rows 11 146 262 44 81 96 96 128 256), losses := [] }

theorem u4388 : Upper (D 6) (R 6) [10,144,258,36,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4389 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 146 262 44 84 96 65 161 289), lower := (rows 11 146 262 44 84 96 65 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 113 65 193 321), good := (rows 491 178 258 40 498 480 481 128 256) }] }

theorem u4389 : Upper (D 6) (R 6) [10,144,258,36,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4390 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 146 262 44 84 96 96 129 257), lower := (rows 11 146 262 44 84 96 96 128 256), losses := [] }

theorem u4390 : Upper (D 6) (R 6) [10,144,258,36,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4391 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 104, targets := 2 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 146 262 104 21 33 68 224 352), lower := (rows 11 146 262 104 21 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 5 40 16 32 117 168 296), good := (rows 462 210 326 488 84 492 68 128 256) }] }

theorem u4391 : Upper (D 6) (R 6) [10,144,258,96,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4392 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 146 262 104 21 33 96 196 324), lower := (rows 11 146 262 104 21 33 96 128 256), losses := [] }

theorem u4392 : Upper (D 6) (R 6) [10,144,258,96,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4393 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 146 262 104 21 36 96 193 321), lower := (rows 11 146 262 104 21 36 96 128 256), losses := [] }

theorem u4393 : Upper (D 6) (R 6) [10,144,258,96,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4394 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 72, targets := 6 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(3,2)], upper := (rows 11 146 262 104 49 36 65 196 324), lower := (rows 11 146 262 104 49 36 65 128 256), losses := [] }

theorem u4394 : Upper (D 6) (R 6) [10,144,258,96,33,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4395 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 146 262 104 49 36 68 193 321), lower := (rows 11 146 262 104 49 36 68 128 256), losses := [] }

theorem u4395 : Upper (D 6) (R 6) [10,144,258,96,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4396 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 262 104 52 33 65 196 324), lower := (rows 11 146 262 104 52 33 65 128 256), losses := [] }

theorem u4396 : Upper (D 6) (R 6) [10,144,258,96,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4397 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 3 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 146 262 104 52 33 68 193 321), lower := (rows 11 146 262 104 52 33 68 128 256), losses := [] }

theorem u4397 : Upper (D 6) (R 6) [10,144,258,96,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4398 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 454, targets := 1 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 146 292 13 49 96 66 196 324), lower := (rows 11 146 292 13 49 96 66 128 256), losses := [] }

theorem u4398 : Upper (D 6) (R 6) [10,144,288,5,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4399 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 454, targets := 1 },{ cop := 3, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 146 292 13 49 96 68 194 322), lower := (rows 11 146 292 13 49 96 68 128 256), losses := [] }

theorem u4399 : Upper (D 6) (R 6) [10,144,288,5,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4400 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 50 96 65 196 324), lower := (rows 11 146 292 13 50 96 65 128 256), losses := [] }

theorem u4400 : Upper (D 6) (R 6) [10,144,288,5,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4401 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 292 13 50 96 68 193 321), lower := (rows 11 146 292 13 50 96 68 128 256), losses := [] }

theorem u4401 : Upper (D 6) (R 6) [10,144,288,5,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4402 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 13 81 96 66 164 292), lower := (rows 11 146 292 13 81 96 66 128 256), losses := [] }

theorem u4402 : Upper (D 6) (R 6) [10,144,288,5,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4403 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 3, region := 80, targets := 2 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 146 292 13 81 96 68 162 290), lower := (rows 11 146 292 13 81 96 68 128 256), losses := [] }

theorem u4403 : Upper (D 6) (R 6) [10,144,288,5,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4404 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 146 292 13 81 96 96 134 262), lower := (rows 11 146 292 13 81 96 96 128 256), losses := [] }

theorem u4404 : Upper (D 6) (R 6) [10,144,288,5,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4405 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 82 96 65 164 292), lower := (rows 11 146 292 13 82 96 65 128 256), losses := [] }

theorem u4405 : Upper (D 6) (R 6) [10,144,288,5,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4406 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 292 13 82 96 68 161 289), lower := (rows 11 146 292 13 82 96 68 128 256), losses := [] }

theorem u4406 : Upper (D 6) (R 6) [10,144,288,5,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4407 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 114, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 146 292 13 82 96 96 133 261), lower := (rows 11 146 292 13 82 96 96 128 256), losses := [] }

theorem u4407 : Upper (D 6) (R 6) [10,144,288,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4408 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 84 34 65 224 352), lower := (rows 11 146 292 13 84 34 65 128 256), losses := [] }

theorem u4408 : Upper (D 6) (R 6) [10,144,288,5,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4409 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 292 13 84 34 96 193 321), lower := (rows 11 146 292 13 84 34 96 128 256), losses := [] }

theorem u4409 : Upper (D 6) (R 6) [10,144,288,5,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4410 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 84 96 65 162 290), lower := (rows 11 146 292 13 84 96 65 128 256), losses := [] }

theorem u4410 : Upper (D 6) (R 6) [10,144,288,5,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4411 : Route 9 := (fun mask => (mask,id))

def c4411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4411 : Upper (D 6) (R 6) [10,144,288,5,68,64,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,68,64,2] 13 (by decide) (choices 1) [1,32] r4411 c4411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u328
  · exact u329

def b4412 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 146 292 13 84 96 96 131 259), lower := (rows 11 146 292 13 84 96 96 128 256), losses := [] }

theorem u4412 : Upper (D 6) (R 6) [10,144,288,5,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4413 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 112 34 65 196 324), lower := (rows 11 146 292 13 112 34 65 128 256), losses := [] }

theorem u4413 : Upper (D 6) (R 6) [10,144,288,5,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4414 : Route 9 := (fun mask => (mask,id))

def c4414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4414 : Upper (D 6) (R 6) [10,144,288,5,96,2,4] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,96,2,4] 13 (by decide) (choices 1) [1,64] r4414 c4414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u330
  · exact u331

def b4415 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 41 22 96 65 196 324), lower := (rows 11 146 292 41 22 96 65 128 256), losses := [] }

theorem u4415 : Upper (D 6) (R 6) [10,144,288,33,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4416 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 292 41 22 96 68 193 321), lower := (rows 11 146 292 41 22 96 68 128 256), losses := [] }

theorem u4416 : Upper (D 6) (R 6) [10,144,288,33,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4417 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 73 21 96 66 164 292), lower := (rows 11 146 292 73 21 96 66 128 256), losses := [] }

theorem u4417 : Upper (D 6) (R 6) [10,144,288,65,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4418 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 146 292 73 21 96 68 162 290), lower := (rows 11 146 292 73 21 96 68 128 256), losses := [] }

theorem u4418 : Upper (D 6) (R 6) [10,144,288,65,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4419 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 146 292 73 21 96 96 134 262), lower := (rows 11 146 292 73 21 96 96 128 256), losses := [] }

theorem u4419 : Upper (D 6) (R 6) [10,144,288,65,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4420 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 146 292 73 22 96 65 164 292), lower := (rows 11 146 292 73 22 96 65 128 256), losses := [] }

theorem u4420 : Upper (D 6) (R 6) [10,144,288,65,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4421 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(2,1),(3,1)], upper := (rows 11 146 292 73 22 96 68 161 289), lower := (rows 11 146 292 73 22 96 68 128 256), losses := [] }

theorem u4421 : Upper (D 6) (R 6) [10,144,288,65,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4422 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 146 292 73 22 96 96 133 261), lower := (rows 11 146 292 73 22 96 96 128 256), losses := [] }

theorem u4422 : Upper (D 6) (R 6) [10,144,288,65,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4423 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 146 292 73 84 34 65 164 292), lower := (rows 11 146 292 73 84 34 65 128 256), losses := [] }

theorem u4423 : Upper (D 6) (R 6) [10,144,288,65,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4424 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 146 292 73 84 34 68 161 289), lower := (rows 11 146 292 73 84 34 68 128 256), losses := [] }

theorem u4424 : Upper (D 6) (R 6) [10,144,288,65,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4425 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 292 73 84 34 96 133 261), lower := (rows 11 146 292 73 84 34 96 128 256), losses := [] }

theorem u4425 : Upper (D 6) (R 6) [10,144,288,65,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4426 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 146 292 76 21 33 66 224 352), lower := (rows 11 146 292 76 21 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 56 16 32 67 160 288), good := (rows 74 218 428 76 92 492 66 128 256) }] }

theorem u4426 : Upper (D 6) (R 6) [10,144,288,68,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4427 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 146 292 76 21 33 96 194 322), lower := (rows 11 146 292 76 21 33 96 128 256), losses := [] }

theorem u4427 : Upper (D 6) (R 6) [10,144,288,68,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4428 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 72, targets := 34 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,1),(3,5)], upper := (rows 11 146 292 76 21 34 65 224 352), lower := (rows 11 146 292 76 21 34 65 128 256), losses := [] }

theorem u4428 : Upper (D 6) (R 6) [10,144,288,68,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4429 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 146 292 76 21 34 96 193 321), lower := (rows 11 146 292 76 21 34 96 128 256), losses := [] }

theorem u4429 : Upper (D 6) (R 6) [10,144,288,68,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4430 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 2 },{ cop := 4, region := 226, targets := 4 },{ cop := 4, region := 72, targets := 32 }], pairs := [(1,2),(3,1),(3,5)], upper := (rows 11 146 292 76 21 96 65 162 290), lower := (rows 11 146 292 76 21 96 65 128 256), losses := [] }

theorem u4430 : Upper (D 6) (R 6) [10,144,288,68,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4431 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,1),(3,0)], upper := (rows 11 146 292 76 21 96 66 161 289), lower := (rows 11 146 292 76 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 123 67 128 256), good := (rows 106 250 292 108 124 96 98 128 256) },{ target := 1, region := (rows 1 0 5 8 17 104 64 129 257), good := (rows 445 144 292 108 405 96 96 128 256) }] }

theorem u4431 : Upper (D 6) (R 6) [10,144,288,68,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4432 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 147, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 146 292 76 21 96 96 131 259), lower := (rows 11 146 292 76 21 96 96 128 256), losses := [] }

theorem u4432 : Upper (D 6) (R 6) [10,144,288,68,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4433 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(2,1),(3,1)], upper := (rows 11 146 292 76 22 33 65 224 352), lower := (rows 11 146 292 76 22 33 65 128 256), losses := [] }

theorem u4433 : Upper (D 6) (R 6) [10,144,288,68,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4434 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 146 292 76 22 33 96 193 321), lower := (rows 11 146 292 76 22 33 96 128 256), losses := [] }

theorem u4434 : Upper (D 6) (R 6) [10,144,288,68,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4435 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(2,1),(3,1)], upper := (rows 11 146 292 76 22 96 65 161 289), lower := (rows 11 146 292 76 22 96 65 128 256), losses := [] }

theorem u4435 : Upper (D 6) (R 6) [10,144,288,68,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4436 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 147, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 146 292 76 22 96 96 129 257), lower := (rows 11 146 292 76 22 96 96 128 256), losses := [] }

theorem u4436 : Upper (D 6) (R 6) [10,144,288,68,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4437 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 76 81 33 66 164 292), lower := (rows 11 146 292 76 81 33 66 128 256), losses := [] }

theorem u4437 : Upper (D 6) (R 6) [10,144,288,68,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4438 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 146 292 76 81 33 68 162 290), lower := (rows 11 146 292 76 81 33 68 128 256), losses := [] }

theorem u4438 : Upper (D 6) (R 6) [10,144,288,68,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4439 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 146 292 76 81 33 96 134 262), lower := (rows 11 146 292 76 81 33 96 128 256), losses := [] }

theorem u4439 : Upper (D 6) (R 6) [10,144,288,68,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4439
end Delivery.IrregularNine14.P06
