import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4380 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 7 104 145 160 80 194 322), lower := (rows 13 290 7 104 145 160 80 128 256), losses := [] }

theorem u4380 : Upper (D 7) (R 7) [12,288,3,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4380 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4381 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 7 104 146 48 65 192 448), lower := (rows 13 290 7 104 146 48 65 128 256), losses := [] }

theorem u4381 : Upper (D 7) (R 7) [12,288,3,96,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4381 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4382 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 7 104 146 48 192 193 321), lower := (rows 13 290 7 104 146 48 192 128 256), losses := [] }

theorem u4382 : Upper (D 7) (R 7) [12,288,3,96,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4382 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4383 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 7 104 146 160 65 208 336), lower := (rows 13 290 7 104 146 160 65 128 256), losses := [] }

theorem u4383 : Upper (D 7) (R 7) [12,288,3,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4384 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 7 104 146 160 80 193 321), lower := (rows 13 290 7 104 146 160 80 128 256), losses := [] }

theorem u4384 : Upper (D 7) (R 7) [12,288,3,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4384 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4385 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 7 104 208 160 65 146 274), lower := (rows 13 290 7 104 208 160 65 128 256), losses := [] }

theorem u4385 : Upper (D 7) (R 7) [12,288,3,96,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4386 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 13 290 7 104 208 160 66 145 273), lower := (rows 13 290 7 104 208 160 66 128 256), losses := [] }

theorem u4386 : Upper (D 7) (R 7) [12,288,3,96,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4387 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 13 290 7 104 208 160 80 131 259), lower := (rows 13 290 7 104 208 160 80 128 256), losses := [] }

theorem u4387 : Upper (D 7) (R 7) [12,288,3,96,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4387 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4388 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 13 290 7 200 82 33 80 160 416), lower := (rows 13 290 7 200 82 33 80 128 256), losses := [] }

theorem u4388 : Upper (D 7) (R 7) [12,288,3,192,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4388 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4389 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 290 7 200 82 33 96 144 400), lower := (rows 13 290 7 200 82 33 96 128 256), losses := [] }

theorem u4389 : Upper (D 7) (R 7) [12,288,3,192,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4390 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 7 200 82 33 192 176 304), lower := (rows 13 290 7 200 82 33 192 128 256), losses := [] }

theorem u4390 : Upper (D 7) (R 7) [12,288,3,192,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4391 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 290 7 200 82 48 65 160 416), lower := (rows 13 290 7 200 82 48 65 128 256), losses := [] }

theorem u4391 : Upper (D 7) (R 7) [12,288,3,192,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4391 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4392 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 290 7 200 82 48 96 129 385), lower := (rows 13 290 7 200 82 48 96 128 256), losses := [] }

theorem u4392 : Upper (D 7) (R 7) [12,288,3,192,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4392 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4393 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 7 200 82 48 192 161 289), lower := (rows 13 290 7 200 82 48 192 128 256), losses := [] }

theorem u4393 : Upper (D 7) (R 7) [12,288,3,192,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4393 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4394 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 80, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 290 7 200 82 160 65 176 304), lower := (rows 13 290 7 200 82 160 65 128 256), losses := [] }

theorem u4394 : Upper (D 7) (R 7) [12,288,3,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4395 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 13 290 7 200 82 160 80 161 289), lower := (rows 13 290 7 200 82 160 80 128 256), losses := [] }

theorem u4395 : Upper (D 7) (R 7) [12,288,3,192,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4395 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4396 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 13 290 7 200 82 160 96 145 273), lower := (rows 13 290 7 200 82 160 96 128 256), losses := [] }

theorem u4396 : Upper (D 7) (R 7) [12,288,3,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4397 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 136, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 290 7 200 112 34 65 144 400), lower := (rows 13 290 7 200 112 34 65 128 256), losses := [] }

theorem u4397 : Upper (D 7) (R 7) [12,288,3,192,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4398 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 290 7 200 112 34 80 129 385), lower := (rows 13 290 7 200 112 34 80 128 256), losses := [] }

theorem u4398 : Upper (D 7) (R 7) [12,288,3,192,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4398 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4399 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 7 200 112 34 192 145 273), lower := (rows 13 290 7 200 112 34 192 128 256), losses := [] }

theorem u4399 : Upper (D 7) (R 7) [12,288,3,192,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4400 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 290 7 200 112 160 65 146 274), lower := (rows 13 290 7 200 112 160 65 128 256), losses := [] }

theorem u4400 : Upper (D 7) (R 7) [12,288,3,192,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4401 : Route 9 := (fun mask => (mask,id))

def c4401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4401 : Upper (D 7) (R 7) [12,288,3,192,96,128,2] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,96,128,2] 13 (by decide) (choices 1) [1,16] r4401 c4401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u341
  · exact u342

def b4402 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 13 290 7 200 112 160 80 131 259), lower := (rows 13 290 7 200 112 160 80 128 256), losses := [] }

theorem u4402 : Upper (D 7) (R 7) [12,288,3,192,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4402 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4403 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 21 41 82 160 66 192 448), lower := (rows 13 290 21 41 82 160 66 128 256), losses := [] }

theorem u4403 : Upper (D 7) (R 7) [12,288,17,33,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4404 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(0,1),(1,0),(4,0),(4,5)], upper := (rows 13 290 21 41 82 160 192 194 322), lower := (rows 13 290 21 41 82 160 192 128 256), losses := [{ target := 1, region := (rows 21 0 20 24 16 224 224 128 256), good := (rows 13 352 29 105 125 224 224 224 256) }] }

theorem u4404 : Upper (D 7) (R 7) [12,288,17,33,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4405 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 21 74 112 160 65 130 386), lower := (rows 13 290 21 74 112 160 65 128 256), losses := [] }

theorem u4405 : Upper (D 7) (R 7) [12,288,17,66,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4406 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 21 74 112 160 66 129 385), lower := (rows 13 290 21 74 112 160 66 128 256), losses := [] }

theorem u4406 : Upper (D 7) (R 7) [12,288,17,66,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4407 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 21 74 112 160 192 131 259), lower := (rows 13 290 21 74 112 160 192 128 256), losses := [] }

theorem u4407 : Upper (D 7) (R 7) [12,288,17,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4408 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(4,5)], upper := (rows 13 290 21 74 146 33 96 192 448), lower := (rows 13 290 21 74 146 33 96 128 256), losses := [] }

theorem u4408 : Upper (D 7) (R 7) [12,288,17,66,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4409 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 5, region := 450, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 290 21 74 146 33 192 224 352), lower := (rows 13 290 21 74 146 33 192 128 256), losses := [] }

theorem u4409 : Upper (D 7) (R 7) [12,288,17,66,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4410 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 4, region := 77, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(3,5)], upper := (rows 13 290 21 74 146 96 65 160 416), lower := (rows 13 290 21 74 146 96 65 128 256), losses := [] }

theorem u4410 : Upper (D 7) (R 7) [12,288,17,66,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4411 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 149, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 13 290 21 74 146 96 96 129 385), lower := (rows 13 290 21 74 146 96 96 128 256), losses := [] }

theorem u4411 : Upper (D 7) (R 7) [12,288,17,66,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4412 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 290 21 74 146 96 192 161 289), lower := (rows 13 290 21 74 146 96 192 128 256), losses := [] }

theorem u4412 : Upper (D 7) (R 7) [12,288,17,66,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4413 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 21 74 146 160 65 224 352), lower := (rows 13 290 21 74 146 160 65 128 256), losses := [] }

theorem u4413 : Upper (D 7) (R 7) [12,288,17,66,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4414 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 290 21 74 146 160 96 193 321), lower := (rows 13 290 21 74 146 160 96 128 256), losses := [] }

theorem u4414 : Upper (D 7) (R 7) [12,288,17,66,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4415 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 8, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 74 176 34 65 192 448), lower := (rows 13 290 21 74 176 34 65 128 256), losses := [] }

theorem u4415 : Upper (D 7) (R 7) [12,288,17,66,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4416 : Route 9 := (fun mask => (mask,id))

def c4416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4416 : Upper (D 7) (R 7) [12,288,17,66,160,2,128] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,160,2,128] 13 (by decide) (choices 1) [1,64] r4416 c4416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u343
  · exact u344

def b4417 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 74 176 96 65 130 386), lower := (rows 13 290 21 74 176 96 65 128 256), losses := [] }

theorem u4417 : Upper (D 7) (R 7) [12,288,17,66,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4418 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 13 290 21 74 176 96 66 129 385), lower := (rows 13 290 21 74 176 96 66 128 256), losses := [] }

theorem u4418 : Upper (D 7) (R 7) [12,288,17,66,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4419 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 48, targets := 3 }], pairs := [(0,1),(2,1),(4,0),(4,1)], upper := (rows 13 290 21 74 176 96 192 131 259), lower := (rows 13 290 21 74 176 96 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 208 252 208 128 256), good := (rows 45 288 117 125 240 112 240 240 256) }] }

theorem u4419 : Upper (D 7) (R 7) [12,288,17,66,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4420 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 74 208 34 65 160 416), lower := (rows 13 290 21 74 208 34 65 128 256), losses := [] }

theorem u4420 : Upper (D 7) (R 7) [12,288,17,66,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4421 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 149, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 21 74 208 34 96 129 385), lower := (rows 13 290 21 74 208 34 96 128 256), losses := [] }

theorem u4421 : Upper (D 7) (R 7) [12,288,17,66,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4422 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 21 74 208 34 192 161 289), lower := (rows 13 290 21 74 208 34 192 128 256), losses := [] }

theorem u4422 : Upper (D 7) (R 7) [12,288,17,66,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4423 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 74 208 160 65 162 290), lower := (rows 13 290 21 74 208 160 65 128 256), losses := [] }

theorem u4423 : Upper (D 7) (R 7) [12,288,17,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4424 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 72, targets := 161 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 13 290 21 74 208 160 66 161 289), lower := (rows 13 290 21 74 208 160 66 128 256), losses := [] }

theorem u4424 : Upper (D 7) (R 7) [12,288,17,66,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4425 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 290 21 74 208 160 96 131 259), lower := (rows 13 290 21 74 208 160 96 128 256), losses := [] }

theorem u4425 : Upper (D 7) (R 7) [12,288,17,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4426 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 21 104 82 160 65 130 386), lower := (rows 13 290 21 104 82 160 65 128 256), losses := [] }

theorem u4426 : Upper (D 7) (R 7) [12,288,17,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4427 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 21 104 82 160 66 129 385), lower := (rows 13 290 21 104 82 160 66 128 256), losses := [] }

theorem u4427 : Upper (D 7) (R 7) [12,288,17,96,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4428 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 21 104 82 160 192 131 259), lower := (rows 13 290 21 104 82 160 192 128 256), losses := [] }

theorem u4428 : Upper (D 7) (R 7) [12,288,17,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4429 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 6, region := 418, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 21 104 146 34 65 192 448), lower := (rows 13 290 21 104 146 34 65 128 256), losses := [] }

theorem u4429 : Upper (D 7) (R 7) [12,288,17,96,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4430 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 104, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 290 21 104 146 34 192 193 321), lower := (rows 13 290 21 104 146 34 192 128 256), losses := [] }

theorem u4430 : Upper (D 7) (R 7) [12,288,17,96,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4431 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 6, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 290 21 104 146 160 65 194 322), lower := (rows 13 290 21 104 146 160 65 128 256), losses := [] }

theorem u4431 : Upper (D 7) (R 7) [12,288,17,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4432 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 72, targets := 129 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 13 290 21 104 146 160 66 193 321), lower := (rows 13 290 21 104 146 160 66 128 256), losses := [{ target := 7, region := (rows 17 2 20 10 16 32 82 0 276), good := (rows 269 362 341 104 351 32 74 0 256) }] }

theorem u4432 : Upper (D 7) (R 7) [12,288,17,96,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4433 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 104 208 34 65 130 386), lower := (rows 13 290 21 104 208 34 65 128 256), losses := [] }

theorem u4433 : Upper (D 7) (R 7) [12,288,17,96,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4434 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 149, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 21 104 208 34 66 129 385), lower := (rows 13 290 21 104 208 34 66 128 256), losses := [] }

theorem u4434 : Upper (D 7) (R 7) [12,288,17,96,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4435 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 21 104 208 34 192 131 259), lower := (rows 13 290 21 104 208 34 192 128 256), losses := [] }

theorem u4435 : Upper (D 7) (R 7) [12,288,17,96,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4436 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 200 82 34 65 160 416), lower := (rows 13 290 21 200 82 34 65 128 256), losses := [] }

theorem u4436 : Upper (D 7) (R 7) [12,288,17,192,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4437 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 21 200 82 34 96 129 385), lower := (rows 13 290 21 200 82 34 96 128 256), losses := [] }

theorem u4437 : Upper (D 7) (R 7) [12,288,17,192,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4438 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 21 200 82 34 192 161 289), lower := (rows 13 290 21 200 82 34 192 128 256), losses := [] }

theorem u4438 : Upper (D 7) (R 7) [12,288,17,192,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4439 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 200 82 160 65 162 290), lower := (rows 13 290 21 200 82 160 65 128 256), losses := [] }

theorem u4439 : Upper (D 7) (R 7) [12,288,17,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4439
end Delivery.IrregularNine14.P07
