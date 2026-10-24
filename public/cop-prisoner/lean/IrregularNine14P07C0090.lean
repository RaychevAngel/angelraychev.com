import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5400 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 184, targets := 1 }], pairs := [(3,0),(3,1),(3,7),(4,0)], upper := (rows 35 70 261 104 146 160 65 152 280), lower := (rows 35 70 261 104 146 160 65 128 256), losses := [] }

theorem u5400 : Upper (D 7) (R 7) [34,68,257,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5401 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 261 104 146 160 72 145 273), lower := (rows 35 70 261 104 146 160 72 128 256), losses := [] }

theorem u5401 : Upper (D 7) (R 7) [34,68,257,96,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5401 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5402 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 261 104 146 160 80 137 265), lower := (rows 35 70 261 104 146 160 80 128 256), losses := [] }

theorem u5402 : Upper (D 7) (R 7) [34,68,257,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5402 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5403 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 184, targets := 1 }], pairs := [(3,0),(3,1),(3,7),(4,0)], upper := (rows 35 70 261 104 152 160 65 146 274), lower := (rows 35 70 261 104 152 160 65 128 256), losses := [] }

theorem u5403 : Upper (D 7) (R 7) [34,68,257,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5404 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 72, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 35 70 261 104 152 160 66 145 273), lower := (rows 35 70 261 104 152 160 66 128 256), losses := [] }

theorem u5404 : Upper (D 7) (R 7) [34,68,257,96,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5405 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 70 261 104 152 160 80 131 259), lower := (rows 35 70 261 104 152 160 80 128 256), losses := [] }

theorem u5405 : Upper (D 7) (R 7) [34,68,257,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5405 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5406 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 261 137 208 40 66 176 304), lower := (rows 35 70 261 137 208 40 66 128 256), losses := [] }

theorem u5406 : Upper (D 7) (R 7) [34,68,257,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5406 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5407 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 261 137 208 40 80 162 290), lower := (rows 35 70 261 137 208 40 80 128 256), losses := [] }

theorem u5407 : Upper (D 7) (R 7) [34,68,257,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5407 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5408 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 144, targets := 33 },{ cop := 3, region := 112, targets := 2 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 70 261 137 208 40 96 146 274), lower := (rows 35 70 261 137 208 40 96 128 256), losses := [] }

theorem u5408 : Upper (D 7) (R 7) [34,68,257,129,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5408 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5409 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 396, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 70 261 137 208 48 66 168 296), lower := (rows 35 70 261 137 208 48 66 128 256), losses := [] }

theorem u5409 : Upper (D 7) (R 7) [34,68,257,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5409 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5410 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 261 137 208 48 72 162 290), lower := (rows 35 70 261 137 208 48 72 128 256), losses := [] }

theorem u5410 : Upper (D 7) (R 7) [34,68,257,129,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5410 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5411 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 35 70 261 137 208 48 96 138 266), lower := (rows 35 70 261 137 208 48 96 128 256), losses := [] }

theorem u5411 : Upper (D 7) (R 7) [34,68,257,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5411 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5412 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 184, targets := 1 }], pairs := [(2,6),(3,0),(3,6)], upper := (rows 35 70 261 138 208 48 65 168 296), lower := (rows 35 70 261 138 208 48 65 128 256), losses := [] }

theorem u5412 : Upper (D 7) (R 7) [34,68,257,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5412 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5413 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 261 138 208 48 72 161 289), lower := (rows 35 70 261 138 208 48 72 128 256), losses := [] }

theorem u5413 : Upper (D 7) (R 7) [34,68,257,130,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5413 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5414 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 35 70 261 138 208 48 96 137 265), lower := (rows 35 70 261 138 208 48 96 128 256), losses := [] }

theorem u5414 : Upper (D 7) (R 7) [34,68,257,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5414 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5415 : Route 9 := (fun mask => (mask,id))

def c5415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5415 : Upper (D 7) (R 7) [34,68,258,17,192,128,1] 13 := by
  apply FastRouting.sound _ _ [34,68,258,17,192,128,1] 13 (by decide) (choices 1) [8,32] r5415 c5415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u406
  · exact u407

def b5416 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 70 262 25 208 160 72 161 289), lower := (rows 35 70 262 25 208 160 72 128 256), losses := [] }

theorem u5416 : Upper (D 7) (R 7) [34,68,258,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5416 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5417 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 5, region := 80, targets := 1 }], pairs := [(1,7),(3,1),(4,0),(4,1)], upper := (rows 35 70 262 25 208 160 96 137 265), lower := (rows 35 70 262 25 208 160 96 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 32 97 0 264), good := (rows 99 70 262 351 80 96 96 0 256) }] }

theorem u5417 : Upper (D 7) (R 7) [34,68,258,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5418 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 0, region := 88, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(3,1)], upper := (rows 35 70 262 56 81 160 65 136 392), lower := (rows 35 70 262 56 81 160 65 128 256), losses := [] }

theorem u5418 : Upper (D 7) (R 7) [34,68,258,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5419 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 88, targets := 2 },{ cop := 0, region := 88, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 262 56 81 160 72 129 385), lower := (rows 35 70 262 56 81 160 72 128 256), losses := [] }

theorem u5419 : Upper (D 7) (R 7) [34,68,258,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5419 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5420 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 4, region := 168, targets := 64 }], pairs := [(3,0),(3,1),(3,6),(4,1)], upper := (rows 35 70 262 56 81 160 192 137 265), lower := (rows 35 70 262 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 98 102 262 120 120 224 224 224 256) }] }

theorem u5420 : Upper (D 7) (R 7) [34,68,258,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5421 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 262 73 145 160 72 176 304), lower := (rows 35 70 262 73 145 160 72 128 256), losses := [] }

theorem u5421 : Upper (D 7) (R 7) [34,68,258,65,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5421 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5422 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 35 70 262 73 145 160 80 168 296), lower := (rows 35 70 262 73 145 160 80 128 256), losses := [] }

theorem u5422 : Upper (D 7) (R 7) [34,68,258,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5422 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5423 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 262 73 145 160 96 152 280), lower := (rows 35 70 262 73 145 160 96 128 256), losses := [] }

theorem u5423 : Upper (D 7) (R 7) [34,68,258,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5424 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 35 70 262 73 152 160 65 176 304), lower := (rows 35 70 262 73 152 160 65 128 256), losses := [] }

theorem u5424 : Upper (D 7) (R 7) [34,68,258,65,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5425 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 70 262 73 152 160 80 161 289), lower := (rows 35 70 262 73 152 160 80 128 256), losses := [] }

theorem u5425 : Upper (D 7) (R 7) [34,68,258,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5425 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5426 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 262 73 152 160 96 145 273), lower := (rows 35 70 262 73 152 160 96 128 256), losses := [] }

theorem u5426 : Upper (D 7) (R 7) [34,68,258,65,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5427 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 70 262 88 145 160 65 168 296), lower := (rows 35 70 262 88 145 160 65 128 256), losses := [] }

theorem u5427 : Upper (D 7) (R 7) [34,68,258,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5428 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 262 88 145 160 72 161 289), lower := (rows 35 70 262 88 145 160 72 128 256), losses := [] }

theorem u5428 : Upper (D 7) (R 7) [34,68,258,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5428 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5429 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 4, region := 104, targets := 1 }], pairs := [(1,7),(3,0),(3,1),(4,1)], upper := (rows 35 70 262 88 145 160 96 137 265), lower := (rows 35 70 262 88 145 160 96 128 256), losses := [{ target := 7, region := (rows 1 26 28 24 16 32 97 0 272), good := (rows 99 70 262 350 351 96 96 0 256) }] }

theorem u5429 : Upper (D 7) (R 7) [34,68,258,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5430 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 262 104 145 48 65 136 392), lower := (rows 35 70 262 104 145 48 65 128 256), losses := [] }

theorem u5430 : Upper (D 7) (R 7) [34,68,258,96,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5430 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5431 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 262 104 145 48 72 129 385), lower := (rows 35 70 262 104 145 48 72 128 256), losses := [] }

theorem u5431 : Upper (D 7) (R 7) [34,68,258,96,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5431 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5432 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 262 104 145 48 192 137 265), lower := (rows 35 70 262 104 145 48 192 128 256), losses := [] }

theorem u5432 : Upper (D 7) (R 7) [34,68,258,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5432 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5433 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 72, targets := 128 }], pairs := [(1,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 262 104 145 160 65 152 280), lower := (rows 35 70 262 104 145 160 65 128 256), losses := [{ target := 7, region := (rows 1 18 20 9 16 32 81 0 272), good := (rows 107 70 262 104 351 32 73 0 256) }] }

theorem u5433 : Upper (D 7) (R 7) [34,68,258,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5434 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 262 104 145 160 72 145 273), lower := (rows 35 70 262 104 145 160 72 128 256), losses := [] }

theorem u5434 : Upper (D 7) (R 7) [34,68,258,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5434 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5435 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 262 104 145 160 80 137 265), lower := (rows 35 70 262 104 145 160 80 128 256), losses := [] }

theorem u5435 : Upper (D 7) (R 7) [34,68,258,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5435 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5436 : Route 9 := (fun mask => (mask,id))

def c5436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5436 : Upper (D 7) (R 7) [34,68,258,96,136,128,1] 13 := by
  apply FastRouting.sound _ _ [34,68,258,96,136,128,1] 13 (by decide) (choices 1) [1,16] r5436 c5436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u408
  · exact u409

def b5437 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 70 262 104 152 160 80 129 257), lower := (rows 35 70 262 104 152 160 80 128 256), losses := [] }

theorem u5437 : Upper (D 7) (R 7) [34,68,258,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5437 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5438 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 80, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 35 70 262 137 208 40 65 176 304), lower := (rows 35 70 262 137 208 40 65 128 256), losses := [] }

theorem u5438 : Upper (D 7) (R 7) [34,68,258,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5438 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5439 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 262 137 208 40 80 161 289), lower := (rows 35 70 262 137 208 40 80 128 256), losses := [] }

theorem u5439 : Upper (D 7) (R 7) [34,68,258,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5439 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5440 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 112, targets := 1 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 35 70 262 137 208 40 96 145 273), lower := (rows 35 70 262 137 208 40 96 128 256), losses := [] }

theorem u5440 : Upper (D 7) (R 7) [34,68,258,129,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5440 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5441 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 268 26 112 160 65 129 385), lower := (rows 35 70 268 26 112 160 65 128 256), losses := [] }

theorem u5441 : Upper (D 7) (R 7) [34,68,264,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5442 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 268 26 112 160 192 129 257), lower := (rows 35 70 268 26 112 160 192 128 256), losses := [] }

theorem u5442 : Upper (D 7) (R 7) [34,68,264,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5443 : Route 9 := (fun mask => (mask,id))

def c5443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5443 : Upper (D 7) (R 7) [34,68,264,18,192,128,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,18,192,128,1] 13 (by decide) (choices 1) [1,32] r5443 c5443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u410
  · exact u411

def b5444 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 70 268 26 208 160 96 129 257), lower := (rows 35 70 268 26 208 160 96 128 256), losses := [] }

theorem u5444 : Upper (D 7) (R 7) [34,68,264,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5445 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 144, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 35 70 268 56 208 33 65 130 386), lower := (rows 35 70 268 56 208 33 65 128 256), losses := [] }

theorem u5445 : Upper (D 7) (R 7) [34,68,264,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5446 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 70 268 56 208 33 66 129 385), lower := (rows 35 70 268 56 208 33 66 128 256), losses := [] }

theorem u5446 : Upper (D 7) (R 7) [34,68,264,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5447 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 268 56 208 33 192 131 259), lower := (rows 35 70 268 56 208 33 192 128 256), losses := [] }

theorem u5447 : Upper (D 7) (R 7) [34,68,264,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5448 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 70 268 73 145 160 66 176 304), lower := (rows 35 70 268 73 145 160 66 128 256), losses := [] }

theorem u5448 : Upper (D 7) (R 7) [34,68,264,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5449 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 3, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 70 268 73 145 160 80 162 290), lower := (rows 35 70 268 73 145 160 80 128 256), losses := [] }

theorem u5449 : Upper (D 7) (R 7) [34,68,264,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5449 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5450 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 268 73 145 160 96 146 274), lower := (rows 35 70 268 73 145 160 96 128 256), losses := [] }

theorem u5450 : Upper (D 7) (R 7) [34,68,264,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5451 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 35 70 268 73 146 160 65 176 304), lower := (rows 35 70 268 73 146 160 65 128 256), losses := [] }

theorem u5451 : Upper (D 7) (R 7) [34,68,264,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5452 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 3, region := 420, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 70 268 73 146 160 80 161 289), lower := (rows 35 70 268 73 146 160 80 128 256), losses := [] }

theorem u5452 : Upper (D 7) (R 7) [34,68,264,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5452 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5453 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 268 73 146 160 96 145 273), lower := (rows 35 70 268 73 146 160 96 128 256), losses := [] }

theorem u5453 : Upper (D 7) (R 7) [34,68,264,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5454 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,1),(2,6),(4,6)], upper := (rows 35 70 268 88 146 160 65 161 289), lower := (rows 35 70 268 88 146 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 251 65 193 321), good := (rows 481 484 300 508 176 160 481 160 256) },{ target := 6, region := (rows 19 2 12 8 19 255 0 219 347), good := (rows 435 439 428 445 435 160 433 160 256) }] }

theorem u5454 : Upper (D 7) (R 7) [34,68,264,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5455 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 104, targets := 3 }], pairs := [(0,6),(3,0),(3,1),(4,6)], upper := (rows 35 70 268 88 146 160 96 129 257), lower := (rows 35 70 268 88 146 160 96 128 256), losses := [] }

theorem u5455 : Upper (D 7) (R 7) [34,68,264,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5456 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 268 88 176 33 65 130 386), lower := (rows 35 70 268 88 176 33 65 128 256), losses := [] }

theorem u5456 : Upper (D 7) (R 7) [34,68,264,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5457 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 70 268 88 176 33 66 129 385), lower := (rows 35 70 268 88 176 33 66 128 256), losses := [] }

theorem u5457 : Upper (D 7) (R 7) [34,68,264,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5458 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 268 88 176 33 192 131 259), lower := (rows 35 70 268 88 176 33 192 128 256), losses := [] }

theorem u5458 : Upper (D 7) (R 7) [34,68,264,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5459 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(3,7),(4,6)], upper := (rows 35 70 268 104 145 160 65 146 274), lower := (rows 35 70 268 104 145 160 65 128 256), losses := [] }

theorem u5459 : Upper (D 7) (R 7) [34,68,264,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5459
end Delivery.IrregularNine14.P07
