import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0007

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6360 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 28 82 288 68 193 321), lower := (rows 35 131 44 28 82 288 68 128 256), losses := [] }

theorem u6360 : Upper (D 6) (R 6) [34,129,40,20,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6360 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6361 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 28 273 96 66 196 324), lower := (rows 35 131 44 28 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 115 67 144 272), good := (rows 98 226 44 444 508 96 98 128 256) }] }

theorem u6361 : Upper (D 6) (R 6) [34,129,40,20,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6362 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 28 273 96 68 194 322), lower := (rows 35 131 44 28 273 96 68 128 256), losses := [] }

theorem u6362 : Upper (D 6) (R 6) [34,129,40,20,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6363 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 28 274 96 65 196 324), lower := (rows 35 131 44 28 274 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 101 75 17 96 64 224 352), good := (rows 446 158 428 28 282 492 508 128 256) }] }

theorem u6363 : Upper (D 6) (R 6) [34,129,40,20,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6364 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 28 274 96 68 193 321), lower := (rows 35 131 44 28 274 96 68 128 256), losses := [] }

theorem u6364 : Upper (D 6) (R 6) [34,129,40,20,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6365 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 73 22 288 68 208 336), lower := (rows 35 131 44 73 22 288 68 128 256), losses := [] }

theorem u6365 : Upper (D 6) (R 6) [34,129,40,65,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6365 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6366 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 292, targets := 1 }], pairs := [(2,0)], upper := (rows 35 131 44 73 22 288 80 196 324), lower := (rows 35 131 44 73 22 288 80 128 256), losses := [] }

theorem u6366 : Upper (D 6) (R 6) [34,129,40,65,6,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6366 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6367 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 73 82 288 68 148 276), lower := (rows 35 131 44 73 82 288 68 128 256), losses := [] }

theorem u6367 : Upper (D 6) (R 6) [34,129,40,65,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6367 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6368 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 88, targets := 4 }], pairs := [(3,2)], upper := (rows 35 131 44 73 82 288 80 132 260), lower := (rows 35 131 44 73 82 288 80 128 256), losses := [] }

theorem u6368 : Upper (D 6) (R 6) [34,129,40,65,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6368 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6369 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 73 276 48 66 196 324), lower := (rows 35 131 44 73 276 48 66 128 256), losses := [] }

theorem u6369 : Upper (D 6) (R 6) [34,129,40,65,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6369 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6370 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 73 276 48 68 194 322), lower := (rows 35 131 44 73 276 48 68 128 256), losses := [] }

theorem u6370 : Upper (D 6) (R 6) [34,129,40,65,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6370 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6371 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 74 81 288 68 148 276), lower := (rows 35 131 44 74 81 288 68 128 256), losses := [] }

theorem u6371 : Upper (D 6) (R 6) [34,129,40,66,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6371 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6372 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 88, targets := 4 }], pairs := [(3,2)], upper := (rows 35 131 44 74 81 288 80 132 260), lower := (rows 35 131 44 74 81 288 80 128 256), losses := [] }

theorem u6372 : Upper (D 6) (R 6) [34,129,40,66,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6372 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6373 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 74 276 48 65 196 324), lower := (rows 35 131 44 74 276 48 65 128 256), losses := [] }

theorem u6373 : Upper (D 6) (R 6) [34,129,40,66,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6373 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6374 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 74 276 48 68 193 321), lower := (rows 35 131 44 74 276 48 68 128 256), losses := [] }

theorem u6374 : Upper (D 6) (R 6) [34,129,40,66,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6374 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6375 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 76 81 288 66 148 276), lower := (rows 35 131 44 76 81 288 66 128 256), losses := [] }

theorem u6375 : Upper (D 6) (R 6) [34,129,40,68,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6375 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6376 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 44 76 81 288 68 146 274), lower := (rows 35 131 44 76 81 288 68 128 256), losses := [] }

theorem u6376 : Upper (D 6) (R 6) [34,129,40,68,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6376 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6377 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1)], upper := (rows 35 131 44 76 81 288 80 134 262), lower := (rows 35 131 44 76 81 288 80 128 256), losses := [] }

theorem u6377 : Upper (D 6) (R 6) [34,129,40,68,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6377 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6378 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 76 82 288 65 148 276), lower := (rows 35 131 44 76 82 288 65 128 256), losses := [] }

theorem u6378 : Upper (D 6) (R 6) [34,129,40,68,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6378 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6379 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 44 76 82 288 68 145 273), lower := (rows 35 131 44 76 82 288 68 128 256), losses := [] }

theorem u6379 : Upper (D 6) (R 6) [34,129,40,68,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6379 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6380 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0)], upper := (rows 35 131 44 76 82 288 80 133 261), lower := (rows 35 131 44 76 82 288 80 128 256), losses := [] }

theorem u6380 : Upper (D 6) (R 6) [34,129,40,68,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6380 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6381 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 88 22 288 65 196 324), lower := (rows 35 131 44 88 22 288 65 128 256), losses := [] }

theorem u6381 : Upper (D 6) (R 6) [34,129,40,80,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6381 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6382 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 88 22 288 68 193 321), lower := (rows 35 131 44 88 22 288 68 128 256), losses := [] }

theorem u6382 : Upper (D 6) (R 6) [34,129,40,80,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6382 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6383 : Route 9 := (fun mask => (mask,id))

def c6383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6383 : Upper (D 6) (R 6) [34,129,40,257,6,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,6,64,4] 13 (by decide) (choices 1) [16,64] r6383 c6383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u467
  · exact u468

def r6384 : Route 9 := (fun mask => (mask,id))

def c6384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6384 : Upper (D 6) (R 6) [34,129,40,257,6,64,16] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,6,64,16] 13 (by decide) (choices 1) [4,64] r6384 c6384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u469
  · exact u470

def b6385 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 44 265 82 96 68 148 276), lower := (rows 35 131 44 265 82 96 68 128 256), losses := [] }

theorem u6385 : Upper (D 6) (R 6) [34,129,40,257,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6386 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 265 82 96 80 132 260), lower := (rows 35 131 44 265 82 96 80 128 256), losses := [] }

theorem u6386 : Upper (D 6) (R 6) [34,129,40,257,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6386 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6387 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(4,0)], upper := (rows 35 131 44 265 84 48 66 196 324), lower := (rows 35 131 44 265 84 48 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 67 152 280), good := (rows 98 194 444 508 500 432 66 128 256) }] }

theorem u6387 : Upper (D 6) (R 6) [34,129,40,257,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6387 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6388 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 265 84 48 68 194 322), lower := (rows 35 131 44 265 84 48 68 128 256), losses := [] }

theorem u6388 : Upper (D 6) (R 6) [34,129,40,257,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6388 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6389 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 265 84 96 66 148 276), lower := (rows 35 131 44 265 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 123 67 156 284), good := (rows 98 226 444 508 500 96 98 128 256) }] }

theorem u6389 : Upper (D 6) (R 6) [34,129,40,257,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6390 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 44 265 84 96 68 146 274), lower := (rows 35 131 44 265 84 96 68 128 256), losses := [] }

theorem u6390 : Upper (D 6) (R 6) [34,129,40,257,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6391 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 265 84 96 80 134 262), lower := (rows 35 131 44 265 84 96 80 128 256), losses := [] }

theorem u6391 : Upper (D 6) (R 6) [34,129,40,257,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6391 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6392 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(2,1)], upper := (rows 35 131 44 266 21 96 68 208 336), lower := (rows 35 131 44 266 21 96 68 128 256), losses := [] }

theorem u6392 : Upper (D 6) (R 6) [34,129,40,258,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6393 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 131 44 266 21 96 80 196 324), lower := (rows 35 131 44 266 21 96 80 128 256), losses := [] }

theorem u6393 : Upper (D 6) (R 6) [34,129,40,258,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6393 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6394 : Route 9 := (fun mask => (mask,id))

def c6394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6394 : Upper (D 6) (R 6) [34,129,40,258,65,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258,65,64,4] 13 (by decide) (choices 1) [4,16] r6394 c6394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u471
  · exact u472

def b6395 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 266 81 96 80 132 260), lower := (rows 35 131 44 266 81 96 80 128 256), losses := [] }

theorem u6395 : Upper (D 6) (R 6) [34,129,40,258,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6395 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6396 : PairBound 9 := { available := 68, camps := [], pairs := [(2,1),(4,1)], upper := (rows 35 131 44 266 84 48 65 196 324), lower := (rows 35 131 44 266 84 48 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 60 67 152 280), good := (rows 97 193 444 508 500 432 65 128 256) }] }

theorem u6396 : Upper (D 6) (R 6) [34,129,40,258,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6396 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6397 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 266 84 48 68 193 321), lower := (rows 35 131 44 266 84 48 68 128 256), losses := [] }

theorem u6397 : Upper (D 6) (R 6) [34,129,40,258,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6397 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6398 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 266 84 96 65 148 276), lower := (rows 35 131 44 266 84 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 11 112 112 64 245 373), good := (rows 446 398 444 266 500 500 508 128 256) }] }

theorem u6398 : Upper (D 6) (R 6) [34,129,40,258,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6399 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 44 266 84 96 68 145 273), lower := (rows 35 131 44 266 84 96 68 128 256), losses := [] }

theorem u6399 : Upper (D 6) (R 6) [34,129,40,258,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6400 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 266 84 96 80 133 261), lower := (rows 35 131 44 266 84 96 80 128 256), losses := [] }

theorem u6400 : Upper (D 6) (R 6) [34,129,40,258,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6400 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6401 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 268 22 96 65 208 336), lower := (rows 35 131 44 268 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 101 104 19 96 64 192 320), good := (rows 62 150 44 268 22 492 508 128 256) }] }

theorem u6401 : Upper (D 6) (R 6) [34,129,40,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6402 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 44 268 22 96 80 193 321), lower := (rows 35 131 44 268 22 96 80 128 256), losses := [] }

theorem u6402 : Upper (D 6) (R 6) [34,129,40,260,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6402 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6403 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 268 81 96 66 148 276), lower := (rows 35 131 44 268 81 96 66 128 256), losses := [] }

theorem u6403 : Upper (D 6) (R 6) [34,129,40,260,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6404 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 268 81 96 68 146 274), lower := (rows 35 131 44 268 81 96 68 128 256), losses := [] }

theorem u6404 : Upper (D 6) (R 6) [34,129,40,260,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6405 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 268 81 96 80 134 262), lower := (rows 35 131 44 268 81 96 80 128 256), losses := [] }

theorem u6405 : Upper (D 6) (R 6) [34,129,40,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6405 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6406 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 268 82 96 65 148 276), lower := (rows 35 131 44 268 82 96 65 128 256), losses := [] }

theorem u6406 : Upper (D 6) (R 6) [34,129,40,260,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6407 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 268 82 96 68 145 273), lower := (rows 35 131 44 268 82 96 68 128 256), losses := [] }

theorem u6407 : Upper (D 6) (R 6) [34,129,40,260,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6408 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 268 82 96 80 133 261), lower := (rows 35 131 44 268 82 96 80 128 256), losses := [] }

theorem u6408 : Upper (D 6) (R 6) [34,129,40,260,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6408 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6409 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 268 84 96 65 146 274), lower := (rows 35 131 44 268 84 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 117 75 112 112 64 129 257), good := (rows 446 398 60 268 124 124 508 128 256) }] }

theorem u6409 : Upper (D 6) (R 6) [34,129,40,260,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6410 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 131 44 268 84 96 66 145 273), lower := (rows 35 131 44 268 84 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 69 11 112 112 64 129 257), good := (rows 445 397 60 268 116 116 124 128 256) }] }

theorem u6410 : Upper (D 6) (R 6) [34,129,40,260,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6411 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 124, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 268 84 96 80 131 259), lower := (rows 35 131 44 268 84 96 80 128 256), losses := [] }

theorem u6411 : Upper (D 6) (R 6) [34,129,40,260,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6411 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6412 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 35 131 44 280 21 96 66 196 324), lower := (rows 35 131 44 280 21 96 66 128 256), losses := [] }

theorem u6412 : Upper (D 6) (R 6) [34,129,40,272,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6413 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(2,1)], upper := (rows 35 131 44 280 21 96 68 194 322), lower := (rows 35 131 44 280 21 96 68 128 256), losses := [] }

theorem u6413 : Upper (D 6) (R 6) [34,129,40,272,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6414 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 280 22 96 65 196 324), lower := (rows 35 131 44 280 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 101 73 19 96 64 224 352), good := (rows 446 158 428 280 22 492 508 128 256) }] }

theorem u6414 : Upper (D 6) (R 6) [34,129,40,272,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6415 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 5, region := 131, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 44 280 22 96 68 193 321), lower := (rows 35 131 44 280 22 96 68 128 256), losses := [] }

theorem u6415 : Upper (D 6) (R 6) [34,129,40,272,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6416 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 25 276 36 72 224 352), lower := (rows 35 131 70 25 276 36 72 128 256), losses := [] }

theorem u6416 : Upper (D 6) (R 6) [34,129,66,17,260,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6416 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6417 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 35 131 70 25 276 36 96 200 328), lower := (rows 35 131 70 25 276 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 63 127 136 264), good := (rows 102 230 102 508 372 100 96 128 256) }] }

theorem u6417 : Upper (D 6) (R 6) [34,129,66,17,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6418 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,5)], upper := (rows 35 131 70 25 276 96 68 168 296), lower := (rows 35 131 70 25 276 96 68 128 256), losses := [] }

theorem u6418 : Upper (D 6) (R 6) [34,129,66,17,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6419 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 25 276 96 72 164 292), lower := (rows 35 131 70 25 276 96 72 128 256), losses := [] }

theorem u6419 : Upper (D 6) (R 6) [34,129,66,17,260,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6419 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6419
end Delivery.IrregularNine14.P06
