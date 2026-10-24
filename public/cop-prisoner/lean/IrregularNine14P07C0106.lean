import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6360 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 3, region := 161, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 26 84 160 96 129 385), lower := (rows 35 322 13 26 84 160 96 128 256), losses := [] }

theorem u6360 : Upper (D 7) (R 7) [34,320,9,18,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6361 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 2, region := 240, targets := 2 }], pairs := [(0,6),(2,5),(2,6),(4,1)], upper := (rows 35 322 13 26 84 160 192 161 289), lower := (rows 35 322 13 26 84 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 224 128 256), good := (rows 95 322 29 26 84 192 192 192 256) }] }

theorem u6361 : Upper (D 7) (R 7) [34,320,9,18,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6362 : Route 9 := (fun mask => (mask,id))

def c6362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6362 : Upper (D 7) (R 7) [34,320,9,18,192,128,1] 13 := by
  apply FastRouting.sound _ _ [34,320,9,18,192,128,1] 13 (by decide) (choices 1) [4,32] r6362 c6362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u468
  · exact u469

def b6363 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 2, region := 240, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 35 322 13 26 208 160 68 161 289), lower := (rows 35 322 13 26 208 160 68 128 256), losses := [] }

theorem u6363 : Upper (D 7) (R 7) [34,320,9,18,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6363 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6364 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 322 13 26 208 160 96 133 261), lower := (rows 35 322 13 26 208 160 96 128 256), losses := [] }

theorem u6364 : Upper (D 7) (R 7) [34,320,9,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6365 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 92, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 322 13 28 112 160 65 130 386), lower := (rows 35 322 13 28 112 160 65 128 256), losses := [] }

theorem u6365 : Upper (D 7) (R 7) [34,320,9,20,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6366 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 8, region := 66, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 28 112 160 66 129 385), lower := (rows 35 322 13 28 112 160 66 128 256), losses := [] }

theorem u6366 : Upper (D 7) (R 7) [34,320,9,20,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6367 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 13 28 112 160 192 131 259), lower := (rows 35 322 13 28 112 160 192 128 256), losses := [] }

theorem u6367 : Upper (D 7) (R 7) [34,320,9,20,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6368 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 35 322 13 28 208 160 65 162 290), lower := (rows 35 322 13 28 208 160 65 128 256), losses := [] }

theorem u6368 : Upper (D 7) (R 7) [34,320,9,20,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6369 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(1,7)], upper := (rows 35 322 13 28 208 160 66 161 289), lower := (rows 35 322 13 28 208 160 66 128 256), losses := [] }

theorem u6369 : Upper (D 7) (R 7) [34,320,9,20,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6370 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 322 13 28 208 160 96 131 259), lower := (rows 35 322 13 28 208 160 96 128 256), losses := [] }

theorem u6370 : Upper (D 7) (R 7) [34,320,9,20,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6371 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 172, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 35 322 13 56 81 160 66 132 388), lower := (rows 35 322 13 56 81 160 66 128 256), losses := [] }

theorem u6371 : Upper (D 7) (R 7) [34,320,9,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6372 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 92, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 322 13 56 81 160 68 130 386), lower := (rows 35 322 13 56 81 160 68 128 256), losses := [] }

theorem u6372 : Upper (D 7) (R 7) [34,320,9,48,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6372 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6373 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 35 322 13 56 81 160 192 134 262), lower := (rows 35 322 13 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 228 228 132 260), good := (rows 98 354 494 120 120 224 224 224 256) }] }

theorem u6373 : Upper (D 7) (R 7) [34,320,9,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6374 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 322 13 56 208 36 65 130 386), lower := (rows 35 322 13 56 208 36 65 128 256), losses := [] }

theorem u6374 : Upper (D 7) (R 7) [34,320,9,48,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6374 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6375 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 322 13 56 208 36 66 129 385), lower := (rows 35 322 13 56 208 36 66 128 256), losses := [] }

theorem u6375 : Upper (D 7) (R 7) [34,320,9,48,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6375 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6376 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 56 208 36 192 131 259), lower := (rows 35 322 13 56 208 36 192 128 256), losses := [] }

theorem u6376 : Upper (D 7) (R 7) [34,320,9,48,192,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6376 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6377 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 322 13 76 145 160 66 176 304), lower := (rows 35 322 13 76 145 160 66 128 256), losses := [] }

theorem u6377 : Upper (D 7) (R 7) [34,320,9,68,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6378 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 322 13 76 145 160 80 162 290), lower := (rows 35 322 13 76 145 160 80 128 256), losses := [] }

theorem u6378 : Upper (D 7) (R 7) [34,320,9,68,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6378 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6379 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 322 13 76 145 160 96 146 274), lower := (rows 35 322 13 76 145 160 96 128 256), losses := [] }

theorem u6379 : Upper (D 7) (R 7) [34,320,9,68,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6380 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 35 322 13 76 146 160 65 176 304), lower := (rows 35 322 13 76 146 160 65 128 256), losses := [] }

theorem u6380 : Upper (D 7) (R 7) [34,320,9,68,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6381 : Route 9 := (fun mask => (mask,id))

def c6381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6381 : Upper (D 7) (R 7) [34,320,9,68,130,128,16] 13 := by
  apply FastRouting.sound _ _ [34,320,9,68,130,128,16] 13 (by decide) (choices 1) [1,32] r6381 c6381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u470
  · exact u471

def b6382 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 322 13 76 146 160 96 145 273), lower := (rows 35 322 13 76 146 160 96 128 256), losses := [] }

theorem u6382 : Upper (D 7) (R 7) [34,320,9,68,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6383 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 322 13 88 22 160 65 160 416), lower := (rows 35 322 13 88 22 160 65 128 256), losses := [] }

theorem u6383 : Upper (D 7) (R 7) [34,320,9,80,6,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6384 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 88 22 160 96 129 385), lower := (rows 35 322 13 88 22 160 96 128 256), losses := [] }

theorem u6384 : Upper (D 7) (R 7) [34,320,9,80,6,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6385 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,5),(3,1),(3,5)], upper := (rows 35 322 13 88 22 160 192 161 289), lower := (rows 35 322 13 88 22 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 245 245 133 261), good := (rows 481 352 493 120 508 224 224 224 256) },{ target := 5, region := (rows 1 2 5 9 17 0 224 128 256), good := (rows 95 322 29 88 22 192 192 192 256) }] }

theorem u6385 : Upper (D 7) (R 7) [34,320,9,80,6,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6386 : PairBound 9 := { available := 36, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 2, region := 176, targets := 2 }], pairs := [(1,0),(1,5),(1,7),(4,1)], upper := (rows 35 322 13 88 145 160 66 164 292), lower := (rows 35 322 13 88 145 160 66 128 256), losses := [] }

theorem u6386 : Upper (D 7) (R 7) [34,320,9,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6387 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 322 13 88 145 160 68 162 290), lower := (rows 35 322 13 88 145 160 68 128 256), losses := [] }

theorem u6387 : Upper (D 7) (R 7) [34,320,9,80,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6387 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6388 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 104, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 35 322 13 88 145 160 96 134 262), lower := (rows 35 322 13 88 145 160 96 128 256), losses := [] }

theorem u6388 : Upper (D 7) (R 7) [34,320,9,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6389 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 13 88 146 36 65 160 416), lower := (rows 35 322 13 88 146 36 65 128 256), losses := [] }

theorem u6389 : Upper (D 7) (R 7) [34,320,9,80,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6389 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6390 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 13 88 146 36 96 129 385), lower := (rows 35 322 13 88 146 36 96 128 256), losses := [] }

theorem u6390 : Upper (D 7) (R 7) [34,320,9,80,130,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6390 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6391 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 88 146 36 192 161 289), lower := (rows 35 322 13 88 146 36 192 128 256), losses := [] }

theorem u6391 : Upper (D 7) (R 7) [34,320,9,80,130,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6391 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6392 : Route 9 := (fun mask => (mask,id))

def c6392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6392 : Upper (D 7) (R 7) [34,320,9,80,130,128,1] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,130,128,1] 13 (by decide) (choices 1) [4,32] r6392 c6392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u472
  · exact u473

def b6393 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 322 13 88 146 160 68 161 289), lower := (rows 35 322 13 88 146 160 68 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 255 0 159 287), good := (rows 435 435 445 445 435 160 420 160 256) }] }

theorem u6393 : Upper (D 7) (R 7) [34,320,9,80,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6393 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6394 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 35 322 13 88 146 160 96 133 261), lower := (rows 35 322 13 88 146 160 96 128 256), losses := [{ target := 6, region := (rows 17 2 12 8 16 188 0 140 268), good := (rows 35 258 429 445 179 160 32 160 256) }] }

theorem u6394 : Upper (D 7) (R 7) [34,320,9,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6395 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 386, targets := 33 },{ cop := 0, region := 144, targets := 1 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 322 13 88 176 36 65 130 386), lower := (rows 35 322 13 88 176 36 65 128 256), losses := [] }

theorem u6395 : Upper (D 7) (R 7) [34,320,9,80,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6395 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6396 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 322 13 88 176 36 66 129 385), lower := (rows 35 322 13 88 176 36 66 128 256), losses := [] }

theorem u6396 : Upper (D 7) (R 7) [34,320,9,80,160,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6396 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6397 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 88 176 36 192 131 259), lower := (rows 35 322 13 88 176 36 192 128 256), losses := [] }

theorem u6397 : Upper (D 7) (R 7) [34,320,9,80,160,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6397 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6398 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 104 22 160 65 144 400), lower := (rows 35 322 13 104 22 160 65 128 256), losses := [] }

theorem u6398 : Upper (D 7) (R 7) [34,320,9,96,6,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6399 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 322 13 104 22 160 80 129 385), lower := (rows 35 322 13 104 22 160 80 128 256), losses := [] }

theorem u6399 : Upper (D 7) (R 7) [34,320,9,96,6,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6399 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6400 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 322 13 104 22 160 192 145 273), lower := (rows 35 322 13 104 22 160 192 128 256), losses := [] }

theorem u6400 : Upper (D 7) (R 7) [34,320,9,96,6,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6401 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 0, region := 76, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(2,7)], upper := (rows 35 322 13 104 145 160 66 148 276), lower := (rows 35 322 13 104 145 160 66 128 256), losses := [] }

theorem u6401 : Upper (D 7) (R 7) [34,320,9,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6402 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 322 13 104 145 160 68 146 274), lower := (rows 35 322 13 104 145 160 68 128 256), losses := [] }

theorem u6402 : Upper (D 7) (R 7) [34,320,9,96,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6402 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6403 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 104 145 160 80 134 262), lower := (rows 35 322 13 104 145 160 80 128 256), losses := [] }

theorem u6403 : Upper (D 7) (R 7) [34,320,9,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6403 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6404 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 322 13 104 146 160 65 148 276), lower := (rows 35 322 13 104 146 160 65 128 256), losses := [] }

theorem u6404 : Upper (D 7) (R 7) [34,320,9,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6405 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 322 13 104 146 160 68 145 273), lower := (rows 35 322 13 104 146 160 68 128 256), losses := [] }

theorem u6405 : Upper (D 7) (R 7) [34,320,9,96,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6405 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6406 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 104 146 160 80 133 261), lower := (rows 35 322 13 104 146 160 80 128 256), losses := [] }

theorem u6406 : Upper (D 7) (R 7) [34,320,9,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6406 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6407 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 322 13 104 148 160 65 146 274), lower := (rows 35 322 13 104 148 160 65 128 256), losses := [] }

theorem u6407 : Upper (D 7) (R 7) [34,320,9,96,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6408 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 0, region := 76, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(2,7)], upper := (rows 35 322 13 104 148 160 66 145 273), lower := (rows 35 322 13 104 148 160 66 128 256), losses := [] }

theorem u6408 : Upper (D 7) (R 7) [34,320,9,96,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6409 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 104 148 160 80 131 259), lower := (rows 35 322 13 104 148 160 80 128 256), losses := [] }

theorem u6409 : Upper (D 7) (R 7) [34,320,9,96,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6409 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6410 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 80, targets := 160 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,5),(4,7)], upper := (rows 35 322 13 138 81 160 68 176 304), lower := (rows 35 322 13 138 81 160 68 128 256), losses := [] }

theorem u6410 : Upper (D 7) (R 7) [34,320,9,130,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6410 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6411 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 35 322 13 138 81 160 80 164 292), lower := (rows 35 322 13 138 81 160 80 128 256), losses := [] }

theorem u6411 : Upper (D 7) (R 7) [34,320,9,130,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6411 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6412 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 322 13 138 81 160 96 148 276), lower := (rows 35 322 13 138 81 160 96 128 256), losses := [] }

theorem u6412 : Upper (D 7) (R 7) [34,320,9,130,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6413 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 80, targets := 160 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(4,5),(4,7)], upper := (rows 35 322 13 138 84 160 65 176 304), lower := (rows 35 322 13 138 84 160 65 128 256), losses := [] }

theorem u6413 : Upper (D 7) (R 7) [34,320,9,130,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6414 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 13 138 84 160 80 161 289), lower := (rows 35 322 13 138 84 160 80 128 256), losses := [] }

theorem u6414 : Upper (D 7) (R 7) [34,320,9,130,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6414 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6415 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 2, region := 240, targets := 2 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 322 13 138 84 160 96 145 273), lower := (rows 35 322 13 138 84 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 237 128 256), good := (rows 98 322 124 234 84 224 96 224 256) }] }

theorem u6415 : Upper (D 7) (R 7) [34,320,9,130,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6416 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(4,1),(4,7)], upper := (rows 35 322 13 138 112 160 65 148 276), lower := (rows 35 322 13 138 112 160 65 128 256), losses := [] }

theorem u6416 : Upper (D 7) (R 7) [34,320,9,130,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6417 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 4, region := 259, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 138 112 160 68 145 273), lower := (rows 35 322 13 138 112 160 68 128 256), losses := [] }

theorem u6417 : Upper (D 7) (R 7) [34,320,9,130,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6417 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6418 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 13 138 112 160 80 133 261), lower := (rows 35 322 13 138 112 160 80 128 256), losses := [] }

theorem u6418 : Upper (D 7) (R 7) [34,320,9,130,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6418 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6419 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 35 322 13 140 112 160 65 146 274), lower := (rows 35 322 13 140 112 160 65 128 256), losses := [] }

theorem u6419 : Upper (D 7) (R 7) [34,320,9,132,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6419
end Delivery.IrregularNine14.P07
