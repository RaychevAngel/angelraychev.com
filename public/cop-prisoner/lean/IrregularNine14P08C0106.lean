import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0013

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6360 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 100 56 146 40 193 193 449), lower := (rows 289 7 100 56 146 40 64 128 256), losses := [] }

theorem u6360 : Upper (D 8) (R 8) [288,5,96,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6360 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6361 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 56 146 96 201 137 393), lower := (rows 289 7 100 56 146 96 64 128 256), losses := [] }

theorem u6361 : Upper (D 8) (R 8) [288,5,96,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6362 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 56 146 160 73 201 329), lower := (rows 289 7 100 56 146 160 64 128 256), losses := [] }

theorem u6362 : Upper (D 8) (R 8) [288,5,96,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6363 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 56 152 33 194 194 450), lower := (rows 289 7 100 56 152 33 64 128 256), losses := [] }

theorem u6363 : Upper (D 8) (R 8) [288,5,96,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6364 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 100 56 152 34 193 193 449), lower := (rows 289 7 100 56 152 34 64 128 256), losses := [] }

theorem u6364 : Upper (D 8) (R 8) [288,5,96,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6364 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6365 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 56 152 96 195 131 387), lower := (rows 289 7 100 56 152 96 64 128 256), losses := [] }

theorem u6365 : Upper (D 8) (R 8) [288,5,96,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6366 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 100 56 152 160 67 195 323), lower := (rows 289 7 100 56 152 160 64 128 256), losses := [] }

theorem u6366 : Upper (D 8) (R 8) [288,5,96,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6367 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 56 208 33 202 138 394), lower := (rows 289 7 100 56 208 33 64 128 256), losses := [] }

theorem u6367 : Upper (D 8) (R 8) [288,5,96,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6368 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 7 100 56 208 34 201 137 393), lower := (rows 289 7 100 56 208 34 64 128 256), losses := [] }

theorem u6368 : Upper (D 8) (R 8) [288,5,96,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6368 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6369 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 7 100 56 208 40 195 131 387), lower := (rows 289 7 100 56 208 40 64 128 256), losses := [] }

theorem u6369 : Upper (D 8) (R 8) [288,5,96,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6369 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6370 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 56 208 160 75 139 267), lower := (rows 289 7 100 56 208 160 64 128 256), losses := [] }

theorem u6370 : Upper (D 8) (R 8) [288,5,96,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6371 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 289 7 100 73 146 40 240 176 432), lower := (rows 289 7 100 73 146 40 64 128 256), losses := [] }

theorem u6371 : Upper (D 8) (R 8) [288,5,96,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6371 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6372 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 289 7 100 73 146 48 232 168 424), lower := (rows 289 7 100 73 146 48 64 128 256), losses := [] }

theorem u6372 : Upper (D 8) (R 8) [288,5,96,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6372 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6373 : Route 9 := (fun mask => (mask,id))

def c6373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6373 : Upper (D 8) (R 8) [288,5,96,65,130,128] 13 := by
  apply FastRouting.sound _ _ [288,5,96,65,130,128] 13 (by decide) (choices 1) [8,16,32] r6373 c6373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u810
  · exact u811
  · exact u812

def b6374 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 289 7 100 73 152 34 240 176 432), lower := (rows 289 7 100 73 152 34 64 128 256), losses := [] }

theorem u6374 : Upper (D 8) (R 8) [288,5,96,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6374 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6375 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 7 100 73 152 48 226 162 418), lower := (rows 289 7 100 73 152 48 64 128 256), losses := [] }

theorem u6375 : Upper (D 8) (R 8) [288,5,96,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6375 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6376 : Route 9 := (fun mask => (mask,id))

def c6376 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6376 : Upper (D 8) (R 8) [288,5,96,65,136,128] 13 := by
  apply FastRouting.sound _ _ [288,5,96,65,136,128] 13 (by decide) (choices 1) [2,16,32] r6376 c6376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u813
  · exact u814
  · exact u815

def b6377 : PairBound 9 := { available := 152, camps := [], pairs := [], upper := (rows 289 7 100 73 176 34 216 152 408), lower := (rows 289 7 100 73 176 34 64 128 256), losses := [] }

theorem u6377 : Upper (D 8) (R 8) [288,5,96,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6377 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6378 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 289 7 100 73 176 40 210 146 402), lower := (rows 289 7 100 73 176 40 64 128 256), losses := [] }

theorem u6378 : Upper (D 8) (R 8) [288,5,96,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6378 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6379 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 289 7 100 73 176 48 202 138 394), lower := (rows 289 7 100 73 176 48 64 128 256), losses := [] }

theorem u6379 : Upper (D 8) (R 8) [288,5,96,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6379 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6380 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 73 176 160 90 154 282), lower := (rows 289 7 100 73 176 160 64 128 256), losses := [] }

theorem u6380 : Upper (D 8) (R 8) [288,5,96,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6381 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 289 7 100 88 145 34 232 168 424), lower := (rows 289 7 100 88 145 34 64 128 256), losses := [] }

theorem u6381 : Upper (D 8) (R 8) [288,5,96,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6381 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6382 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 7 100 88 145 40 226 162 418), lower := (rows 289 7 100 88 145 40 64 128 256), losses := [] }

theorem u6382 : Upper (D 8) (R 8) [288,5,96,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6382 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6383 : PairBound 9 := { available := 42, camps := [], pairs := [(2,0)], upper := (rows 289 7 100 88 145 160 106 170 298), lower := (rows 289 7 100 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 288 6 100 124 176 160 64 160 256) }] }

theorem u6383 : Upper (D 8) (R 8) [288,5,96,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6384 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 88 176 33 202 138 394), lower := (rows 289 7 100 88 176 33 64 128 256), losses := [] }

theorem u6384 : Upper (D 8) (R 8) [288,5,96,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6385 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 7 100 88 176 34 201 137 393), lower := (rows 289 7 100 88 176 34 64 128 256), losses := [] }

theorem u6385 : Upper (D 8) (R 8) [288,5,96,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6385 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6386 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 7 100 88 176 40 195 131 387), lower := (rows 289 7 100 88 176 40 64 128 256), losses := [] }

theorem u6386 : Upper (D 8) (R 8) [288,5,96,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6386 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6387 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 88 176 160 75 139 267), lower := (rows 289 7 100 88 176 160 64 128 256), losses := [] }

theorem u6387 : Upper (D 8) (R 8) [288,5,96,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6388 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 289 7 100 137 146 40 112 240 368), lower := (rows 289 7 100 137 146 40 64 128 256), losses := [] }

theorem u6388 : Upper (D 8) (R 8) [288,5,96,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6388 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6389 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 289 7 100 137 146 48 104 232 360), lower := (rows 289 7 100 137 146 48 64 128 256), losses := [] }

theorem u6389 : Upper (D 8) (R 8) [288,5,96,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6389 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6390 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 137 146 96 120 184 312), lower := (rows 289 7 100 137 146 96 64 128 256), losses := [] }

theorem u6390 : Upper (D 8) (R 8) [288,5,96,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6391 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 289 7 100 137 176 34 88 216 344), lower := (rows 289 7 100 137 176 34 64 128 256), losses := [] }

theorem u6391 : Upper (D 8) (R 8) [288,5,96,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6391 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6392 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 289 7 100 137 176 40 82 210 338), lower := (rows 289 7 100 137 176 40 64 128 256), losses := [] }

theorem u6392 : Upper (D 8) (R 8) [288,5,96,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6392 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6393 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 289 7 100 137 176 48 74 202 330), lower := (rows 289 7 100 137 176 48 64 128 256), losses := [] }

theorem u6393 : Upper (D 8) (R 8) [288,5,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6393 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6394 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 137 176 96 90 154 282), lower := (rows 289 7 100 137 176 96 64 128 256), losses := [] }

theorem u6394 : Upper (D 8) (R 8) [288,5,96,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6395 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 289 7 100 137 208 34 120 184 312), lower := (rows 289 7 100 137 208 34 64 128 256), losses := [] }

theorem u6395 : Upper (D 8) (R 8) [288,5,96,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6395 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6396 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 289 7 100 137 208 40 114 178 306), lower := (rows 289 7 100 137 208 40 64 128 256), losses := [] }

theorem u6396 : Upper (D 8) (R 8) [288,5,96,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6396 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6397 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 289 7 100 137 208 48 106 170 298), lower := (rows 289 7 100 137 208 48 64 128 256), losses := [] }

theorem u6397 : Upper (D 8) (R 8) [288,5,96,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6397 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6398 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 138 176 33 88 216 344), lower := (rows 289 7 100 138 176 33 64 128 256), losses := [] }

theorem u6398 : Upper (D 8) (R 8) [288,5,96,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6399 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 7 100 138 176 40 81 209 337), lower := (rows 289 7 100 138 176 40 64 128 256), losses := [] }

theorem u6399 : Upper (D 8) (R 8) [288,5,96,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6399 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6400 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 289 7 100 138 176 48 73 201 329), lower := (rows 289 7 100 138 176 48 64 128 256), losses := [] }

theorem u6400 : Upper (D 8) (R 8) [288,5,96,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6400 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6401 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 138 176 96 89 153 281), lower := (rows 289 7 100 138 176 96 64 128 256), losses := [] }

theorem u6401 : Upper (D 8) (R 8) [288,5,96,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6402 : PairBound 9 := { available := 56, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 138 208 33 120 184 312), lower := (rows 289 7 100 138 208 33 64 128 256), losses := [] }

theorem u6402 : Upper (D 8) (R 8) [288,5,96,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6403 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 7 100 138 208 40 113 177 305), lower := (rows 289 7 100 138 208 40 64 128 256), losses := [] }

theorem u6403 : Upper (D 8) (R 8) [288,5,96,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6403 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6404 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 289 7 100 138 208 48 105 169 297), lower := (rows 289 7 100 138 208 48 64 128 256), losses := [] }

theorem u6404 : Upper (D 8) (R 8) [288,5,96,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6404 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6405 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 168 208 33 90 154 282), lower := (rows 289 7 100 168 208 33 64 128 256), losses := [] }

theorem u6405 : Upper (D 8) (R 8) [288,5,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6406 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 7 100 168 208 34 89 153 281), lower := (rows 289 7 100 168 208 34 64 128 256), losses := [] }

theorem u6406 : Upper (D 8) (R 8) [288,5,96,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6406 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6407 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 7 100 168 208 40 83 147 275), lower := (rows 289 7 100 168 208 40 64 128 256), losses := [] }

theorem u6407 : Upper (D 8) (R 8) [288,5,96,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6407 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6408 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 289 7 100 168 208 48 75 139 267), lower := (rows 289 7 100 168 208 48 64 128 256), losses := [] }

theorem u6408 : Upper (D 8) (R 8) [288,5,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6408 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6409 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 196 26 56 33 224 224 480), lower := (rows 289 7 196 26 56 33 64 128 256), losses := [] }

theorem u6409 : Upper (D 8) (R 8) [288,5,192,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6410 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 26 56 96 225 161 417), lower := (rows 289 7 196 26 56 96 64 128 256), losses := [] }

theorem u6410 : Upper (D 8) (R 8) [288,5,192,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6411 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 289 7 196 42 81 40 240 176 432), lower := (rows 289 7 196 42 81 40 64 128 256), losses := [] }

theorem u6411 : Upper (D 8) (R 8) [288,5,192,34,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6411 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6412 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 289 7 196 42 81 48 232 168 424), lower := (rows 289 7 196 42 81 48 64 128 256), losses := [] }

theorem u6412 : Upper (D 8) (R 8) [288,5,192,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6412 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6413 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 196 42 81 160 120 184 312), lower := (rows 289 7 196 42 81 160 64 128 256), losses := [] }

theorem u6413 : Upper (D 8) (R 8) [288,5,192,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6414 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 196 42 112 33 216 152 408), lower := (rows 289 7 196 42 112 33 64 128 256), losses := [] }

theorem u6414 : Upper (D 8) (R 8) [288,5,192,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6415 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 7 196 42 112 40 209 145 401), lower := (rows 289 7 196 42 112 40 64 128 256), losses := [] }

theorem u6415 : Upper (D 8) (R 8) [288,5,192,34,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6415 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6416 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 7 196 42 112 48 201 137 393), lower := (rows 289 7 196 42 112 48 64 128 256), losses := [] }

theorem u6416 : Upper (D 8) (R 8) [288,5,192,34,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6416 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6417 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 196 42 112 160 89 153 281), lower := (rows 289 7 196 42 112 160 64 128 256), losses := [] }

theorem u6417 : Upper (D 8) (R 8) [288,5,192,34,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6418 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 289 7 196 56 81 34 232 168 424), lower := (rows 289 7 196 56 81 34 64 128 256), losses := [] }

theorem u6418 : Upper (D 8) (R 8) [288,5,192,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6418 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6419 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 7 196 56 81 40 226 162 418), lower := (rows 289 7 196 56 81 40 64 128 256), losses := [] }

theorem u6419 : Upper (D 8) (R 8) [288,5,192,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6419 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6419
end Delivery.IrregularNine14.P08
