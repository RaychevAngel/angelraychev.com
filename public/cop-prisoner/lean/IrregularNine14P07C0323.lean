import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0088

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19380 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 134 56 336 40 193 129 385), lower := (rows 35 70 134 56 336 40 64 128 256), losses := [] }

theorem u19380 : Upper (D 7) (R 7) [34,68,130,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19380 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19381 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 56 336 160 73 137 265), lower := (rows 35 70 134 56 336 160 64 128 256), losses := [] }

theorem u19381 : Upper (D 7) (R 7) [34,68,130,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19382 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 56 400 33 73 201 329), lower := (rows 35 70 134 56 400 33 64 128 256), losses := [] }

theorem u19382 : Upper (D 7) (R 7) [34,68,130,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19383 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 134 56 400 40 65 193 321), lower := (rows 35 70 134 56 400 40 64 128 256), losses := [] }

theorem u19383 : Upper (D 7) (R 7) [34,68,130,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19383 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19384 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 56 400 96 73 137 265), lower := (rows 35 70 134 56 400 96 64 128 256), losses := [] }

theorem u19384 : Upper (D 7) (R 7) [34,68,130,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19385 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 73 152 33 368 432 304), lower := (rows 35 70 134 73 152 33 64 128 256), losses := [] }

theorem u19385 : Upper (D 7) (R 7) [34,68,130,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19386 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 73 152 48 353 417 289), lower := (rows 35 70 134 73 152 48 64 128 256), losses := [] }

theorem u19386 : Upper (D 7) (R 7) [34,68,130,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19386 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19387 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 432, targets := 64 }], pairs := [(3,1),(4,1),(4,6)], upper := (rows 35 70 134 73 152 288 113 177 305), lower := (rows 35 70 134 73 152 288 64 128 256), losses := [] }

theorem u19387 : Upper (D 7) (R 7) [34,68,130,65,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19387 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19388 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 73 176 33 344 408 280), lower := (rows 35 70 134 73 176 33 64 128 256), losses := [] }

theorem u19388 : Upper (D 7) (R 7) [34,68,130,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19389 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 73 176 40 337 401 273), lower := (rows 35 70 134 73 176 40 64 128 256), losses := [] }

theorem u19389 : Upper (D 7) (R 7) [34,68,130,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19389 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19390 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 134 73 176 48 329 393 265), lower := (rows 35 70 134 73 176 48 64 128 256), losses := [] }

theorem u19390 : Upper (D 7) (R 7) [34,68,130,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19390 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19391 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 432, targets := 64 }], pairs := [(3,1),(4,1),(4,6)], upper := (rows 35 70 134 73 176 288 89 153 281), lower := (rows 35 70 134 73 176 288 64 128 256), losses := [] }

theorem u19391 : Upper (D 7) (R 7) [34,68,130,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19391 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19392 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 73 273 40 240 176 432), lower := (rows 35 70 134 73 273 40 64 128 256), losses := [] }

theorem u19392 : Upper (D 7) (R 7) [34,68,130,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19392 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19393 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 432, targets := 64 }], pairs := [(3,1),(4,1),(4,6)], upper := (rows 35 70 134 73 273 48 232 168 424), lower := (rows 35 70 134 73 273 48 64 128 256), losses := [] }

theorem u19393 : Upper (D 7) (R 7) [34,68,130,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19393 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19394 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 73 273 160 120 184 312), lower := (rows 35 70 134 73 273 160 64 128 256), losses := [] }

theorem u19394 : Upper (D 7) (R 7) [34,68,130,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19395 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 73 280 33 240 176 432), lower := (rows 35 70 134 73 280 33 64 128 256), losses := [] }

theorem u19395 : Upper (D 7) (R 7) [34,68,130,65,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19396 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 73 280 48 225 161 417), lower := (rows 35 70 134 73 280 48 64 128 256), losses := [] }

theorem u19396 : Upper (D 7) (R 7) [34,68,130,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19396 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19397 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 73 280 160 113 177 305), lower := (rows 35 70 134 73 280 160 64 128 256), losses := [] }

theorem u19397 : Upper (D 7) (R 7) [34,68,130,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19398 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 73 304 33 216 152 408), lower := (rows 35 70 134 73 304 33 64 128 256), losses := [] }

theorem u19398 : Upper (D 7) (R 7) [34,68,130,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19399 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 73 304 40 209 145 401), lower := (rows 35 70 134 73 304 40 64 128 256), losses := [] }

theorem u19399 : Upper (D 7) (R 7) [34,68,130,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19399 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19400 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 134 73 304 48 201 137 393), lower := (rows 35 70 134 73 304 48 64 128 256), losses := [] }

theorem u19400 : Upper (D 7) (R 7) [34,68,130,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19400 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19401 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 73 304 160 89 153 281), lower := (rows 35 70 134 73 304 160 64 128 256), losses := [] }

theorem u19401 : Upper (D 7) (R 7) [34,68,130,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19402 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 73 400 33 120 184 312), lower := (rows 35 70 134 73 400 33 64 128 256), losses := [] }

theorem u19402 : Upper (D 7) (R 7) [34,68,130,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19403 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 73 400 40 113 177 305), lower := (rows 35 70 134 73 400 40 64 128 256), losses := [] }

theorem u19403 : Upper (D 7) (R 7) [34,68,130,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19403 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19404 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 72, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 134 73 400 48 105 169 297), lower := (rows 35 70 134 73 400 48 64 128 256), losses := [] }

theorem u19404 : Upper (D 7) (R 7) [34,68,130,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19404 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19405 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 88 145 33 360 424 296), lower := (rows 35 70 134 88 145 33 64 128 256), losses := [] }

theorem u19405 : Upper (D 7) (R 7) [34,68,130,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19406 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 88 145 40 353 417 289), lower := (rows 35 70 134 88 145 40 64 128 256), losses := [] }

theorem u19406 : Upper (D 7) (R 7) [34,68,130,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19406 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19407 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 4, region := 360, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 134 88 145 288 105 169 297), lower := (rows 35 70 134 88 145 288 64 128 256), losses := [] }

theorem u19407 : Upper (D 7) (R 7) [34,68,130,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19407 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19408 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 88 176 33 329 393 265), lower := (rows 35 70 134 88 176 33 64 128 256), losses := [] }

theorem u19408 : Upper (D 7) (R 7) [34,68,130,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19409 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 134 88 176 40 321 385 257), lower := (rows 35 70 134 88 176 40 64 128 256), losses := [] }

theorem u19409 : Upper (D 7) (R 7) [34,68,130,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19409 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19410 : Route 9 := (fun mask => (mask,id))

def c19410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19410 : Upper (D 7) (R 7) [34,68,130,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,160,256] 13 (by decide) (choices 1) [1,8] r19410 c19410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5300
  · exact u5301

def b19411 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 88 273 33 232 168 424), lower := (rows 35 70 134 88 273 33 64 128 256), losses := [] }

theorem u19411 : Upper (D 7) (R 7) [34,68,130,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19412 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 88 273 40 225 161 417), lower := (rows 35 70 134 88 273 40 64 128 256), losses := [] }

theorem u19412 : Upper (D 7) (R 7) [34,68,130,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19412 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19413 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 88 273 160 105 169 297), lower := (rows 35 70 134 88 273 160 64 128 256), losses := [] }

theorem u19413 : Upper (D 7) (R 7) [34,68,130,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19414 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 88 304 33 201 137 393), lower := (rows 35 70 134 88 304 33 64 128 256), losses := [] }

theorem u19414 : Upper (D 7) (R 7) [34,68,130,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19415 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 134 88 304 40 193 129 385), lower := (rows 35 70 134 88 304 40 64 128 256), losses := [] }

theorem u19415 : Upper (D 7) (R 7) [34,68,130,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19415 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19416 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 88 304 160 73 137 265), lower := (rows 35 70 134 88 304 160 64 128 256), losses := [] }

theorem u19416 : Upper (D 7) (R 7) [34,68,130,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19417 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 88 400 33 105 169 297), lower := (rows 35 70 134 88 400 33 64 128 256), losses := [] }

theorem u19417 : Upper (D 7) (R 7) [34,68,130,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19418 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 134 88 400 40 97 161 289), lower := (rows 35 70 134 88 400 40 64 128 256), losses := [] }

theorem u19418 : Upper (D 7) (R 7) [34,68,130,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19418 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19419 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 104 145 33 344 408 280), lower := (rows 35 70 134 104 145 33 64 128 256), losses := [] }

theorem u19419 : Upper (D 7) (R 7) [34,68,130,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19420 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 134 104 145 40 337 401 273), lower := (rows 35 70 134 104 145 40 64 128 256), losses := [] }

theorem u19420 : Upper (D 7) (R 7) [34,68,130,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19420 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19421 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 70 134 104 145 48 329 393 265), lower := (rows 35 70 134 104 145 48 64 128 256), losses := [] }

theorem u19421 : Upper (D 7) (R 7) [34,68,130,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19421 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19422 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 4, region := 360, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 134 104 145 288 89 153 281), lower := (rows 35 70 134 104 145 288 64 128 256), losses := [] }

theorem u19422 : Upper (D 7) (R 7) [34,68,130,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19422 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19423 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 104 152 33 337 401 273), lower := (rows 35 70 134 104 152 33 64 128 256), losses := [] }

theorem u19423 : Upper (D 7) (R 7) [34,68,130,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19424 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 134 104 152 48 321 385 257), lower := (rows 35 70 134 104 152 48 64 128 256), losses := [] }

theorem u19424 : Upper (D 7) (R 7) [34,68,130,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19424 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19425 : Route 9 := (fun mask => (mask,id))

def c19425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19425 : Upper (D 7) (R 7) [34,68,130,96,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,136,256] 13 (by decide) (choices 1) [1,16] r19425 c19425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5302
  · exact u5303

def b19426 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 104 273 33 216 152 408), lower := (rows 35 70 134 104 273 33 64 128 256), losses := [] }

theorem u19426 : Upper (D 7) (R 7) [34,68,130,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19427 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 134 104 273 40 209 145 401), lower := (rows 35 70 134 104 273 40 64 128 256), losses := [] }

theorem u19427 : Upper (D 7) (R 7) [34,68,130,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19427 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19428 : Route 9 := (fun mask => (mask,id))

def c19428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19428 : Upper (D 7) (R 7) [34,68,130,96,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,257,16] 13 (by decide) (choices 1) [1,8,128] r19428 c19428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5304
  · exact u5305
  · exact u5306

def b19429 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 104 273 160 89 153 281), lower := (rows 35 70 134 104 273 160 64 128 256), losses := [] }

theorem u19429 : Upper (D 7) (R 7) [34,68,130,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19430 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 104 280 33 209 145 401), lower := (rows 35 70 134 104 280 33 64 128 256), losses := [] }

theorem u19430 : Upper (D 7) (R 7) [34,68,130,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19431 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 134 104 280 48 193 129 385), lower := (rows 35 70 134 104 280 48 64 128 256), losses := [] }

theorem u19431 : Upper (D 7) (R 7) [34,68,130,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19431 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19432 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 2 },{ cop := 0, region := 344, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 35 70 134 104 280 160 81 145 273), lower := (rows 35 70 134 104 280 160 64 128 256), losses := [] }

theorem u19432 : Upper (D 7) (R 7) [34,68,130,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19433 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 134 104 400 33 89 153 281), lower := (rows 35 70 134 104 400 33 64 128 256), losses := [] }

theorem u19433 : Upper (D 7) (R 7) [34,68,130,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19434 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 134 104 400 40 81 145 273), lower := (rows 35 70 134 104 400 40 64 128 256), losses := [] }

theorem u19434 : Upper (D 7) (R 7) [34,68,130,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19434 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19435 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 72, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 134 104 400 48 73 137 265), lower := (rows 35 70 134 104 400 48 64 128 256), losses := [] }

theorem u19435 : Upper (D 7) (R 7) [34,68,130,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19435 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19436 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 70 134 137 273 40 112 240 368), lower := (rows 35 70 134 137 273 40 64 128 256), losses := [] }

theorem u19436 : Upper (D 7) (R 7) [34,68,130,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19436 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19437 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 368, targets := 128 }], pairs := [(3,1),(4,1),(4,7)], upper := (rows 35 70 134 137 273 48 104 232 360), lower := (rows 35 70 134 137 273 48 64 128 256), losses := [] }

theorem u19437 : Upper (D 7) (R 7) [34,68,130,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19437 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19438 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 134 137 273 96 120 184 312), lower := (rows 35 70 134 137 273 96 64 128 256), losses := [] }

theorem u19438 : Upper (D 7) (R 7) [34,68,130,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19439 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 134 137 280 33 112 240 368), lower := (rows 35 70 134 137 280 33 64 128 256), losses := [] }

theorem u19439 : Upper (D 7) (R 7) [34,68,130,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19439
end Delivery.IrregularNine14.P07
