import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0011

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5340 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 38 56 336 40 225 161 417), lower := (rows 193 7 38 56 336 40 64 128 256), losses := [] }

theorem u5340 : Upper (D 8) (R 8) [192,5,34,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5340 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5341 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 56 336 160 105 169 297), lower := (rows 193 7 38 56 336 160 64 128 256), losses := [] }

theorem u5341 : Upper (D 8) (R 8) [192,5,34,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5342 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 88 176 33 360 424 296), lower := (rows 193 7 38 88 176 33 64 128 256), losses := [] }

theorem u5342 : Upper (D 8) (R 8) [192,5,34,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5343 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 193 7 38 88 176 40 353 417 289), lower := (rows 193 7 38 88 176 40 64 128 256), losses := [] }

theorem u5343 : Upper (D 8) (R 8) [192,5,34,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5343 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5344 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 7 38 88 176 288 105 169 297), lower := (rows 193 7 38 88 176 288 64 128 256), losses := [] }

theorem u5344 : Upper (D 8) (R 8) [192,5,34,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5344 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5345 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 88 304 33 232 168 424), lower := (rows 193 7 38 88 304 33 64 128 256), losses := [] }

theorem u5345 : Upper (D 8) (R 8) [192,5,34,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5346 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 38 88 304 40 225 161 417), lower := (rows 193 7 38 88 304 40 64 128 256), losses := [] }

theorem u5346 : Upper (D 8) (R 8) [192,5,34,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5346 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5347 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 88 304 160 105 169 297), lower := (rows 193 7 38 88 304 160 64 128 256), losses := [] }

theorem u5347 : Upper (D 8) (R 8) [192,5,34,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5348 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 88 400 33 104 168 296), lower := (rows 193 7 38 88 400 33 64 128 256), losses := [] }

theorem u5348 : Upper (D 8) (R 8) [192,5,34,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5349 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 7 38 88 400 40 97 161 289), lower := (rows 193 7 38 88 400 40 64 128 256), losses := [] }

theorem u5349 : Upper (D 8) (R 8) [192,5,34,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5349 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5350 : PairBound 9 := { available := 280, camps := [{ cop := 5, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 104 176 33 344 408 280), lower := (rows 193 7 38 104 176 33 64 128 256), losses := [] }

theorem u5350 : Upper (D 8) (R 8) [192,5,34,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5351 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 193 7 38 104 176 40 337 401 273), lower := (rows 193 7 38 104 176 40 64 128 256), losses := [] }

theorem u5351 : Upper (D 8) (R 8) [192,5,34,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5351 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5352 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 193 7 38 104 176 288 89 153 281), lower := (rows 193 7 38 104 176 288 64 128 256), losses := [] }

theorem u5352 : Upper (D 8) (R 8) [192,5,34,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5352 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5353 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 104 280 33 240 176 432), lower := (rows 193 7 38 104 280 33 64 128 256), losses := [] }

theorem u5353 : Upper (D 8) (R 8) [192,5,34,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5354 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 38 104 280 48 225 161 417), lower := (rows 193 7 38 104 280 48 64 128 256), losses := [] }

theorem u5354 : Upper (D 8) (R 8) [192,5,34,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5354 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5355 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 104 280 160 113 177 305), lower := (rows 193 7 38 104 280 160 64 128 256), losses := [] }

theorem u5355 : Upper (D 8) (R 8) [192,5,34,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5356 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 104 304 33 216 152 408), lower := (rows 193 7 38 104 304 33 64 128 256), losses := [] }

theorem u5356 : Upper (D 8) (R 8) [192,5,34,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5357 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 193 7 38 104 304 40 209 145 401), lower := (rows 193 7 38 104 304 40 64 128 256), losses := [] }

theorem u5357 : Upper (D 8) (R 8) [192,5,34,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5357 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5358 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 193 7 38 104 304 48 201 137 393), lower := (rows 193 7 38 104 304 48 64 128 256), losses := [] }

theorem u5358 : Upper (D 8) (R 8) [192,5,34,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5358 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5359 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 104 304 160 89 153 281), lower := (rows 193 7 38 104 304 160 64 128 256), losses := [] }

theorem u5359 : Upper (D 8) (R 8) [192,5,34,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5360 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 104 400 33 120 184 312), lower := (rows 193 7 38 104 400 33 64 128 256), losses := [] }

theorem u5360 : Upper (D 8) (R 8) [192,5,34,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5361 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 7 38 104 400 40 113 177 305), lower := (rows 193 7 38 104 400 40 64 128 256), losses := [] }

theorem u5361 : Upper (D 8) (R 8) [192,5,34,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5361 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5362 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 7 38 104 400 48 105 169 297), lower := (rows 193 7 38 104 400 48 64 128 256), losses := [] }

theorem u5362 : Upper (D 8) (R 8) [192,5,34,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5362 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5363 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 26 304 33 224 224 480), lower := (rows 193 7 44 26 304 33 64 128 256), losses := [] }

theorem u5363 : Upper (D 8) (R 8) [192,5,40,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5364 : Route 9 := (fun mask => (mask,id))

def c5364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5364 : Upper (D 8) (R 8) [192,5,40,18,288,64] 13 := by
  apply FastRouting.sound _ _ [192,5,40,18,288,64] 13 (by decide) (choices 1) [1,32,128] r5364 c5364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u698
  · exact u699
  · exact u700

def b5365 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 193 7 44 266 49 48 224 224 480), lower := (rows 193 7 44 266 49 48 64 128 256), losses := [] }

theorem u5365 : Upper (D 8) (R 8) [192,5,40,258,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5365 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5366 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 266 49 96 240 176 432), lower := (rows 193 7 44 266 49 96 64 128 256), losses := [] }

theorem u5366 : Upper (D 8) (R 8) [192,5,40,258,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5367 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 193 7 44 266 112 33 240 176 432), lower := (rows 193 7 44 266 112 33 64 128 256), losses := [] }

theorem u5367 : Upper (D 8) (R 8) [192,5,40,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5368 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 44 266 112 48 225 161 417), lower := (rows 193 7 44 266 112 48 64 128 256), losses := [] }

theorem u5368 : Upper (D 8) (R 8) [192,5,40,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5368 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5369 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 266 112 160 113 177 305), lower := (rows 193 7 44 266 112 160 64 128 256), losses := [] }

theorem u5369 : Upper (D 8) (R 8) [192,5,40,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5370 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 193 7 44 280 49 34 224 224 480), lower := (rows 193 7 44 280 49 34 64 128 256), losses := [] }

theorem u5370 : Upper (D 8) (R 8) [192,5,40,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5370 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5371 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 280 49 96 226 162 418), lower := (rows 193 7 44 280 49 96 64 128 256), losses := [] }

theorem u5371 : Upper (D 8) (R 8) [192,5,40,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5372 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 280 50 33 224 224 480), lower := (rows 193 7 44 280 50 33 64 128 256), losses := [] }

theorem u5372 : Upper (D 8) (R 8) [192,5,40,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5373 : PairBound 9 := { available := 161, camps := [], pairs := [(4,0)], upper := (rows 193 7 44 280 50 96 225 161 417), lower := (rows 193 7 44 280 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 97 64 128 256), good := (rows 224 54 44 280 50 96 96 128 256) }] }

theorem u5373 : Upper (D 8) (R 8) [192,5,40,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5374 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 193 7 44 280 112 33 226 162 418), lower := (rows 193 7 44 280 112 33 64 128 256), losses := [] }

theorem u5374 : Upper (D 8) (R 8) [192,5,40,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5375 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 44 280 112 34 225 161 417), lower := (rows 193 7 44 280 112 34 64 128 256), losses := [] }

theorem u5375 : Upper (D 8) (R 8) [192,5,40,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5375 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5376 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 280 112 160 99 163 291), lower := (rows 193 7 44 280 112 160 64 128 256), losses := [] }

theorem u5376 : Upper (D 8) (R 8) [192,5,40,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5377 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 262 88 176 33 104 168 296), lower := (rows 193 7 262 88 176 33 64 128 256), losses := [] }

theorem u5377 : Upper (D 8) (R 8) [192,5,258,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5378 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 7 262 88 176 40 97 161 289), lower := (rows 193 7 262 88 176 40 64 128 256), losses := [] }

theorem u5378 : Upper (D 8) (R 8) [192,5,258,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5378 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5379 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 262 104 176 33 120 184 312), lower := (rows 193 7 262 104 176 33 64 128 256), losses := [] }

theorem u5379 : Upper (D 8) (R 8) [192,5,258,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5380 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 7 262 104 176 40 113 177 305), lower := (rows 193 7 262 104 176 40 64 128 256), losses := [] }

theorem u5380 : Upper (D 8) (R 8) [192,5,258,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5380 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5381 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 193 7 268 42 49 48 224 224 480), lower := (rows 193 7 268 42 49 48 64 128 256), losses := [] }

theorem u5381 : Upper (D 8) (R 8) [192,5,264,34,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5381 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5382 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 268 42 49 96 240 176 432), lower := (rows 193 7 268 42 49 96 64 128 256), losses := [] }

theorem u5382 : Upper (D 8) (R 8) [192,5,264,34,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5383 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 268 42 112 33 240 176 432), lower := (rows 193 7 268 42 112 33 64 128 256), losses := [] }

theorem u5383 : Upper (D 8) (R 8) [192,5,264,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5384 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 268 42 112 48 225 161 417), lower := (rows 193 7 268 42 112 48 64 128 256), losses := [] }

theorem u5384 : Upper (D 8) (R 8) [192,5,264,34,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5384 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5385 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 42 112 160 113 177 305), lower := (rows 193 7 268 42 112 160 64 128 256), losses := [] }

theorem u5385 : Upper (D 8) (R 8) [192,5,264,34,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5386 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 292 26 56 33 224 224 480), lower := (rows 193 7 292 26 56 33 64 128 256), losses := [] }

theorem u5386 : Upper (D 8) (R 8) [192,5,288,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5387 : PairBound 9 := { available := 161, camps := [], pairs := [(3,0)], upper := (rows 193 7 292 26 56 96 225 161 417), lower := (rows 193 7 292 26 56 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 97 64 128 256), good := (rows 224 62 292 26 56 96 96 128 256) }] }

theorem u5387 : Upper (D 8) (R 8) [192,5,288,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5388 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 193 7 292 26 112 33 232 168 424), lower := (rows 193 7 292 26 112 33 64 128 256), losses := [] }

theorem u5388 : Upper (D 8) (R 8) [192,5,288,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5389 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 292 26 112 40 225 161 417), lower := (rows 193 7 292 26 112 40 64 128 256), losses := [] }

theorem u5389 : Upper (D 8) (R 8) [192,5,288,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5389 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5390 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 292 26 112 160 105 169 297), lower := (rows 193 7 292 26 112 160 64 128 256), losses := [] }

theorem u5390 : Upper (D 8) (R 8) [192,5,288,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5391 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 193 7 292 41 50 40 208 208 464), lower := (rows 193 7 292 41 50 40 64 128 256), losses := [] }

theorem u5391 : Upper (D 8) (R 8) [192,5,288,33,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5391 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5392 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 193 7 292 41 50 48 200 200 456), lower := (rows 193 7 292 41 50 48 64 128 256), losses := [] }

theorem u5392 : Upper (D 8) (R 8) [192,5,288,33,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5392 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5393 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 41 50 96 216 152 408), lower := (rows 193 7 292 41 50 96 64 128 256), losses := [] }

theorem u5393 : Upper (D 8) (R 8) [192,5,288,33,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5394 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 193 7 292 41 82 40 240 176 432), lower := (rows 193 7 292 41 82 40 64 128 256), losses := [] }

theorem u5394 : Upper (D 8) (R 8) [192,5,288,33,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5394 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5395 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 193 7 292 41 82 48 232 168 424), lower := (rows 193 7 292 41 82 48 64 128 256), losses := [] }

theorem u5395 : Upper (D 8) (R 8) [192,5,288,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5395 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5396 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 342, targets := 128 }], pairs := [(1,7)], upper := (rows 193 7 292 41 82 160 120 184 312), lower := (rows 193 7 292 41 82 160 64 128 256), losses := [] }

theorem u5396 : Upper (D 8) (R 8) [192,5,288,33,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5397 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 193 7 292 41 88 34 240 176 432), lower := (rows 193 7 292 41 88 34 64 128 256), losses := [] }

theorem u5397 : Upper (D 8) (R 8) [192,5,288,33,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5397 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5398 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 193 7 292 41 88 48 226 162 418), lower := (rows 193 7 292 41 88 48 64 128 256), losses := [] }

theorem u5398 : Upper (D 8) (R 8) [192,5,288,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5398 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5399 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 342, targets := 128 }], pairs := [(1,7)], upper := (rows 193 7 292 41 88 160 114 178 306), lower := (rows 193 7 292 41 88 160 64 128 256), losses := [] }

theorem u5399 : Upper (D 8) (R 8) [192,5,288,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5399
end Delivery.IrregularNine14.P08
