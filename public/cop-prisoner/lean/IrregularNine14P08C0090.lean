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

def b5400 : PairBound 9 := { available := 152, camps := [], pairs := [], upper := (rows 193 7 292 41 112 34 216 152 408), lower := (rows 193 7 292 41 112 34 64 128 256), losses := [] }

theorem u5400 : Upper (D 8) (R 8) [192,5,288,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5400 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5401 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 193 7 292 41 112 40 210 146 402), lower := (rows 193 7 292 41 112 40 64 128 256), losses := [] }

theorem u5401 : Upper (D 8) (R 8) [192,5,288,33,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5401 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5402 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 193 7 292 41 112 48 202 138 394), lower := (rows 193 7 292 41 112 48 64 128 256), losses := [] }

theorem u5402 : Upper (D 8) (R 8) [192,5,288,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5402 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5403 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 342, targets := 128 }], pairs := [(1,7)], upper := (rows 193 7 292 41 112 160 90 154 282), lower := (rows 193 7 292 41 112 160 64 128 256), losses := [] }

theorem u5403 : Upper (D 8) (R 8) [192,5,288,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5404 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 292 42 88 33 240 176 432), lower := (rows 193 7 292 42 88 33 64 128 256), losses := [] }

theorem u5404 : Upper (D 8) (R 8) [192,5,288,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5405 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 292 42 88 48 225 161 417), lower := (rows 193 7 292 42 88 48 64 128 256), losses := [] }

theorem u5405 : Upper (D 8) (R 8) [192,5,288,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5405 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5406 : PairBound 9 := { available := 49, camps := [], pairs := [(3,0)], upper := (rows 193 7 292 42 88 160 113 177 305), lower := (rows 193 7 292 42 88 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 161 64 128 256), good := (rows 224 46 292 42 88 160 64 160 256) }] }

theorem u5406 : Upper (D 8) (R 8) [192,5,288,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5407 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 292 42 112 33 216 152 408), lower := (rows 193 7 292 42 112 33 64 128 256), losses := [] }

theorem u5407 : Upper (D 8) (R 8) [192,5,288,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5408 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 193 7 292 42 112 40 209 145 401), lower := (rows 193 7 292 42 112 40 64 128 256), losses := [] }

theorem u5408 : Upper (D 8) (R 8) [192,5,288,34,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5408 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5409 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 193 7 292 42 112 48 201 137 393), lower := (rows 193 7 292 42 112 48 64 128 256), losses := [] }

theorem u5409 : Upper (D 8) (R 8) [192,5,288,34,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5409 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5410 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 292 42 112 160 89 153 281), lower := (rows 193 7 292 42 112 160 64 128 256), losses := [] }

theorem u5410 : Upper (D 8) (R 8) [192,5,288,34,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5411 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 292 56 82 33 232 168 424), lower := (rows 193 7 292 56 82 33 64 128 256), losses := [] }

theorem u5411 : Upper (D 8) (R 8) [192,5,288,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5412 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 7 292 56 82 40 225 161 417), lower := (rows 193 7 292 56 82 40 64 128 256), losses := [] }

theorem u5412 : Upper (D 8) (R 8) [192,5,288,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5412 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5413 : Route 9 := (fun mask => (mask,id))

def c5413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5413 : Upper (D 8) (R 8) [192,5,288,48,66,128] 13 := by
  apply FastRouting.sound _ _ [192,5,288,48,66,128] 13 (by decide) (choices 1) [1,8,32] r5413 c5413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u701
  · exact u702
  · exact u703

def b5414 : PairBound 9 := { available := 48, camps := [], pairs := [(2,6)], upper := (rows 193 7 292 74 152 33 112 176 304), lower := (rows 193 7 292 74 152 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 24 35 0 136 264), good := (rows 161 39 292 446 412 33 0 128 256) }] }

theorem u5414 : Upper (D 8) (R 8) [192,5,288,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5415 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 7 292 74 152 48 97 161 289), lower := (rows 193 7 292 74 152 48 64 128 256), losses := [] }

theorem u5415 : Upper (D 8) (R 8) [192,5,288,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5415 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5416 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 292 74 176 33 120 184 312), lower := (rows 193 7 292 74 176 33 64 128 256), losses := [] }

theorem u5416 : Upper (D 8) (R 8) [192,5,288,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5417 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 7 292 74 176 40 113 177 305), lower := (rows 193 7 292 74 176 40 64 128 256), losses := [] }

theorem u5417 : Upper (D 8) (R 8) [192,5,288,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5417 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5418 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 7 292 74 176 48 105 169 297), lower := (rows 193 7 292 74 176 48 64 128 256), losses := [] }

theorem u5418 : Upper (D 8) (R 8) [192,5,288,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5418 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5419 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 292 88 176 33 106 170 298), lower := (rows 193 7 292 88 176 33 64 128 256), losses := [] }

theorem u5419 : Upper (D 8) (R 8) [192,5,288,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5420 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 7 292 88 176 34 105 169 297), lower := (rows 193 7 292 88 176 34 64 128 256), losses := [] }

theorem u5420 : Upper (D 8) (R 8) [192,5,288,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5420 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5421 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 7 292 88 176 40 99 163 291), lower := (rows 193 7 292 88 176 40 64 128 256), losses := [] }

theorem u5421 : Upper (D 8) (R 8) [192,5,288,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5421 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5422 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 292 104 176 33 90 154 282), lower := (rows 193 7 292 104 176 33 64 128 256), losses := [] }

theorem u5422 : Upper (D 8) (R 8) [192,5,288,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5423 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 193 7 292 104 176 34 89 153 281), lower := (rows 193 7 292 104 176 34 64 128 256), losses := [] }

theorem u5423 : Upper (D 8) (R 8) [192,5,288,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5423 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5424 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 193 7 292 104 176 40 83 147 275), lower := (rows 193 7 292 104 176 40 64 128 256), losses := [] }

theorem u5424 : Upper (D 8) (R 8) [192,5,288,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5424 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5425 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 22 41 273 96 224 160 416), lower := (rows 193 14 22 41 273 96 64 128 256), losses := [] }

theorem u5425 : Upper (D 8) (R 8) [192,12,18,33,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5426 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 22 41 304 33 224 224 480), lower := (rows 193 14 22 41 304 33 64 128 256), losses := [] }

theorem u5426 : Upper (D 8) (R 8) [192,12,18,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5427 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 22 41 304 96 225 161 417), lower := (rows 193 14 22 41 304 96 64 128 256), losses := [] }

theorem u5427 : Upper (D 8) (R 8) [192,12,18,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5428 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 193 14 37 56 273 34 224 224 480), lower := (rows 193 14 37 56 273 34 64 128 256), losses := [] }

theorem u5428 : Upper (D 8) (R 8) [192,12,33,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5428 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5429 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 56 273 96 226 162 418), lower := (rows 193 14 37 56 273 96 64 128 256), losses := [] }

theorem u5429 : Upper (D 8) (R 8) [192,12,33,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5430 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 56 274 33 224 224 480), lower := (rows 193 14 37 56 274 33 64 128 256), losses := [] }

theorem u5430 : Upper (D 8) (R 8) [192,12,33,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5431 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 56 274 96 225 161 417), lower := (rows 193 14 37 56 274 96 64 128 256), losses := [] }

theorem u5431 : Upper (D 8) (R 8) [192,12,33,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5432 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 56 336 33 226 162 418), lower := (rows 193 14 37 56 336 33 64 128 256), losses := [] }

theorem u5432 : Upper (D 8) (R 8) [192,12,33,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5433 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 37 56 336 34 225 161 417), lower := (rows 193 14 37 56 336 34 64 128 256), losses := [] }

theorem u5433 : Upper (D 8) (R 8) [192,12,33,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5433 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5434 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 56 336 160 99 163 291), lower := (rows 193 14 37 56 336 160 64 128 256), losses := [] }

theorem u5434 : Upper (D 8) (R 8) [192,12,33,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5435 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 88 176 33 354 418 290), lower := (rows 193 14 37 88 176 33 64 128 256), losses := [] }

theorem u5435 : Upper (D 8) (R 8) [192,12,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5436 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 193 14 37 88 176 34 353 417 289), lower := (rows 193 14 37 88 176 34 64 128 256), losses := [] }

theorem u5436 : Upper (D 8) (R 8) [192,12,33,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5436 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5437 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 14 37 88 176 288 99 163 291), lower := (rows 193 14 37 88 176 288 64 128 256), losses := [] }

theorem u5437 : Upper (D 8) (R 8) [192,12,33,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5437 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5438 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 193 14 37 88 273 34 224 160 416), lower := (rows 193 14 37 88 273 34 64 128 256), losses := [] }

theorem u5438 : Upper (D 8) (R 8) [192,12,33,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5438 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5439 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 88 273 160 98 162 290), lower := (rows 193 14 37 88 273 160 64 128 256), losses := [] }

theorem u5439 : Upper (D 8) (R 8) [192,12,33,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5440 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 88 304 33 226 162 418), lower := (rows 193 14 37 88 304 33 64 128 256), losses := [] }

theorem u5440 : Upper (D 8) (R 8) [192,12,33,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5441 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 37 88 304 34 225 161 417), lower := (rows 193 14 37 88 304 34 64 128 256), losses := [] }

theorem u5441 : Upper (D 8) (R 8) [192,12,33,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5441 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5442 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 88 304 160 99 163 291), lower := (rows 193 14 37 88 304 160 64 128 256), losses := [] }

theorem u5442 : Upper (D 8) (R 8) [192,12,33,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5443 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 88 400 33 98 162 290), lower := (rows 193 14 37 88 400 33 64 128 256), losses := [] }

theorem u5443 : Upper (D 8) (R 8) [192,12,33,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5444 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 37 88 400 34 97 161 289), lower := (rows 193 14 37 88 400 34 64 128 256), losses := [] }

theorem u5444 : Upper (D 8) (R 8) [192,12,33,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5444 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5445 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 146 33 368 432 304), lower := (rows 193 14 37 104 146 33 64 128 256), losses := [] }

theorem u5445 : Upper (D 8) (R 8) [192,12,33,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5446 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 193 14 37 104 146 48 353 417 289), lower := (rows 193 14 37 104 146 48 64 128 256), losses := [] }

theorem u5446 : Upper (D 8) (R 8) [192,12,33,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5446 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5447 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 14 37 104 146 288 113 177 305), lower := (rows 193 14 37 104 146 288 64 128 256), losses := [] }

theorem u5447 : Upper (D 8) (R 8) [192,12,33,96,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5447 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5448 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 176 33 338 402 274), lower := (rows 193 14 37 104 176 33 64 128 256), losses := [] }

theorem u5448 : Upper (D 8) (R 8) [192,12,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5449 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 193 14 37 104 176 34 337 401 273), lower := (rows 193 14 37 104 176 34 64 128 256), losses := [] }

theorem u5449 : Upper (D 8) (R 8) [192,12,33,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5449 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5450 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 193 14 37 104 176 48 323 387 259), lower := (rows 193 14 37 104 176 48 64 128 256), losses := [] }

theorem u5450 : Upper (D 8) (R 8) [192,12,33,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5450 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5451 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 193 14 37 104 176 288 83 147 275), lower := (rows 193 14 37 104 176 288 64 128 256), losses := [] }

theorem u5451 : Upper (D 8) (R 8) [192,12,33,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5451 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5452 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 193 14 37 104 273 34 240 176 432), lower := (rows 193 14 37 104 273 34 64 128 256), losses := [] }

theorem u5452 : Upper (D 8) (R 8) [192,12,33,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5452 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5453 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 193 14 37 104 273 48 226 162 418), lower := (rows 193 14 37 104 273 48 64 128 256), losses := [] }

theorem u5453 : Upper (D 8) (R 8) [192,12,33,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5453 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5454 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 273 160 114 178 306), lower := (rows 193 14 37 104 273 160 64 128 256), losses := [] }

theorem u5454 : Upper (D 8) (R 8) [192,12,33,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5455 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 274 33 240 176 432), lower := (rows 193 14 37 104 274 33 64 128 256), losses := [] }

theorem u5455 : Upper (D 8) (R 8) [192,12,33,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5456 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 37 104 274 48 225 161 417), lower := (rows 193 14 37 104 274 48 64 128 256), losses := [] }

theorem u5456 : Upper (D 8) (R 8) [192,12,33,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5456 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5457 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 274 160 113 177 305), lower := (rows 193 14 37 104 274 160 64 128 256), losses := [] }

theorem u5457 : Upper (D 8) (R 8) [192,12,33,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5458 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 304 33 210 146 402), lower := (rows 193 14 37 104 304 33 64 128 256), losses := [] }

theorem u5458 : Upper (D 8) (R 8) [192,12,33,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5459 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 193 14 37 104 304 34 209 145 401), lower := (rows 193 14 37 104 304 34 64 128 256), losses := [] }

theorem u5459 : Upper (D 8) (R 8) [192,12,33,96,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5459 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5459
end Delivery.IrregularNine14.P08
