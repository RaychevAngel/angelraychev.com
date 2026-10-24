import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0007

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3360 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 131 100 140 304 40 113 177 305), lower := (rows 67 131 100 140 304 40 64 128 256), losses := [] }

theorem u3360 : Upper (D 8) (R 8) [66,129,96,132,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3360 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3361 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 131 100 140 304 48 105 169 297), lower := (rows 67 131 100 140 304 48 64 128 256), losses := [] }

theorem u3361 : Upper (D 8) (R 8) [66,129,96,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3361 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3362 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 152 276 33 104 168 296), lower := (rows 67 131 100 152 276 33 64 128 256), losses := [] }

theorem u3362 : Upper (D 8) (R 8) [66,129,96,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3363 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 100 152 276 40 97 161 289), lower := (rows 67 131 100 152 276 40 64 128 256), losses := [] }

theorem u3363 : Upper (D 8) (R 8) [66,129,96,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3363 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3364 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 152 304 33 108 172 300), lower := (rows 67 131 100 152 304 33 64 128 256), losses := [] }

theorem u3364 : Upper (D 8) (R 8) [66,129,96,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3365 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 131 100 152 304 36 105 169 297), lower := (rows 67 131 100 152 304 36 64 128 256), losses := [] }

theorem u3365 : Upper (D 8) (R 8) [66,129,96,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3365 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3366 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 100 152 304 40 101 165 293), lower := (rows 67 131 100 152 304 40 64 128 256), losses := [] }

theorem u3366 : Upper (D 8) (R 8) [66,129,96,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3366 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3367 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 168 276 33 120 184 312), lower := (rows 67 131 100 168 276 33 64 128 256), losses := [] }

theorem u3367 : Upper (D 8) (R 8) [66,129,96,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3368 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 131 100 168 276 40 113 177 305), lower := (rows 67 131 100 168 276 40 64 128 256), losses := [] }

theorem u3368 : Upper (D 8) (R 8) [66,129,96,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3368 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3369 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 131 100 168 276 48 105 169 297), lower := (rows 67 131 100 168 276 48 64 128 256), losses := [] }

theorem u3369 : Upper (D 8) (R 8) [66,129,96,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3369 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3370 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 168 280 33 116 180 308), lower := (rows 67 131 100 168 280 33 64 128 256), losses := [] }

theorem u3370 : Upper (D 8) (R 8) [66,129,96,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3371 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 131 100 168 280 36 113 177 305), lower := (rows 67 131 100 168 280 36 64 128 256), losses := [] }

theorem u3371 : Upper (D 8) (R 8) [66,129,96,160,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3371 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3372 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 100 168 280 48 101 165 293), lower := (rows 67 131 100 168 280 48 64 128 256), losses := [] }

theorem u3372 : Upper (D 8) (R 8) [66,129,96,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3372 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3373 : PairBound 9 := { available := 28, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 168 304 33 92 156 284), lower := (rows 67 131 100 168 304 33 64 128 256), losses := [] }

theorem u3373 : Upper (D 8) (R 8) [66,129,96,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3374 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 131 100 168 304 36 89 153 281), lower := (rows 67 131 100 168 304 36 64 128 256), losses := [] }

theorem u3374 : Upper (D 8) (R 8) [66,129,96,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3374 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3375 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 131 100 168 304 40 85 149 277), lower := (rows 67 131 100 168 304 40 64 128 256), losses := [] }

theorem u3375 : Upper (D 8) (R 8) [66,129,96,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3375 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3376 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 67 131 100 168 304 48 77 141 269), lower := (rows 67 131 100 168 304 48 64 128 256), losses := [] }

theorem u3376 : Upper (D 8) (R 8) [66,129,96,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3376 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3377 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 296 112 33 240 176 432), lower := (rows 67 134 13 296 112 33 64 128 256), losses := [] }

theorem u3377 : Upper (D 8) (R 8) [66,132,9,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3378 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 134 13 296 112 48 225 161 417), lower := (rows 67 134 13 296 112 48 64 128 256), losses := [] }

theorem u3378 : Upper (D 8) (R 8) [66,132,9,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3378 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3379 : PairBound 9 := { available := 49, camps := [], pairs := [(4,0)], upper := (rows 67 134 13 296 112 160 113 177 305), lower := (rows 67 134 13 296 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 162 64 128 256), good := (rows 114 166 28 296 112 160 64 160 256) }] }

theorem u3379 : Upper (D 8) (R 8) [66,132,9,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3380 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 296 176 33 112 240 368), lower := (rows 67 134 13 296 176 33 64 128 256), losses := [] }

theorem u3380 : Upper (D 8) (R 8) [66,132,9,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3381 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 134 13 296 176 48 97 225 353), lower := (rows 67 134 13 296 176 48 64 128 256), losses := [] }

theorem u3381 : Upper (D 8) (R 8) [66,132,9,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3381 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3382 : Route 9 := (fun mask => (mask,id))

def c3382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3382 : Upper (D 8) (R 8) [66,132,9,288,160,64] 13 := by
  apply FastRouting.sound _ _ [66,132,9,288,160,64] 13 (by decide) (choices 1) [1,16,32] r3382 c3382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u450
  · exact u451
  · exact u452

def b3383 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 296 208 33 112 176 304), lower := (rows 67 134 13 296 208 33 64 128 256), losses := [] }

theorem u3383 : Upper (D 8) (R 8) [66,132,9,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3384 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 13 296 208 48 97 161 289), lower := (rows 67 134 13 296 208 48 64 128 256), losses := [] }

theorem u3384 : Upper (D 8) (R 8) [66,132,9,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3384 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3385 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 28 41 304 33 224 224 480), lower := (rows 67 134 28 41 304 33 64 128 256), losses := [] }

theorem u3385 : Upper (D 8) (R 8) [66,132,24,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3386 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 28 41 304 96 225 161 417), lower := (rows 67 134 28 41 304 96 64 128 256), losses := [] }

theorem u3386 : Upper (D 8) (R 8) [66,132,24,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3387 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 28 41 304 160 97 225 353), lower := (rows 67 134 28 41 304 160 64 128 256), losses := [] }

theorem u3387 : Upper (D 8) (R 8) [66,132,24,33,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3388 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 56 208 33 360 424 296), lower := (rows 67 134 37 56 208 33 64 128 256), losses := [] }

theorem u3388 : Upper (D 8) (R 8) [66,132,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3389 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 134 37 56 208 40 353 417 289), lower := (rows 67 134 37 56 208 40 64 128 256), losses := [] }

theorem u3389 : Upper (D 8) (R 8) [66,132,33,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3389 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3390 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 134 37 56 208 288 105 169 297), lower := (rows 67 134 37 56 208 288 64 128 256), losses := [] }

theorem u3390 : Upper (D 8) (R 8) [66,132,33,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3390 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3391 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 56 280 33 224 224 480), lower := (rows 67 134 37 56 280 33 64 128 256), losses := [] }

theorem u3391 : Upper (D 8) (R 8) [66,132,33,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3392 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 56 280 96 225 161 417), lower := (rows 67 134 37 56 280 96 64 128 256), losses := [] }

theorem u3392 : Upper (D 8) (R 8) [66,132,33,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3393 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 37 56 280 160 97 225 353), lower := (rows 67 134 37 56 280 160 64 128 256), losses := [] }

theorem u3393 : Upper (D 8) (R 8) [66,132,33,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3394 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 56 336 33 232 168 424), lower := (rows 67 134 37 56 336 33 64 128 256), losses := [] }

theorem u3394 : Upper (D 8) (R 8) [66,132,33,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3395 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 134 37 56 336 40 225 161 417), lower := (rows 67 134 37 56 336 40 64 128 256), losses := [] }

theorem u3395 : Upper (D 8) (R 8) [66,132,33,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3395 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3396 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 37 56 336 160 105 169 297), lower := (rows 67 134 37 56 336 160 64 128 256), losses := [] }

theorem u3396 : Upper (D 8) (R 8) [66,132,33,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3397 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 56 400 33 104 232 360), lower := (rows 67 134 37 56 400 33 64 128 256), losses := [] }

theorem u3397 : Upper (D 8) (R 8) [66,132,33,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3398 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 134 37 56 400 40 97 225 353), lower := (rows 67 134 37 56 400 40 64 128 256), losses := [] }

theorem u3398 : Upper (D 8) (R 8) [66,132,33,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3398 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3399 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 56 400 96 105 169 297), lower := (rows 67 134 37 56 400 96 64 128 256), losses := [] }

theorem u3399 : Upper (D 8) (R 8) [66,132,33,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3400 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 88 176 33 360 424 296), lower := (rows 67 134 37 88 176 33 64 128 256), losses := [] }

theorem u3400 : Upper (D 8) (R 8) [66,132,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3401 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 134 37 88 176 40 353 417 289), lower := (rows 67 134 37 88 176 40 64 128 256), losses := [] }

theorem u3401 : Upper (D 8) (R 8) [66,132,33,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3401 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3402 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 134 37 88 176 288 105 169 297), lower := (rows 67 134 37 88 176 288 64 128 256), losses := [] }

theorem u3402 : Upper (D 8) (R 8) [66,132,33,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3402 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3403 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 88 304 33 232 168 424), lower := (rows 67 134 37 88 304 33 64 128 256), losses := [] }

theorem u3403 : Upper (D 8) (R 8) [66,132,33,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3404 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 134 37 88 304 40 225 161 417), lower := (rows 67 134 37 88 304 40 64 128 256), losses := [] }

theorem u3404 : Upper (D 8) (R 8) [66,132,33,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3404 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3405 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 37 88 304 160 105 169 297), lower := (rows 67 134 37 88 304 160 64 128 256), losses := [] }

theorem u3405 : Upper (D 8) (R 8) [66,132,33,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3406 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 88 400 33 104 168 296), lower := (rows 67 134 37 88 400 33 64 128 256), losses := [] }

theorem u3406 : Upper (D 8) (R 8) [66,132,33,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3407 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 37 88 400 40 97 161 289), lower := (rows 67 134 37 88 400 40 64 128 256), losses := [] }

theorem u3407 : Upper (D 8) (R 8) [66,132,33,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3407 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3408 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 104 152 33 368 432 304), lower := (rows 67 134 37 104 152 33 64 128 256), losses := [] }

theorem u3408 : Upper (D 8) (R 8) [66,132,33,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3409 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 134 37 104 152 48 353 417 289), lower := (rows 67 134 37 104 152 48 64 128 256), losses := [] }

theorem u3409 : Upper (D 8) (R 8) [66,132,33,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3409 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3410 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 134 37 104 152 288 113 177 305), lower := (rows 67 134 37 104 152 288 64 128 256), losses := [] }

theorem u3410 : Upper (D 8) (R 8) [66,132,33,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3410 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3411 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 104 176 33 344 408 280), lower := (rows 67 134 37 104 176 33 64 128 256), losses := [] }

theorem u3411 : Upper (D 8) (R 8) [66,132,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3412 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 67 134 37 104 176 40 337 401 273), lower := (rows 67 134 37 104 176 40 64 128 256), losses := [] }

theorem u3412 : Upper (D 8) (R 8) [66,132,33,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3412 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3413 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 67 134 37 104 176 48 329 393 265), lower := (rows 67 134 37 104 176 48 64 128 256), losses := [] }

theorem u3413 : Upper (D 8) (R 8) [66,132,33,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3413 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3414 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 134 37 104 176 288 89 153 281), lower := (rows 67 134 37 104 176 288 64 128 256), losses := [] }

theorem u3414 : Upper (D 8) (R 8) [66,132,33,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3414 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3415 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 104 280 33 240 176 432), lower := (rows 67 134 37 104 280 33 64 128 256), losses := [] }

theorem u3415 : Upper (D 8) (R 8) [66,132,33,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3416 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 134 37 104 280 48 225 161 417), lower := (rows 67 134 37 104 280 48 64 128 256), losses := [] }

theorem u3416 : Upper (D 8) (R 8) [66,132,33,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3416 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3417 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 37 104 280 160 113 177 305), lower := (rows 67 134 37 104 280 160 64 128 256), losses := [] }

theorem u3417 : Upper (D 8) (R 8) [66,132,33,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3418 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 104 304 33 216 152 408), lower := (rows 67 134 37 104 304 33 64 128 256), losses := [] }

theorem u3418 : Upper (D 8) (R 8) [66,132,33,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3419 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 134 37 104 304 40 209 145 401), lower := (rows 67 134 37 104 304 40 64 128 256), losses := [] }

theorem u3419 : Upper (D 8) (R 8) [66,132,33,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3419 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3419
end Delivery.IrregularNine14.P08
