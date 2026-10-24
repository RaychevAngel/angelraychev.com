import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0003

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3360 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 69 266 112 160 80 130 386), lower := (rows 13 35 69 266 112 160 80 128 256), losses := [] }

theorem u3360 : Upper (D 7) (R 7) [12,33,65,258,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3360 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3361 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 69 266 112 160 192 146 274), lower := (rows 13 35 69 266 112 160 192 128 256), losses := [] }

theorem u3361 : Upper (D 7) (R 7) [12,33,65,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3362 : Route 9 := (fun mask => (mask,id))

def c3362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3362 : Upper (D 7) (R 7) [12,33,65,258,130,128,16] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,130,128,16] 13 (by decide) (choices 1) [32,64] r3362 c3362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u210
  · exact u211

def b3363 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 68, targets := 2 },{ cop := 1, region := 68, targets := 128 }], pairs := [(2,1),(2,7),(3,0),(4,0)], upper := (rows 13 35 69 266 146 160 96 208 336), lower := (rows 13 35 69 266 146 160 96 128 256), losses := [] }

theorem u3363 : Upper (D 7) (R 7) [12,33,65,258,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3364 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 35 69 266 208 160 66 176 304), lower := (rows 13 35 69 266 208 160 66 128 256), losses := [] }

theorem u3364 : Upper (D 7) (R 7) [12,33,65,258,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3365 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 69 266 208 160 80 162 290), lower := (rows 13 35 69 266 208 160 80 128 256), losses := [] }

theorem u3365 : Upper (D 7) (R 7) [12,33,65,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3365 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3366 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 68, targets := 2 },{ cop := 1, region := 68, targets := 128 }], pairs := [(2,1),(2,7),(3,0),(4,0)], upper := (rows 13 35 69 266 208 160 96 146 274), lower := (rows 13 35 69 266 208 160 96 128 256), losses := [] }

theorem u3366 : Upper (D 7) (R 7) [12,33,65,258,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3367 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 0, region := 162, targets := 64 }], pairs := [(0,1),(1,6),(3,1),(4,1)], upper := (rows 13 35 70 88 273 160 66 160 416), lower := (rows 13 35 70 88 273 160 66 128 256), losses := [] }

theorem u3367 : Upper (D 7) (R 7) [12,33,66,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3368 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 0, region := 162, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 35 70 88 273 160 96 130 386), lower := (rows 13 35 70 88 273 160 96 128 256), losses := [] }

theorem u3368 : Upper (D 7) (R 7) [12,33,66,80,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3369 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 196, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,6),(2,0),(4,6),(4,7)], upper := (rows 13 35 70 88 273 160 192 162 290), lower := (rows 13 35 70 88 273 160 192 128 256), losses := [] }

theorem u3369 : Upper (D 7) (R 7) [12,33,66,80,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3370 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 35 70 88 274 160 65 160 416), lower := (rows 13 35 70 88 274 160 65 128 256), losses := [] }

theorem u3370 : Upper (D 7) (R 7) [12,33,66,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3371 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 0, region := 162, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 35 70 88 274 160 96 129 385), lower := (rows 13 35 70 88 274 160 96 128 256), losses := [] }

theorem u3371 : Upper (D 7) (R 7) [12,33,66,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3372 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,6),(2,0),(4,6),(4,7)], upper := (rows 13 35 70 88 274 160 192 161 289), lower := (rows 13 35 70 88 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 224 224 128 256), good := (rows 12 102 102 120 278 224 224 224 256) }] }

theorem u3372 : Upper (D 7) (R 7) [12,33,66,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3373 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 88 304 160 65 130 386), lower := (rows 13 35 70 88 304 160 65 128 256), losses := [] }

theorem u3373 : Upper (D 7) (R 7) [12,33,66,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3374 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 88 304 160 66 129 385), lower := (rows 13 35 70 88 304 160 66 128 256), losses := [] }

theorem u3374 : Upper (D 7) (R 7) [12,33,66,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3375 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 196, targets := 32 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,6),(2,5),(4,6),(4,7)], upper := (rows 13 35 70 88 304 160 192 131 259), lower := (rows 13 35 70 88 304 160 192 128 256), losses := [] }

theorem u3375 : Upper (D 7) (R 7) [12,33,66,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3376 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 440, targets := 1 }], pairs := [(1,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 70 88 400 160 65 162 290), lower := (rows 13 35 70 88 400 160 65 128 256), losses := [] }

theorem u3376 : Upper (D 7) (R 7) [12,33,66,80,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3377 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 13 35 70 88 400 160 66 161 289), lower := (rows 13 35 70 88 400 160 66 128 256), losses := [] }

theorem u3377 : Upper (D 7) (R 7) [12,33,66,80,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3378 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 0, region := 162, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 35 70 88 400 160 96 131 259), lower := (rows 13 35 70 88 400 160 96 128 256), losses := [] }

theorem u3378 : Upper (D 7) (R 7) [12,33,66,80,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3379 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 35 70 138 112 288 65 144 400), lower := (rows 13 35 70 138 112 288 65 128 256), losses := [] }

theorem u3379 : Upper (D 7) (R 7) [12,33,66,130,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3379 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3380 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7)], upper := (rows 13 35 70 138 112 288 80 129 385), lower := (rows 13 35 70 138 112 288 80 128 256), losses := [] }

theorem u3380 : Upper (D 7) (R 7) [12,33,66,130,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3380 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3381 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 13 35 70 138 112 288 192 145 273), lower := (rows 13 35 70 138 112 288 192 128 256), losses := [] }

theorem u3381 : Upper (D 7) (R 7) [12,33,66,130,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3381 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3382 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 35 70 138 208 288 65 176 304), lower := (rows 13 35 70 138 208 288 65 128 256), losses := [] }

theorem u3382 : Upper (D 7) (R 7) [12,33,66,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3382 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3383 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 13 35 70 138 208 288 80 161 289), lower := (rows 13 35 70 138 208 288 80 128 256), losses := [] }

theorem u3383 : Upper (D 7) (R 7) [12,33,66,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3383 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3384 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 13 35 70 138 208 288 96 145 273), lower := (rows 13 35 70 138 208 288 96 128 256), losses := [] }

theorem u3384 : Upper (D 7) (R 7) [12,33,66,130,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3384 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3385 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 84, targets := 128 },{ cop := 2, region := 440, targets := 1 }], pairs := [(2,7),(3,0),(4,7)], upper := (rows 13 35 70 152 112 288 65 130 386), lower := (rows 13 35 70 152 112 288 65 128 256), losses := [] }

theorem u3385 : Upper (D 7) (R 7) [12,33,66,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3385 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3386 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0)], upper := (rows 13 35 70 152 112 288 66 129 385), lower := (rows 13 35 70 152 112 288 66 128 256), losses := [] }

theorem u3386 : Upper (D 7) (R 7) [12,33,66,144,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3386 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3387 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 290, targets := 64 },{ cop := 0, region := 290, targets := 128 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,6),(1,7),(2,5)], upper := (rows 13 35 70 152 112 288 192 131 259), lower := (rows 13 35 70 152 112 288 192 128 256), losses := [] }

theorem u3387 : Upper (D 7) (R 7) [12,33,66,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3387 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3388 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 2, region := 440, targets := 1 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 70 152 336 160 65 162 290), lower := (rows 13 35 70 152 336 160 65 128 256), losses := [] }

theorem u3388 : Upper (D 7) (R 7) [12,33,66,144,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3389 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 13 35 70 152 336 160 66 161 289), lower := (rows 13 35 70 152 336 160 66 128 256), losses := [] }

theorem u3389 : Upper (D 7) (R 7) [12,33,66,144,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3390 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 128 }], pairs := [(0,5),(2,7),(3,5),(4,5)], upper := (rows 13 35 70 152 336 160 96 131 259), lower := (rows 13 35 70 152 336 160 96 128 256), losses := [] }

theorem u3390 : Upper (D 7) (R 7) [12,33,66,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3391 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 35 70 168 146 288 65 208 336), lower := (rows 13 35 70 168 146 288 65 128 256), losses := [] }

theorem u3391 : Upper (D 7) (R 7) [12,33,66,160,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3391 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3392 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 13 35 70 168 146 288 80 193 321), lower := (rows 13 35 70 168 146 288 80 128 256), losses := [] }

theorem u3392 : Upper (D 7) (R 7) [12,33,66,160,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3392 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3393 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 35 70 168 208 288 65 146 274), lower := (rows 13 35 70 168 208 288 65 128 256), losses := [] }

theorem u3393 : Upper (D 7) (R 7) [12,33,66,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3393 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3394 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 13 35 70 168 208 288 66 145 273), lower := (rows 13 35 70 168 208 288 66 128 256), losses := [] }

theorem u3394 : Upper (D 7) (R 7) [12,33,66,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3394 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3395 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 13 35 70 168 208 288 80 131 259), lower := (rows 13 35 70 168 208 288 80 128 256), losses := [] }

theorem u3395 : Upper (D 7) (R 7) [12,33,66,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3395 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3396 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 200 146 288 65 176 304), lower := (rows 13 35 70 200 146 288 65 128 256), losses := [] }

theorem u3396 : Upper (D 7) (R 7) [12,33,66,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3396 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3397 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 13 35 70 200 146 288 80 161 289), lower := (rows 13 35 70 200 146 288 80 128 256), losses := [] }

theorem u3397 : Upper (D 7) (R 7) [12,33,66,192,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3397 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3398 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 13 35 70 200 146 288 96 145 273), lower := (rows 13 35 70 200 146 288 96 128 256), losses := [] }

theorem u3398 : Upper (D 7) (R 7) [12,33,66,192,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3398 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3399 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 13 35 70 200 176 288 65 146 274), lower := (rows 13 35 70 200 176 288 65 128 256), losses := [] }

theorem u3399 : Upper (D 7) (R 7) [12,33,66,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3399 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3400 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 13 35 70 200 176 288 66 145 273), lower := (rows 13 35 70 200 176 288 66 128 256), losses := [] }

theorem u3400 : Upper (D 7) (R 7) [12,33,66,192,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3400 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3401 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 13 35 70 200 176 288 80 131 259), lower := (rows 13 35 70 200 176 288 80 128 256), losses := [] }

theorem u3401 : Upper (D 7) (R 7) [12,33,66,192,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3401 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3402 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 13 35 70 265 112 160 66 144 400), lower := (rows 13 35 70 265 112 160 66 128 256), losses := [] }

theorem u3402 : Upper (D 7) (R 7) [12,33,66,257,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3403 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 70 265 112 160 80 130 386), lower := (rows 13 35 70 265 112 160 80 128 256), losses := [] }

theorem u3403 : Upper (D 7) (R 7) [12,33,66,257,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3403 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3404 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 265 112 160 192 146 274), lower := (rows 13 35 70 265 112 160 192 128 256), losses := [] }

theorem u3404 : Upper (D 7) (R 7) [12,33,66,257,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3405 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 13 35 70 265 146 160 80 224 352), lower := (rows 13 35 70 265 146 160 80 128 256), losses := [] }

theorem u3405 : Upper (D 7) (R 7) [12,33,66,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3405 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3406 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 35 70 265 146 160 96 208 336), lower := (rows 13 35 70 265 146 160 96 128 256), losses := [] }

theorem u3406 : Upper (D 7) (R 7) [12,33,66,257,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3407 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 13 35 70 265 208 160 66 176 304), lower := (rows 13 35 70 265 208 160 66 128 256), losses := [] }

theorem u3407 : Upper (D 7) (R 7) [12,33,66,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3408 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 70 265 208 160 80 162 290), lower := (rows 13 35 70 265 208 160 80 128 256), losses := [] }

theorem u3408 : Upper (D 7) (R 7) [12,33,66,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3408 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3409 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 35 70 265 208 160 96 146 274), lower := (rows 13 35 70 265 208 160 96 128 256), losses := [] }

theorem u3409 : Upper (D 7) (R 7) [12,33,66,257,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3410 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 85, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 35 70 266 81 160 80 160 416), lower := (rows 13 35 70 266 81 160 80 128 256), losses := [] }

theorem u3410 : Upper (D 7) (R 7) [12,33,66,258,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3410 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3411 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 128 }], pairs := [(0,5),(2,7),(3,5),(4,5)], upper := (rows 13 35 70 266 81 160 96 144 400), lower := (rows 13 35 70 266 81 160 96 128 256), losses := [] }

theorem u3411 : Upper (D 7) (R 7) [12,33,66,258,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3412 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,6),(2,0),(3,6),(4,1)], upper := (rows 13 35 70 266 81 160 192 176 304), lower := (rows 13 35 70 266 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 240 240 144 272), good := (rows 12 102 102 270 496 224 224 224 256) }] }

theorem u3412 : Upper (D 7) (R 7) [12,33,66,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3413 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 35 70 266 112 160 65 144 400), lower := (rows 13 35 70 266 112 160 65 128 256), losses := [] }

theorem u3413 : Upper (D 7) (R 7) [12,33,66,258,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3414 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0)], upper := (rows 13 35 70 266 112 160 80 129 385), lower := (rows 13 35 70 266 112 160 80 128 256), losses := [] }

theorem u3414 : Upper (D 7) (R 7) [12,33,66,258,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3414 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3415 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 266 112 160 192 145 273), lower := (rows 13 35 70 266 112 160 192 128 256), losses := [] }

theorem u3415 : Upper (D 7) (R 7) [12,33,66,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3416 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 2, region := 424, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,1)], upper := (rows 13 35 70 266 145 160 80 224 352), lower := (rows 13 35 70 266 145 160 80 128 256), losses := [] }

theorem u3416 : Upper (D 7) (R 7) [12,33,66,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3416 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3417 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 35 70 266 145 160 96 208 336), lower := (rows 13 35 70 266 145 160 96 128 256), losses := [] }

theorem u3417 : Upper (D 7) (R 7) [12,33,66,258,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3418 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 35 70 266 208 160 65 176 304), lower := (rows 13 35 70 266 208 160 65 128 256), losses := [] }

theorem u3418 : Upper (D 7) (R 7) [12,33,66,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3419 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 70 266 208 160 80 161 289), lower := (rows 13 35 70 266 208 160 80 128 256), losses := [] }

theorem u3419 : Upper (D 7) (R 7) [12,33,66,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3419 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3419
end Delivery.IrregularNine14.P07
