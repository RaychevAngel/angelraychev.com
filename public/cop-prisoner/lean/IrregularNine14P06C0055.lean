import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0003
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3300 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 196 296 81 36 66 133 261), lower := (rows 11 50 196 296 81 36 66 128 256), losses := [] }

theorem u3300 : Upper (D 6) (R 6) [10,48,192,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3301 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 196 296 81 36 68 131 259), lower := (rows 11 50 196 296 81 36 68 128 256), losses := [] }

theorem u3301 : Upper (D 6) (R 6) [10,48,192,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3302 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 50 196 328 22 33 65 164 292), lower := (rows 11 50 196 328 22 33 65 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 20 97 0 132 260), good := (rows 43 50 438 296 406 33 33 128 256) }] }

theorem u3302 : Upper (D 6) (R 6) [10,48,192,320,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3303 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 50 196 328 22 33 68 161 289), lower := (rows 11 50 196 328 22 33 68 128 256), losses := [] }

theorem u3303 : Upper (D 6) (R 6) [10,48,192,320,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3304 : Route 9 := (fun mask => (mask,id))

def c3304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3304 : Upper (D 6) (R 6) [10,48,192,320,6,1,32] 13 := by
  apply FastRouting.sound _ _ [10,48,192,320,6,1,32] 13 (by decide) (choices 1) [1,4] r3304 c3304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u238
  · exact u239

def b3305 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 388 13 82 36 65 224 352), lower := (rows 11 50 388 13 82 36 65 128 256), losses := [] }

theorem u3305 : Upper (D 6) (R 6) [10,48,384,5,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3306 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 82, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 388 13 82 36 96 193 321), lower := (rows 11 50 388 13 82 36 96 128 256), losses := [] }

theorem u3306 : Upper (D 6) (R 6) [10,48,384,5,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3307 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 50 388 73 22 96 65 164 292), lower := (rows 11 50 388 73 22 96 65 128 256), losses := [] }

theorem u3307 : Upper (D 6) (R 6) [10,48,384,65,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3308 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 388 73 22 96 68 161 289), lower := (rows 11 50 388 73 22 96 68 128 256), losses := [] }

theorem u3308 : Upper (D 6) (R 6) [10,48,384,65,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3309 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 388 73 22 96 96 133 261), lower := (rows 11 50 388 73 22 96 96 128 256), losses := [] }

theorem u3309 : Upper (D 6) (R 6) [10,48,384,65,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3310 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 388, targets := 65 },{ cop := 4, region := 72, targets := 2 }], pairs := [(2,0),(2,6),(3,1)], upper := (rows 11 50 388 76 21 96 65 162 290), lower := (rows 11 50 388 76 21 96 65 128 256), losses := [] }

theorem u3310 : Upper (D 6) (R 6) [10,48,384,68,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3311 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 11 50 388 76 21 96 66 161 289), lower := (rows 11 50 388 76 21 96 66 128 256), losses := [] }

theorem u3311 : Upper (D 6) (R 6) [10,48,384,68,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3312 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 388 76 21 96 96 131 259), lower := (rows 11 50 388 76 21 96 96 128 256), losses := [] }

theorem u3312 : Upper (D 6) (R 6) [10,48,384,68,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3313 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 50 388 76 81 36 65 162 290), lower := (rows 11 50 388 76 81 36 65 128 256), losses := [] }

theorem u3313 : Upper (D 6) (R 6) [10,48,384,68,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3314 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 420, targets := 66 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 50 388 76 81 36 66 161 289), lower := (rows 11 50 388 76 81 36 66 128 256), losses := [] }

theorem u3314 : Upper (D 6) (R 6) [10,48,384,68,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3315 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 50 388 76 81 36 96 131 259), lower := (rows 11 50 388 76 81 36 96 128 256), losses := [] }

theorem u3315 : Upper (D 6) (R 6) [10,48,384,68,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 22 137 273 36 68 224 352), lower := (rows 11 98 22 137 273 36 68 128 256), losses := [] }

theorem u3316 : Upper (D 6) (R 6) [10,96,18,129,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3317 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 22 137 273 36 96 196 324), lower := (rows 11 98 22 137 273 36 96 128 256), losses := [] }

theorem u3317 : Upper (D 6) (R 6) [10,96,18,129,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3318 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 310, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 22 137 304 36 65 196 324), lower := (rows 11 98 22 137 304 36 65 128 256), losses := [] }

theorem u3318 : Upper (D 6) (R 6) [10,96,18,129,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3319 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 22 137 304 36 68 193 321), lower := (rows 11 98 22 137 304 36 68 128 256), losses := [] }

theorem u3319 : Upper (D 6) (R 6) [10,96,18,129,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3320 : PairBound 9 := { available := 96, camps := [], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 98 22 140 273 33 68 224 352), lower := (rows 11 98 22 140 273 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 76 130 258), good := (rows 458 482 478 204 272 32 76 128 256) },{ target := 1, region := (rows 1 0 4 76 49 49 76 135 263), good := (rows 505 504 508 460 433 433 460 128 256) }] }

theorem u3320 : Upper (D 6) (R 6) [10,96,18,132,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3321 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 22 140 273 33 96 196 324), lower := (rows 11 98 22 140 273 33 96 128 256), losses := [] }

theorem u3321 : Upper (D 6) (R 6) [10,96,18,132,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3322 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 22 140 304 33 65 196 324), lower := (rows 11 98 22 140 304 33 65 128 256), losses := [] }

theorem u3322 : Upper (D 6) (R 6) [10,96,18,132,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3323 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 4, region := 70, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 98 22 140 304 33 68 193 321), lower := (rows 11 98 22 140 304 33 68 128 256), losses := [] }

theorem u3323 : Upper (D 6) (R 6) [10,96,18,132,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3324 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 11 98 37 28 145 288 66 196 324), lower := (rows 11 98 37 28 145 288 66 128 256), losses := [] }

theorem u3324 : Upper (D 6) (R 6) [10,96,33,20,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3324 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3325 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 11 98 37 28 145 288 68 194 322), lower := (rows 11 98 37 28 145 288 68 128 256), losses := [] }

theorem u3325 : Upper (D 6) (R 6) [10,96,33,20,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3325 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3326 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 2, region := 66, targets := 4 }], pairs := [(1,2),(2,1)], upper := (rows 11 98 37 28 146 288 65 196 324), lower := (rows 11 98 37 28 146 288 65 128 256), losses := [] }

theorem u3326 : Upper (D 6) (R 6) [10,96,33,20,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3326 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3327 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1)], upper := (rows 11 98 37 28 146 288 68 193 321), lower := (rows 11 98 37 28 146 288 68 128 256), losses := [] }

theorem u3327 : Upper (D 6) (R 6) [10,96,33,20,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3327 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3328 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 292, targets := 64 },{ cop := 2, region := 66, targets := 4 }], pairs := [(1,2),(2,6)], upper := (rows 11 98 37 28 208 288 65 134 262), lower := (rows 11 98 37 28 208 288 65 128 256), losses := [] }

theorem u3328 : Upper (D 6) (R 6) [10,96,33,20,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3328 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3329 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 98 37 28 208 288 66 133 261), lower := (rows 11 98 37 28 208 288 66 128 256), losses := [] }

theorem u3329 : Upper (D 6) (R 6) [10,96,33,20,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3329 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3330 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 292, targets := 64 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,6)], upper := (rows 11 98 37 28 208 288 68 131 259), lower := (rows 11 98 37 28 208 288 68 128 256), losses := [] }

theorem u3330 : Upper (D 6) (R 6) [10,96,33,20,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3330 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3331 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 98 37 140 81 288 66 148 276), lower := (rows 11 98 37 140 81 288 66 128 256), losses := [] }

theorem u3331 : Upper (D 6) (R 6) [10,96,33,132,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3331 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3332 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 11 98 37 140 81 288 68 146 274), lower := (rows 11 98 37 140 81 288 68 128 256), losses := [] }

theorem u3332 : Upper (D 6) (R 6) [10,96,33,132,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3332 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3333 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 2 }], pairs := [(4,1)], upper := (rows 11 98 37 140 81 288 80 134 262), lower := (rows 11 98 37 140 81 288 80 128 256), losses := [] }

theorem u3333 : Upper (D 6) (R 6) [10,96,33,132,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3333 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3334 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 11 98 37 140 84 288 65 146 274), lower := (rows 11 98 37 140 84 288 65 128 256), losses := [] }

theorem u3334 : Upper (D 6) (R 6) [10,96,33,132,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3334 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3335 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 98 37 140 84 288 66 145 273), lower := (rows 11 98 37 140 84 288 66 128 256), losses := [] }

theorem u3335 : Upper (D 6) (R 6) [10,96,33,132,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3335 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3336 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6)], upper := (rows 11 98 37 140 84 288 80 131 259), lower := (rows 11 98 37 140 84 288 80 128 256), losses := [] }

theorem u3336 : Upper (D 6) (R 6) [10,96,33,132,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3336 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3337 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 11 98 37 152 84 288 65 134 262), lower := (rows 11 98 37 152 84 288 65 128 256), losses := [] }

theorem u3337 : Upper (D 6) (R 6) [10,96,33,144,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3337 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3338 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 98 37 152 84 288 66 133 261), lower := (rows 11 98 37 152 84 288 66 128 256), losses := [] }

theorem u3338 : Upper (D 6) (R 6) [10,96,33,144,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3338 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3339 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 98 37 152 84 288 68 131 259), lower := (rows 11 98 37 152 84 288 68 128 256), losses := [] }

theorem u3339 : Upper (D 6) (R 6) [10,96,33,144,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3339 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3340 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 },{ cop := 2, region := 66, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 98 37 152 274 36 65 196 324), lower := (rows 11 98 37 152 274 36 65 128 256), losses := [] }

theorem u3340 : Upper (D 6) (R 6) [10,96,33,144,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3341 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 409, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 152 274 36 68 193 321), lower := (rows 11 98 37 152 274 36 68 128 256), losses := [] }

theorem u3341 : Upper (D 6) (R 6) [10,96,33,144,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3342 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 },{ cop := 2, region := 66, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 98 37 152 336 36 65 134 262), lower := (rows 11 98 37 152 336 36 65 128 256), losses := [] }

theorem u3342 : Upper (D 6) (R 6) [10,96,33,144,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3343 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 152 336 36 66 133 261), lower := (rows 11 98 37 152 336 36 66 128 256), losses := [] }

theorem u3343 : Upper (D 6) (R 6) [10,96,33,144,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3344 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 409, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 152 336 36 68 131 259), lower := (rows 11 98 37 152 336 36 68 128 256), losses := [] }

theorem u3344 : Upper (D 6) (R 6) [10,96,33,144,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3345 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 98 37 392 81 36 66 148 276), lower := (rows 11 98 37 392 81 36 66 128 256), losses := [] }

theorem u3345 : Upper (D 6) (R 6) [10,96,33,384,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3346 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 409, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 392 81 36 68 146 274), lower := (rows 11 98 37 392 81 36 68 128 256), losses := [] }

theorem u3346 : Upper (D 6) (R 6) [10,96,33,384,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3347 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 37 392 81 36 80 134 262), lower := (rows 11 98 37 392 81 36 80 128 256), losses := [] }

theorem u3347 : Upper (D 6) (R 6) [10,96,33,384,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3347 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3348 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 52 13 146 288 65 196 324), lower := (rows 11 98 52 13 146 288 65 128 256), losses := [] }

theorem u3348 : Upper (D 6) (R 6) [10,96,48,5,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3348 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3349 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(4,5)], upper := (rows 11 98 52 13 146 288 68 193 321), lower := (rows 11 98 52 13 146 288 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 76 137 265), good := (rows 475 66 84 477 146 256 68 128 256) }] }

theorem u3349 : Upper (D 6) (R 6) [10,96,48,5,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3349 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3350 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 52 13 208 288 65 134 262), lower := (rows 11 98 52 13 208 288 65 128 256), losses := [] }

theorem u3350 : Upper (D 6) (R 6) [10,96,48,5,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3350 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3351 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 11 98 52 13 208 288 66 133 261), lower := (rows 11 98 52 13 208 288 66 128 256), losses := [] }

theorem u3351 : Upper (D 6) (R 6) [10,96,48,5,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3351 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3352 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(4,5)], upper := (rows 11 98 52 13 208 288 68 131 259), lower := (rows 11 98 52 13 208 288 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 25 0 76 129 257), good := (rows 475 66 84 477 208 256 68 128 256) }] }

theorem u3352 : Upper (D 6) (R 6) [10,96,48,5,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3352 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3353 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 310, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 52 137 276 34 65 196 324), lower := (rows 11 98 52 137 276 34 65 128 256), losses := [] }

theorem u3353 : Upper (D 6) (R 6) [10,96,48,129,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3354 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 52 137 276 34 68 193 321), lower := (rows 11 98 52 137 276 34 68 128 256), losses := [] }

theorem u3354 : Upper (D 6) (R 6) [10,96,48,129,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3355 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 98 52 140 81 288 65 134 262), lower := (rows 11 98 52 140 81 288 65 128 256), losses := [] }

theorem u3355 : Upper (D 6) (R 6) [10,96,48,132,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3355 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3356 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 98 52 140 81 288 66 133 261), lower := (rows 11 98 52 140 81 288 66 128 256), losses := [] }

theorem u3356 : Upper (D 6) (R 6) [10,96,48,132,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3356 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3357 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 1 },{ cop := 4, region := 290, targets := 4 }], pairs := [(1,0),(1,2)], upper := (rows 11 98 52 140 81 288 68 131 259), lower := (rows 11 98 52 140 81 288 68 128 256), losses := [] }

theorem u3357 : Upper (D 6) (R 6) [10,96,48,132,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3357 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3358 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 52 140 274 33 65 196 324), lower := (rows 11 98 52 140 274 33 65 128 256), losses := [] }

theorem u3358 : Upper (D 6) (R 6) [10,96,48,132,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3359 : Route 9 := (fun mask => (mask,id))

def c3359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3359 : Upper (D 6) (R 6) [10,96,48,132,258,1,4] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,258,1,4] 13 (by decide) (choices 1) [1,64] r3359 c3359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u240
  · exact u241

#print axioms u3359
end Delivery.IrregularNine14.P06
