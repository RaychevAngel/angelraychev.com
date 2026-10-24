import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0003

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3180 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 134 76 21 96 96 385 257), lower := (rows 11 50 134 76 21 96 96 128 256), losses := [] }

theorem u3180 : Upper (D 6) (R 6) [10,48,130,68,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3181 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(3,1)], upper := (rows 11 50 134 76 21 96 320 161 289), lower := (rows 11 50 134 76 21 96 320 128 256), losses := [] }

theorem u3181 : Upper (D 6) (R 6) [10,48,130,68,5,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3181 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3182 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 50 134 76 273 36 65 224 352), lower := (rows 11 50 134 76 273 36 65 128 256), losses := [{ target := 0, region := (rows 0 18 5 72 16 125 64 200 328), good := (rows 430 50 166 492 310 36 492 128 256) }] }

theorem u3182 : Upper (D 6) (R 6) [10,48,130,68,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3183 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 50 134 76 273 36 96 193 321), lower := (rows 11 50 134 76 273 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 44 17 44 111 145 273), good := (rows 505 504 236 108 465 108 104 128 256) }] }

theorem u3183 : Upper (D 6) (R 6) [10,48,130,68,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3184 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 132, targets := 65 },{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(2,0),(2,6)], upper := (rows 11 50 134 76 273 96 65 164 292), lower := (rows 11 50 134 76 273 96 65 128 256), losses := [] }

theorem u3184 : Upper (D 6) (R 6) [10,48,130,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3185 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 76 273 96 68 161 289), lower := (rows 11 50 134 76 273 96 68 128 256), losses := [] }

theorem u3185 : Upper (D 6) (R 6) [10,48,130,68,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3186 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 134 76 273 96 96 133 261), lower := (rows 11 50 134 76 273 96 96 128 256), losses := [] }

theorem u3186 : Upper (D 6) (R 6) [10,48,130,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3187 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 50 134 76 276 33 65 224 352), lower := (rows 11 50 134 76 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 28 97 97 235 363), good := (rows 505 496 404 508 276 481 481 128 256) }] }

theorem u3187 : Upper (D 6) (R 6) [10,48,130,68,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3188 : Route 9 := (fun mask => (mask,id))

def c3188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3188 : Upper (D 6) (R 6) [10,48,130,68,260,1,32] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,260,1,32] 13 (by decide) (choices 1) [1,64] r3188 c3188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u222
  · exact u223

def b3189 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 50 134 76 276 96 65 161 289), lower := (rows 11 50 134 76 276 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 105 65 193 321), good := (rows 505 48 132 508 276 480 481 128 256) }] }

theorem u3189 : Upper (D 6) (R 6) [10,48,130,68,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3190 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 134 76 276 96 96 129 257), lower := (rows 11 50 134 76 276 96 96 128 256), losses := [] }

theorem u3190 : Upper (D 6) (R 6) [10,48,130,68,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3191 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 132, targets := 65 },{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(2,0),(2,6)], upper := (rows 11 50 134 76 336 33 65 164 292), lower := (rows 11 50 134 76 336 33 65 128 256), losses := [] }

theorem u3191 : Upper (D 6) (R 6) [10,48,130,68,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3192 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 76 336 33 68 161 289), lower := (rows 11 50 134 76 336 33 68 128 256), losses := [] }

theorem u3192 : Upper (D 6) (R 6) [10,48,130,68,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3193 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(3,0)], upper := (rows 11 50 134 76 336 33 96 133 261), lower := (rows 11 50 134 76 336 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 98 128 256), good := (rows 74 114 206 76 336 96 96 128 256) }] }

theorem u3193 : Upper (D 6) (R 6) [10,48,130,68,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3194 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 0, region := 164, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 50 134 76 336 36 65 161 289), lower := (rows 11 50 134 76 336 36 65 128 256), losses := [] }

theorem u3194 : Upper (D 6) (R 6) [10,48,130,68,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3195 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 50 134 76 336 36 96 129 257), lower := (rows 11 50 134 76 336 36 96 128 256), losses := [] }

theorem u3195 : Upper (D 6) (R 6) [10,48,130,68,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3196 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 134 104 273 36 65 196 324), lower := (rows 11 50 134 104 273 36 65 128 256), losses := [] }

theorem u3196 : Upper (D 6) (R 6) [10,48,130,96,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3197 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 275, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 104 273 36 68 193 321), lower := (rows 11 50 134 104 273 36 68 128 256), losses := [] }

theorem u3197 : Upper (D 6) (R 6) [10,48,130,96,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3198 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 134 104 276 33 65 196 324), lower := (rows 11 50 134 104 276 33 65 128 256), losses := [] }

theorem u3198 : Upper (D 6) (R 6) [10,48,130,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3199 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 50 134 104 276 33 68 193 321), lower := (rows 11 50 134 104 276 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 84 128 256), good := (rows 10 122 206 104 340 32 68 128 256) }] }

theorem u3199 : Upper (D 6) (R 6) [10,48,130,96,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3200 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 50 134 265 81 36 68 224 352), lower := (rows 11 50 134 265 81 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 25 16 100 100 246 374), good := (rows 393 504 484 265 505 484 484 128 256) }] }

theorem u3200 : Upper (D 6) (R 6) [10,48,130,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3201 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 50 134 265 81 36 96 196 324), lower := (rows 11 50 134 265 81 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 36 102 164 292), good := (rows 89 496 484 281 81 484 480 128 256) }] }

theorem u3201 : Upper (D 6) (R 6) [10,48,130,257,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3202 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(3,1)], upper := (rows 11 50 134 268 21 96 65 224 352), lower := (rows 11 50 134 268 21 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 96 64 224 352), good := (rows 14 446 142 268 20 480 480 128 256) }] }

theorem u3202 : Upper (D 6) (R 6) [10,48,130,260,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3203 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 98, targets := 1 },{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,1)], upper := (rows 11 50 134 268 21 96 96 193 321), lower := (rows 11 50 134 268 21 96 96 128 256), losses := [] }

theorem u3203 : Upper (D 6) (R 6) [10,48,130,260,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3204 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 50 134 268 81 36 65 224 352), lower := (rows 11 50 134 268 81 36 65 128 256), losses := [] }

theorem u3204 : Upper (D 6) (R 6) [10,48,130,260,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3205 : PairBound 9 := { available := 65, camps := [], pairs := [(0,5),(4,1),(4,2)], upper := (rows 11 50 134 268 81 36 96 193 321), lower := (rows 11 50 134 268 81 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 111 145 273), good := (rows 505 496 228 364 465 100 96 128 256) },{ target := 2, region := (rows 1 2 0 8 17 32 98 145 273), good := (rows 475 498 194 264 465 96 96 128 256) },{ target := 5, region := (rows 7 2 6 10 16 0 64 144 272), good := (rows 15 415 143 269 465 5 64 128 256) }] }

theorem u3205 : Upper (D 6) (R 6) [10,48,130,260,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3206 : PairBound 9 := { available := 96, camps := [], pairs := [(1,2),(1,6),(3,1)], upper := (rows 11 50 134 268 84 33 65 224 352), lower := (rows 11 50 134 268 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 16 97 97 243 371), good := (rows 489 504 396 268 508 481 481 128 256) },{ target := 2, region := (rows 1 18 0 8 16 97 97 243 371), good := (rows 491 498 386 264 498 481 481 128 256) },{ target := 6, region := (rows 1 18 4 8 16 97 0 128 256), good := (rows 43 50 134 268 54 33 33 128 256) }] }

theorem u3206 : Upper (D 6) (R 6) [10,48,130,260,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3207 : PairBound 9 := { available := 65, camps := [], pairs := [(0,5),(4,0),(4,1)], upper := (rows 11 50 134 268 84 33 96 193 321), lower := (rows 11 50 134 268 84 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 98 128 256), good := (rows 74 114 214 284 84 96 96 128 256) },{ target := 1, region := (rows 1 0 4 8 20 33 99 161 289), good := (rows 489 496 212 284 84 481 480 128 256) },{ target := 5, region := (rows 7 2 6 26 16 0 64 144 272), good := (rows 15 415 143 269 477 1 64 128 256) }] }

theorem u3207 : Upper (D 6) (R 6) [10,48,130,260,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3208 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 296 81 36 65 196 324), lower := (rows 11 50 134 296 81 36 65 128 256), losses := [] }

theorem u3208 : Upper (D 6) (R 6) [10,48,130,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3209 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 50 134 296 81 36 68 193 321), lower := (rows 11 50 134 296 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 100 128 256), good := (rows 10 114 230 360 114 100 100 128 256) }] }

theorem u3209 : Upper (D 6) (R 6) [10,48,130,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3210 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 134 296 84 33 65 196 324), lower := (rows 11 50 134 296 84 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 32 64 144 272), good := (rows 14 446 142 296 468 32 64 128 256) }] }

theorem u3210 : Upper (D 6) (R 6) [10,48,130,288,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3211 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 134 296 84 33 68 193 321), lower := (rows 11 50 134 296 84 33 68 128 256), losses := [] }

theorem u3211 : Upper (D 6) (R 6) [10,48,130,288,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3212 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 132, targets := 65 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,0),(2,6),(3,1)], upper := (rows 11 50 134 328 21 96 65 164 292), lower := (rows 11 50 134 328 21 96 65 128 256), losses := [] }

theorem u3212 : Upper (D 6) (R 6) [10,48,130,320,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3213 : Route 9 := (fun mask => (mask,id))

def c3213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3213 : Upper (D 6) (R 6) [10,48,130,320,5,64,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,320,5,64,4] 13 (by decide) (choices 1) [1,32] r3213 c3213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u224
  · exact u225

def b3214 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 148, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 134 328 21 96 96 133 261), lower := (rows 11 50 134 328 21 96 96 128 256), losses := [] }

theorem u3214 : Upper (D 6) (R 6) [10,48,130,320,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3215 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 50 134 328 81 36 65 164 292), lower := (rows 11 50 134 328 81 36 65 128 256), losses := [] }

theorem u3215 : Upper (D 6) (R 6) [10,48,130,320,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3216 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 11 50 134 328 81 36 68 161 289), lower := (rows 11 50 134 328 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 100 128 256), good := (rows 10 114 230 360 114 100 100 128 256) }] }

theorem u3216 : Upper (D 6) (R 6) [10,48,130,320,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3217 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 0, region := 132, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 11 50 134 328 81 36 96 133 261), lower := (rows 11 50 134 328 81 36 96 128 256), losses := [] }

theorem u3217 : Upper (D 6) (R 6) [10,48,130,320,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3218 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 50 134 328 84 33 65 164 292), lower := (rows 11 50 134 328 84 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 80 32 64 162 290), good := (rows 398 438 390 344 84 420 84 128 256) }] }

theorem u3218 : Upper (D 6) (R 6) [10,48,130,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3219 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 134 328 84 33 68 161 289), lower := (rows 11 50 134 328 84 33 68 128 256), losses := [] }

theorem u3219 : Upper (D 6) (R 6) [10,48,130,320,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3220 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(4,0)], upper := (rows 11 50 134 328 84 33 96 133 261), lower := (rows 11 50 134 328 84 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 98 128 256), good := (rows 74 114 214 328 84 96 96 128 256) }] }

theorem u3220 : Upper (D 6) (R 6) [10,48,130,320,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3221 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 164 13 84 288 65 194 322), lower := (rows 11 50 164 13 84 288 65 128 256), losses := [] }

theorem u3221 : Upper (D 6) (R 6) [10,48,160,5,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3221 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3222 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 50 164 13 84 288 66 193 321), lower := (rows 11 50 164 13 84 288 66 128 256), losses := [] }

theorem u3222 : Upper (D 6) (R 6) [10,48,160,5,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3222 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3223 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 164 13 273 96 66 196 324), lower := (rows 11 50 164 13 273 96 66 128 256), losses := [] }

theorem u3223 : Upper (D 6) (R 6) [10,48,160,5,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3224 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 164 13 273 96 68 194 322), lower := (rows 11 50 164 13 273 96 68 128 256), losses := [] }

theorem u3224 : Upper (D 6) (R 6) [10,48,160,5,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3225 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 164 13 276 96 65 194 322), lower := (rows 11 50 164 13 276 96 65 128 256), losses := [] }

theorem u3225 : Upper (D 6) (R 6) [10,48,160,5,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3226 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(4,5)], upper := (rows 11 50 164 13 276 96 66 193 321), lower := (rows 11 50 164 13 276 96 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 67 137 265), good := (rows 475 82 132 477 276 64 66 128 256) }] }

theorem u3226 : Upper (D 6) (R 6) [10,48,160,5,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3227 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 50 164 73 84 288 65 134 262), lower := (rows 11 50 164 73 84 288 65 128 256), losses := [] }

theorem u3227 : Upper (D 6) (R 6) [10,48,160,65,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3227 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3228 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 50 164 73 84 288 66 133 261), lower := (rows 11 50 164 73 84 288 66 128 256), losses := [] }

theorem u3228 : Upper (D 6) (R 6) [10,48,160,65,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3228 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3229 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 50 164 73 84 288 68 131 259), lower := (rows 11 50 164 73 84 288 68 128 256), losses := [] }

theorem u3229 : Upper (D 6) (R 6) [10,48,160,65,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3229 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3230 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 50 164 73 274 96 65 132 260), lower := (rows 11 50 164 73 274 96 65 128 256), losses := [] }

theorem u3230 : Upper (D 6) (R 6) [10,48,160,65,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3231 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 164 73 274 96 68 133 261), lower := (rows 11 50 164 73 274 96 68 128 256), losses := [] }

theorem u3231 : Upper (D 6) (R 6) [10,48,160,65,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3232 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 50 164 73 276 96 65 134 262), lower := (rows 11 50 164 73 276 96 65 128 256), losses := [] }

theorem u3232 : Upper (D 6) (R 6) [10,48,160,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3233 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 164 73 276 96 66 133 261), lower := (rows 11 50 164 73 276 96 66 128 256), losses := [] }

theorem u3233 : Upper (D 6) (R 6) [10,48,160,65,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3234 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 164 73 276 96 68 131 259), lower := (rows 11 50 164 73 276 96 68 128 256), losses := [] }

theorem u3234 : Upper (D 6) (R 6) [10,48,160,65,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3235 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 65 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(2,6)], upper := (rows 11 50 164 76 273 96 65 134 262), lower := (rows 11 50 164 76 273 96 65 128 256), losses := [] }

theorem u3235 : Upper (D 6) (R 6) [10,48,160,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3236 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 11 50 164 76 273 96 66 133 261), lower := (rows 11 50 164 76 273 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 7 72 17 104 64 145 273), good := (rows 445 436 164 108 405 104 108 128 256) }] }

theorem u3236 : Upper (D 6) (R 6) [10,48,160,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3237 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 50 164 76 273 96 68 131 259), lower := (rows 11 50 164 76 273 96 68 128 256), losses := [] }

theorem u3237 : Upper (D 6) (R 6) [10,48,160,68,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3238 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 164 76 274 33 65 196 324), lower := (rows 11 50 164 76 274 33 65 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 17 32 64 136 264), good := (rows 410 50 166 460 274 50 80 128 256) }] }

theorem u3238 : Upper (D 6) (R 6) [10,48,160,68,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3239 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 50 164 76 274 33 68 193 321), lower := (rows 11 50 164 76 274 33 68 128 256), losses := [] }

theorem u3239 : Upper (D 6) (R 6) [10,48,160,68,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3239
end Delivery.IrregularNine14.P06
