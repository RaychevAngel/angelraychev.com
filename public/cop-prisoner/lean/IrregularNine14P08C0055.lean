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

def b3300 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 168 304 33 100 228 356), lower := (rows 67 131 28 168 304 33 64 128 256), losses := [] }

theorem u3300 : Upper (D 8) (R 8) [66,129,24,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3301 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 131 28 168 304 36 97 225 353), lower := (rows 67 131 28 168 304 36 64 128 256), losses := [] }

theorem u3301 : Upper (D 8) (R 8) [66,129,24,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3301 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3302 : PairBound 9 := { available := 37, camps := [], pairs := [(3,0)], upper := (rows 67 131 28 168 304 96 101 165 293), lower := (rows 67 131 28 168 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 97 64 128 256), good := (rows 106 170 28 168 304 96 96 128 256) }] }

theorem u3302 : Upper (D 8) (R 8) [66,129,24,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3303 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 168 336 33 100 164 292), lower := (rows 67 131 28 168 336 33 64 128 256), losses := [] }

theorem u3303 : Upper (D 8) (R 8) [66,129,24,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3304 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 28 168 336 36 97 161 289), lower := (rows 67 131 28 168 336 36 64 128 256), losses := [] }

theorem u3304 : Upper (D 8) (R 8) [66,129,24,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3304 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3305 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 88 176 33 356 420 292), lower := (rows 67 131 44 88 176 33 64 128 256), losses := [] }

theorem u3305 : Upper (D 8) (R 8) [66,129,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3306 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 131 44 88 176 36 353 417 289), lower := (rows 67 131 44 88 176 36 64 128 256), losses := [] }

theorem u3306 : Upper (D 8) (R 8) [66,129,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3306 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3307 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 44 88 176 288 101 165 293), lower := (rows 67 131 44 88 176 288 64 128 256), losses := [] }

theorem u3307 : Upper (D 8) (R 8) [66,129,40,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3307 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3308 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 88 304 33 228 164 420), lower := (rows 67 131 44 88 304 33 64 128 256), losses := [] }

theorem u3308 : Upper (D 8) (R 8) [66,129,40,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3309 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 131 44 88 304 36 225 161 417), lower := (rows 67 131 44 88 304 36 64 128 256), losses := [] }

theorem u3309 : Upper (D 8) (R 8) [66,129,40,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3309 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3310 : Route 9 := (fun mask => (mask,id))

def c3310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3310 : Upper (D 8) (R 8) [66,129,40,80,288,128] 13 := by
  apply FastRouting.sound _ _ [66,129,40,80,288,128] 13 (by decide) (choices 1) [1,4,32] r3310 c3310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u444
  · exact u445
  · exact u446

def b3311 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 88 400 33 100 164 292), lower := (rows 67 131 44 88 400 33 64 128 256), losses := [] }

theorem u3311 : Upper (D 8) (R 8) [66,129,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3312 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 44 88 400 36 97 161 289), lower := (rows 67 131 44 88 400 36 64 128 256), losses := [] }

theorem u3312 : Upper (D 8) (R 8) [66,129,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3312 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3313 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 152 112 33 356 420 292), lower := (rows 67 131 44 152 112 33 64 128 256), losses := [] }

theorem u3313 : Upper (D 8) (R 8) [66,129,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3314 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 131 44 152 112 36 353 417 289), lower := (rows 67 131 44 152 112 36 64 128 256), losses := [] }

theorem u3314 : Upper (D 8) (R 8) [66,129,40,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3314 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3315 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 44 152 112 288 101 165 293), lower := (rows 67 131 44 152 112 288 64 128 256), losses := [] }

theorem u3315 : Upper (D 8) (R 8) [66,129,40,144,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3315 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 152 304 33 100 228 356), lower := (rows 67 131 44 152 304 33 64 128 256), losses := [] }

theorem u3316 : Upper (D 8) (R 8) [66,129,40,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3317 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 131 44 152 304 36 97 225 353), lower := (rows 67 131 44 152 304 36 64 128 256), losses := [] }

theorem u3317 : Upper (D 8) (R 8) [66,129,40,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3317 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3318 : Route 9 := (fun mask => (mask,id))

def c3318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3318 : Upper (D 8) (R 8) [66,129,40,144,288,64] 13 := by
  apply FastRouting.sound _ _ [66,129,40,144,288,64] 13 (by decide) (choices 1) [1,4,32] r3318 c3318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u447
  · exact u448
  · exact u449

def b3319 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 152 336 33 100 164 292), lower := (rows 67 131 44 152 336 33 64 128 256), losses := [] }

theorem u3319 : Upper (D 8) (R 8) [66,129,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3320 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 44 152 336 36 97 161 289), lower := (rows 67 131 44 152 336 36 64 128 256), losses := [] }

theorem u3320 : Upper (D 8) (R 8) [66,129,40,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3320 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3321 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 268 112 33 240 176 432), lower := (rows 67 131 44 268 112 33 64 128 256), losses := [] }

theorem u3321 : Upper (D 8) (R 8) [66,129,40,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3322 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 131 44 268 112 48 225 161 417), lower := (rows 67 131 44 268 112 48 64 128 256), losses := [] }

theorem u3322 : Upper (D 8) (R 8) [66,129,40,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3322 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3323 : PairBound 9 := { available := 49, camps := [], pairs := [(4,0)], upper := (rows 67 131 44 268 112 160 113 177 305), lower := (rows 67 131 44 268 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 162 64 128 256), good := (rows 114 178 44 268 112 160 64 160 256) }] }

theorem u3323 : Upper (D 8) (R 8) [66,129,40,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3324 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 268 176 33 112 240 368), lower := (rows 67 131 44 268 176 33 64 128 256), losses := [] }

theorem u3324 : Upper (D 8) (R 8) [66,129,40,260,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3325 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 131 44 268 176 48 97 225 353), lower := (rows 67 131 44 268 176 48 64 128 256), losses := [] }

theorem u3325 : Upper (D 8) (R 8) [66,129,40,260,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3325 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3326 : PairBound 9 := { available := 49, camps := [], pairs := [(4,0)], upper := (rows 67 131 44 268 176 96 113 177 305), lower := (rows 67 131 44 268 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 97 64 128 256), good := (rows 114 178 44 268 176 96 96 128 256) }] }

theorem u3326 : Upper (D 8) (R 8) [66,129,40,260,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3327 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 280 112 33 228 164 420), lower := (rows 67 131 44 280 112 33 64 128 256), losses := [] }

theorem u3327 : Upper (D 8) (R 8) [66,129,40,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3328 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 131 44 280 112 36 225 161 417), lower := (rows 67 131 44 280 112 36 64 128 256), losses := [] }

theorem u3328 : Upper (D 8) (R 8) [66,129,40,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3328 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3329 : PairBound 9 := { available := 37, camps := [], pairs := [(4,0)], upper := (rows 67 131 44 280 112 160 101 165 293), lower := (rows 67 131 44 280 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 162 64 128 256), good := (rows 114 178 44 280 112 160 64 160 256) }] }

theorem u3329 : Upper (D 8) (R 8) [66,129,40,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3330 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 280 176 33 100 228 356), lower := (rows 67 131 44 280 176 33 64 128 256), losses := [] }

theorem u3330 : Upper (D 8) (R 8) [66,129,40,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3331 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 131 44 280 176 36 97 225 353), lower := (rows 67 131 44 280 176 36 64 128 256), losses := [] }

theorem u3331 : Upper (D 8) (R 8) [66,129,40,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3331 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3332 : PairBound 9 := { available := 37, camps := [], pairs := [(4,0)], upper := (rows 67 131 44 280 176 96 101 165 293), lower := (rows 67 131 44 280 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 97 64 128 256), good := (rows 114 178 44 280 176 96 96 128 256) }] }

theorem u3332 : Upper (D 8) (R 8) [66,129,40,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3333 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 328 148 33 112 176 304), lower := (rows 67 131 44 328 148 33 64 128 256), losses := [] }

theorem u3333 : Upper (D 8) (R 8) [66,129,40,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3334 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 44 328 148 48 97 161 289), lower := (rows 67 131 44 328 148 48 64 128 256), losses := [] }

theorem u3334 : Upper (D 8) (R 8) [66,129,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3334 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3335 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 328 176 33 116 180 308), lower := (rows 67 131 44 328 176 33 64 128 256), losses := [] }

theorem u3335 : Upper (D 8) (R 8) [66,129,40,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3336 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 131 44 328 176 36 113 177 305), lower := (rows 67 131 44 328 176 36 64 128 256), losses := [] }

theorem u3336 : Upper (D 8) (R 8) [66,129,40,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3336 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3337 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 44 328 176 48 101 165 293), lower := (rows 67 131 44 328 176 48 64 128 256), losses := [] }

theorem u3337 : Upper (D 8) (R 8) [66,129,40,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3337 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3338 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 392 84 33 112 176 304), lower := (rows 67 131 44 392 84 33 64 128 256), losses := [] }

theorem u3338 : Upper (D 8) (R 8) [66,129,40,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3339 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 44 392 84 48 97 161 289), lower := (rows 67 131 44 392 84 48 64 128 256), losses := [] }

theorem u3339 : Upper (D 8) (R 8) [66,129,40,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3339 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3340 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 392 112 33 116 180 308), lower := (rows 67 131 44 392 112 33 64 128 256), losses := [] }

theorem u3340 : Upper (D 8) (R 8) [66,129,40,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3341 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 131 44 392 112 36 113 177 305), lower := (rows 67 131 44 392 112 36 64 128 256), losses := [] }

theorem u3341 : Upper (D 8) (R 8) [66,129,40,384,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3341 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3342 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 44 392 112 48 101 165 293), lower := (rows 67 131 44 392 112 48 64 128 256), losses := [] }

theorem u3342 : Upper (D 8) (R 8) [66,129,40,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3342 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3343 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 152 304 33 100 164 292), lower := (rows 67 131 76 152 304 33 64 128 256), losses := [] }

theorem u3343 : Upper (D 8) (R 8) [66,129,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3344 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 76 152 304 36 97 161 289), lower := (rows 67 131 76 152 304 36 64 128 256), losses := [] }

theorem u3344 : Upper (D 8) (R 8) [66,129,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3344 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3345 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 168 276 33 112 176 304), lower := (rows 67 131 76 168 276 33 64 128 256), losses := [] }

theorem u3345 : Upper (D 8) (R 8) [66,129,72,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3346 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 76 168 276 48 97 161 289), lower := (rows 67 131 76 168 276 48 64 128 256), losses := [] }

theorem u3346 : Upper (D 8) (R 8) [66,129,72,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3346 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3347 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 168 304 33 116 180 308), lower := (rows 67 131 76 168 304 33 64 128 256), losses := [] }

theorem u3347 : Upper (D 8) (R 8) [66,129,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3348 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 131 76 168 304 36 113 177 305), lower := (rows 67 131 76 168 304 36 64 128 256), losses := [] }

theorem u3348 : Upper (D 8) (R 8) [66,129,72,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3348 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3349 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 76 168 304 48 101 165 293), lower := (rows 67 131 76 168 304 48 64 128 256), losses := [] }

theorem u3349 : Upper (D 8) (R 8) [66,129,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3349 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3350 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 280 176 33 100 164 292), lower := (rows 67 131 76 280 176 33 64 128 256), losses := [] }

theorem u3350 : Upper (D 8) (R 8) [66,129,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3351 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 76 280 176 36 97 161 289), lower := (rows 67 131 76 280 176 36 64 128 256), losses := [] }

theorem u3351 : Upper (D 8) (R 8) [66,129,72,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3351 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3352 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 296 148 33 112 176 304), lower := (rows 67 131 76 296 148 33 64 128 256), losses := [] }

theorem u3352 : Upper (D 8) (R 8) [66,129,72,288,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3353 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 76 296 148 48 97 161 289), lower := (rows 67 131 76 296 148 48 64 128 256), losses := [] }

theorem u3353 : Upper (D 8) (R 8) [66,129,72,288,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3353 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3354 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 76 296 176 33 116 180 308), lower := (rows 67 131 76 296 176 33 64 128 256), losses := [] }

theorem u3354 : Upper (D 8) (R 8) [66,129,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3355 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 131 76 296 176 36 113 177 305), lower := (rows 67 131 76 296 176 36 64 128 256), losses := [] }

theorem u3355 : Upper (D 8) (R 8) [66,129,72,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3355 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3356 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 76 296 176 48 101 165 293), lower := (rows 67 131 76 296 176 48 64 128 256), losses := [] }

theorem u3356 : Upper (D 8) (R 8) [66,129,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3356 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3357 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 140 280 33 112 176 304), lower := (rows 67 131 100 140 280 33 64 128 256), losses := [] }

theorem u3357 : Upper (D 8) (R 8) [66,129,96,132,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3358 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 100 140 280 48 97 161 289), lower := (rows 67 131 100 140 280 48 64 128 256), losses := [] }

theorem u3358 : Upper (D 8) (R 8) [66,129,96,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3358 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3359 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 100 140 304 33 120 184 312), lower := (rows 67 131 100 140 304 33 64 128 256), losses := [] }

theorem u3359 : Upper (D 8) (R 8) [66,129,96,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3359
end Delivery.IrregularNine14.P08
