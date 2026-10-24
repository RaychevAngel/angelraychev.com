import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008
import IrregularNine14P07C0009

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7320 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 6, region := 37, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 133 280 19 96 192 162 290), lower := (rows 37 74 133 280 19 96 192 128 256), losses := [] }

theorem u7320 : Upper (D 7) (R 7) [36,72,129,272,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7321 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 133 280 146 96 65 162 290), lower := (rows 37 74 133 280 146 96 65 128 256), losses := [] }

theorem u7321 : Upper (D 7) (R 7) [36,72,129,272,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7322 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 146 96 66 161 289), lower := (rows 37 74 133 280 146 96 66 128 256), losses := [] }

theorem u7322 : Upper (D 7) (R 7) [36,72,129,272,130,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7323 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 3, region := 98, targets := 129 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 37 74 133 280 146 96 96 131 259), lower := (rows 37 74 133 280 146 96 96 128 256), losses := [] }

theorem u7323 : Upper (D 7) (R 7) [36,72,129,272,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7324 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 133 280 208 34 65 162 290), lower := (rows 37 74 133 280 208 34 65 128 256), losses := [] }

theorem u7324 : Upper (D 7) (R 7) [36,72,129,272,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7325 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 208 34 66 161 289), lower := (rows 37 74 133 280 208 34 66 128 256), losses := [] }

theorem u7325 : Upper (D 7) (R 7) [36,72,129,272,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7326 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 98, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 74 133 280 208 34 96 131 259), lower := (rows 37 74 133 280 208 34 96 128 256), losses := [] }

theorem u7326 : Upper (D 7) (R 7) [36,72,129,272,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7327 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 133 296 81 34 66 144 400), lower := (rows 37 74 133 296 81 34 66 128 256), losses := [] }

theorem u7327 : Upper (D 7) (R 7) [36,72,129,288,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7328 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 74 133 296 81 34 80 130 386), lower := (rows 37 74 133 296 81 34 80 128 256), losses := [] }

theorem u7328 : Upper (D 7) (R 7) [36,72,129,288,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7328 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7329 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 34 },{ cop := 4, region := 298, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 37 74 133 296 81 34 192 146 274), lower := (rows 37 74 133 296 81 34 192 128 256), losses := [] }

theorem u7329 : Upper (D 7) (R 7) [36,72,129,288,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7330 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 133 296 146 34 65 208 336), lower := (rows 37 74 133 296 146 34 65 128 256), losses := [] }

theorem u7330 : Upper (D 7) (R 7) [36,72,129,288,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7331 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,6)], upper := (rows 37 74 133 296 146 34 80 193 321), lower := (rows 37 74 133 296 146 34 80 128 256), losses := [{ target := 1, region := (rows 41 0 38 40 16 32 80 130 258), good := (rows 45 461 133 301 468 429 80 128 256) }] }

theorem u7331 : Upper (D 7) (R 7) [36,72,129,288,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7331 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7332 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 37 74 133 296 146 96 65 146 274), lower := (rows 37 74 133 296 146 96 65 128 256), losses := [] }

theorem u7332 : Upper (D 7) (R 7) [36,72,129,288,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7333 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 133 296 146 96 66 145 273), lower := (rows 37 74 133 296 146 96 66 128 256), losses := [] }

theorem u7333 : Upper (D 7) (R 7) [36,72,129,288,130,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7334 : Route 9 := (fun mask => (mask,id))

def c7334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7334 : Upper (D 7) (R 7) [36,72,129,288,130,64,16] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,130,64,16] 13 (by decide) (choices 1) [1,2] r7334 c7334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u532
  · exact u533

def b7335 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 74 133 296 208 34 65 146 274), lower := (rows 37 74 133 296 208 34 65 128 256), losses := [] }

theorem u7335 : Upper (D 7) (R 7) [36,72,129,288,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7336 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 133 296 208 34 66 145 273), lower := (rows 37 74 133 296 208 34 66 128 256), losses := [] }

theorem u7336 : Upper (D 7) (R 7) [36,72,129,288,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7337 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 133 296 208 34 80 131 259), lower := (rows 37 74 133 296 208 34 80 128 256), losses := [] }

theorem u7337 : Upper (D 7) (R 7) [36,72,129,288,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7337 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7338 : Route 9 := (fun mask => (mask,id))

def c7338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7338 : Upper (D 7) (R 7) [36,72,129,384,3,2,16] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,3,2,16] 13 (by decide) (choices 1) [32,64] r7338 c7338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u534
  · exact u535

def b7339 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 98, targets := 129 },{ cop := 4, region := 488, targets := 1 }], pairs := [(1,0),(1,7),(2,1),(3,0)], upper := (rows 37 74 133 392 19 34 96 208 336), lower := (rows 37 74 133 392 19 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 97 144 272), good := (rows 101 72 197 392 477 96 96 128 256) }] }

theorem u7339 : Upper (D 7) (R 7) [36,72,129,384,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7340 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 133 392 19 48 66 224 352), lower := (rows 37 74 133 392 19 48 66 128 256), losses := [] }

theorem u7340 : Upper (D 7) (R 7) [36,72,129,384,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7341 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 133 392 19 48 96 194 322), lower := (rows 37 74 133 392 19 48 96 128 256), losses := [] }

theorem u7341 : Upper (D 7) (R 7) [36,72,129,384,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7341 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7342 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 3, region := 66, targets := 32 },{ cop := 4, region := 488, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 133 392 19 96 66 176 304), lower := (rows 37 74 133 392 19 96 66 128 256), losses := [] }

theorem u7342 : Upper (D 7) (R 7) [36,72,129,384,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7343 : Route 9 := (fun mask => (mask,id))

def c7343 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7343 : Upper (D 7) (R 7) [36,72,129,384,3,64,16] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,3,64,16] 13 (by decide) (choices 1) [2,32] r7343 c7343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u536
  · exact u537

def b7344 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6)], upper := (rows 37 74 133 392 19 96 96 146 274), lower := (rows 37 74 133 392 19 96 96 128 256), losses := [] }

theorem u7344 : Upper (D 7) (R 7) [36,72,129,384,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7345 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 3, region := 66, targets := 32 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 133 392 81 34 66 176 304), lower := (rows 37 74 133 392 81 34 66 128 256), losses := [] }

theorem u7345 : Upper (D 7) (R 7) [36,72,129,384,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7346 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 74 133 392 81 34 80 162 290), lower := (rows 37 74 133 392 81 34 80 128 256), losses := [] }

theorem u7346 : Upper (D 7) (R 7) [36,72,129,384,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7346 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7347 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 74 133 392 81 34 96 146 274), lower := (rows 37 74 133 392 81 34 96 128 256), losses := [] }

theorem u7347 : Upper (D 7) (R 7) [36,72,129,384,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7348 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 133 392 81 48 66 162 290), lower := (rows 37 74 133 392 81 48 66 128 256), losses := [] }

theorem u7348 : Upper (D 7) (R 7) [36,72,129,384,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7348 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7349 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 74 133 392 81 48 96 130 258), lower := (rows 37 74 133 392 81 48 96 128 256), losses := [] }

theorem u7349 : Upper (D 7) (R 7) [36,72,129,384,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7349 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7350 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 74 133 392 112 34 65 146 274), lower := (rows 37 74 133 392 112 34 65 128 256), losses := [] }

theorem u7350 : Upper (D 7) (R 7) [36,72,129,384,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7351 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 392 112 34 66 145 273), lower := (rows 37 74 133 392 112 34 66 128 256), losses := [] }

theorem u7351 : Upper (D 7) (R 7) [36,72,129,384,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7352 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 74 133 392 112 34 80 131 259), lower := (rows 37 74 133 392 112 34 80 128 256), losses := [] }

theorem u7352 : Upper (D 7) (R 7) [36,72,129,384,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7352 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7353 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 1, region := 164, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(2,0),(4,7)], upper := (rows 37 74 134 152 273 96 65 162 290), lower := (rows 37 74 134 152 273 96 65 128 256), losses := [] }

theorem u7353 : Upper (D 7) (R 7) [36,72,130,144,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7354 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 134 152 273 96 66 161 289), lower := (rows 37 74 134 152 273 96 66 128 256), losses := [] }

theorem u7354 : Upper (D 7) (R 7) [36,72,130,144,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7355 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 3, region := 102, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(4,7)], upper := (rows 37 74 134 152 273 96 96 131 259), lower := (rows 37 74 134 152 273 96 96 128 256), losses := [] }

theorem u7355 : Upper (D 7) (R 7) [36,72,130,144,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7356 : Route 9 := (fun mask => (mask,id))

def c7356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7356 : Upper (D 7) (R 7) [36,72,130,144,258,64,1] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,258,64,1] 13 (by decide) (choices 1) [1,32] r7356 c7356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u538
  · exact u539

def b7357 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 3, region := 102, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(4,7)], upper := (rows 37 74 134 152 274 96 96 129 257), lower := (rows 37 74 134 152 274 96 96 128 256), losses := [] }

theorem u7357 : Upper (D 7) (R 7) [36,72,130,144,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7358 : Route 9 := (fun mask => (mask,id))

def c7358 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7358 : Upper (D 7) (R 7) [36,72,130,144,288,64,1] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,288,64,1] 13 (by decide) (choices 1) [1,2] r7358 c7358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u540
  · exact u541

def b7359 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 134 152 304 96 66 129 257), lower := (rows 37 74 134 152 304 96 66 128 256), losses := [] }

theorem u7359 : Upper (D 7) (R 7) [36,72,130,144,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7360 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 388, targets := 97 }], pairs := [(2,0),(2,5),(2,6)], upper := (rows 37 74 134 168 81 48 65 386 258), lower := (rows 37 74 134 168 81 48 65 128 256), losses := [] }

theorem u7360 : Upper (D 7) (R 7) [36,72,130,160,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7360 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7361 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 134 168 81 48 66 385 257), lower := (rows 37 74 134 168 81 48 66 128 256), losses := [] }

theorem u7361 : Upper (D 7) (R 7) [36,72,130,160,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7361 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7362 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(4,7)], upper := (rows 37 74 134 168 81 48 320 131 259), lower := (rows 37 74 134 168 81 48 320 128 256), losses := [] }

theorem u7362 : Upper (D 7) (R 7) [36,72,130,160,65,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7362 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7363 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 74 134 168 81 288 65 146 274), lower := (rows 37 74 134 168 81 288 65 128 256), losses := [] }

theorem u7363 : Upper (D 7) (R 7) [36,72,130,160,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7363 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7364 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 134 168 81 288 66 145 273), lower := (rows 37 74 134 168 81 288 66 128 256), losses := [] }

theorem u7364 : Upper (D 7) (R 7) [36,72,130,160,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7364 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7365 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 37 74 134 168 81 288 80 131 259), lower := (rows 37 74 134 168 81 288 80 128 256), losses := [] }

theorem u7365 : Upper (D 7) (R 7) [36,72,130,160,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7365 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7366 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 132, targets := 33 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(2,0),(2,5)], upper := (rows 37 74 134 168 273 48 65 194 322), lower := (rows 37 74 134 168 273 48 65 128 256), losses := [] }

theorem u7366 : Upper (D 7) (R 7) [36,72,130,160,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7366 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7367 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 134 168 273 48 66 193 321), lower := (rows 37 74 134 168 273 48 66 128 256), losses := [] }

theorem u7367 : Upper (D 7) (R 7) [36,72,130,160,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7367 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7368 : Route 9 := (fun mask => (mask,id))

def c7368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7368 : Upper (D 7) (R 7) [36,72,130,160,320,16,1] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,320,16,1] 13 (by decide) (choices 1) [1,2] r7368 c7368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u542
  · exact u543

def b7369 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 134 168 336 48 66 129 257), lower := (rows 37 74 134 168 336 48 66 128 256), losses := [] }

theorem u7369 : Upper (D 7) (R 7) [36,72,130,160,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7369 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7370 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(3,1),(3,6)], upper := (rows 37 74 134 265 81 48 66 160 416), lower := (rows 37 74 134 265 81 48 66 128 256), losses := [] }

theorem u7370 : Upper (D 7) (R 7) [36,72,130,257,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7370 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7371 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 74 134 265 81 48 96 130 386), lower := (rows 37 74 134 265 81 48 96 128 256), losses := [] }

theorem u7371 : Upper (D 7) (R 7) [36,72,130,257,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7371 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7372 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 4, region := 298, targets := 128 }], pairs := [(0,1),(1,7),(4,1)], upper := (rows 37 74 134 265 81 48 192 162 290), lower := (rows 37 74 134 265 81 48 192 128 256), losses := [] }

theorem u7372 : Upper (D 7) (R 7) [36,72,130,257,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7372 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7373 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 80, targets := 33 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(4,0),(4,5)], upper := (rows 37 74 134 265 208 33 66 176 304), lower := (rows 37 74 134 265 208 33 66 128 256), losses := [] }

theorem u7373 : Upper (D 7) (R 7) [36,72,130,257,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7374 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 134 265 208 33 80 162 290), lower := (rows 37 74 134 265 208 33 80 128 256), losses := [] }

theorem u7374 : Upper (D 7) (R 7) [36,72,130,257,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7374 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7375 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 74 134 265 208 33 96 146 274), lower := (rows 37 74 134 265 208 33 96 128 256), losses := [] }

theorem u7375 : Upper (D 7) (R 7) [36,72,130,257,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7376 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 1, region := 180, targets := 1 }], pairs := [(1,7),(2,0),(3,7)], upper := (rows 37 74 134 265 208 48 65 162 290), lower := (rows 37 74 134 265 208 48 65 128 256), losses := [] }

theorem u7376 : Upper (D 7) (R 7) [36,72,130,257,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7376 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7377 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 134 265 208 48 66 161 289), lower := (rows 37 74 134 265 208 48 66 128 256), losses := [] }

theorem u7377 : Upper (D 7) (R 7) [36,72,130,257,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7377 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7378 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 113, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 74 134 265 208 48 96 131 259), lower := (rows 37 74 134 265 208 48 96 128 256), losses := [] }

theorem u7378 : Upper (D 7) (R 7) [36,72,130,257,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7378 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7379 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 37 74 134 266 81 48 65 160 416), lower := (rows 37 74 134 266 81 48 65 128 256), losses := [] }

theorem u7379 : Upper (D 7) (R 7) [36,72,130,258,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7379 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7379
end Delivery.IrregularNine14.P07
