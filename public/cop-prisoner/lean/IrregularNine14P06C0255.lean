import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0058
import IrregularNine14P06C0059

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15300 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 131 37 268 22 48 96 224 352), lower := (rows 11 131 37 268 22 48 64 128 256), losses := [] }

theorem u15300 : Upper (D 6) (R 6) [10,129,33,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15300 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15301 : Route 9 := (fun mask => (mask,id))

def c15301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15301 : Upper (D 6) (R 6) [10,129,33,260,6,64] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,6,64] 13 (by decide) (choices 1) [16,32] r15301 c15301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3528
  · exact u3529

def b15302 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 210, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 11 131 37 268 50 36 80 208 336), lower := (rows 11 131 37 268 50 36 64 128 256), losses := [] }

theorem u15302 : Upper (D 6) (R 6) [10,129,33,260,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15303 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 268 50 48 68 196 324), lower := (rows 11 131 37 268 50 48 64 128 256), losses := [] }

theorem u15303 : Upper (D 6) (R 6) [10,129,33,260,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15303 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15304 : Route 9 := (fun mask => (mask,id))

def c15304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15304 : Upper (D 6) (R 6) [10,129,33,260,34,64] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,34,64] 13 (by decide) (choices 1) [4,16] r15304 c15304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3530
  · exact u3531

def b15305 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 268 82 36 112 240 368), lower := (rows 11 131 37 268 82 36 64 128 256), losses := [] }

theorem u15305 : Upper (D 6) (R 6) [10,129,33,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15306 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 268 82 48 100 228 356), lower := (rows 11 131 37 268 82 48 64 128 256), losses := [] }

theorem u15306 : Upper (D 6) (R 6) [10,129,33,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15306 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15307 : Route 9 := (fun mask => (mask,id))

def c15307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15307 : Upper (D 6) (R 6) [10,129,33,260,66,64] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,66,64] 13 (by decide) (choices 1) [4,16,32] r15307 c15307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3532
  · exact u3533
  · exact u3534

def b15308 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 268 84 34 112 240 368), lower := (rows 11 131 37 268 84 34 64 128 256), losses := [] }

theorem u15308 : Upper (D 6) (R 6) [10,129,33,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15309 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 194, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 11 131 37 268 84 48 98 226 354), lower := (rows 11 131 37 268 84 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 60 65 129 257), good := (rows 490 450 508 316 124 48 64 128 256) }] }

theorem u15309 : Upper (D 6) (R 6) [10,129,33,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15309 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15310 : Route 9 := (fun mask => (mask,id))

def c15310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15310 : Upper (D 6) (R 6) [10,129,33,260,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,33,260,68,64] 13 (by decide) (choices 1) [2,16,32] r15310 c15310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3535
  · exact u3536
  · exact u3537

def b15311 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 268 112 34 84 212 340), lower := (rows 11 131 37 268 112 34 64 128 256), losses := [] }

theorem u15311 : Upper (D 6) (R 6) [10,129,33,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15312 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 268 112 36 82 210 338), lower := (rows 11 131 37 268 112 36 64 128 256), losses := [] }

theorem u15312 : Upper (D 6) (R 6) [10,129,33,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15313 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 268 112 48 70 198 326), lower := (rows 11 131 37 268 112 48 64 128 256), losses := [] }

theorem u15313 : Upper (D 6) (R 6) [10,129,33,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15313 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15314 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 37 268 112 96 86 150 278), lower := (rows 11 131 37 268 112 96 64 128 256), losses := [] }

theorem u15314 : Upper (D 6) (R 6) [10,129,33,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15315 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 131 37 280 82 36 100 228 356), lower := (rows 11 131 37 280 82 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 55 119 183 311), good := (rows 493 485 485 504 508 484 64 128 256) }] }

theorem u15315 : Upper (D 6) (R 6) [10,129,33,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15316 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 131 37 280 82 96 100 164 292), lower := (rows 11 131 37 280 82 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 127 87 151 279), good := (rows 493 485 485 504 508 96 96 128 256) }] }

theorem u15316 : Upper (D 6) (R 6) [10,129,33,272,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15317 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 280 84 34 100 228 356), lower := (rows 11 131 37 280 84 34 64 128 256), losses := [] }

theorem u15317 : Upper (D 6) (R 6) [10,129,33,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15318 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 131 37 280 84 36 98 226 354), lower := (rows 11 131 37 280 84 36 64 128 256), losses := [] }

theorem u15318 : Upper (D 6) (R 6) [10,129,33,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15319 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 37 280 84 96 102 166 294), lower := (rows 11 131 37 280 84 96 64 128 256), losses := [{ target := 6, region := (rows 25 22 4 24 16 32 0 132 260), good := (rows 11 131 423 283 415 32 0 128 256) }] }

theorem u15319 : Upper (D 6) (R 6) [10,129,33,272,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15320 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 280 112 34 68 196 324), lower := (rows 11 131 37 280 112 34 64 128 256), losses := [] }

theorem u15320 : Upper (D 6) (R 6) [10,129,33,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15321 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 280 112 36 70 198 326), lower := (rows 11 131 37 280 112 36 64 128 256), losses := [] }

theorem u15321 : Upper (D 6) (R 6) [10,129,33,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15322 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 37 280 112 96 70 134 262), lower := (rows 11 131 37 280 112 96 64 128 256), losses := [] }

theorem u15322 : Upper (D 6) (R 6) [10,129,33,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15323 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 296 82 36 84 212 340), lower := (rows 11 131 37 296 82 36 64 128 256), losses := [] }

theorem u15323 : Upper (D 6) (R 6) [10,129,33,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15324 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 296 82 48 68 196 324), lower := (rows 11 131 37 296 82 48 64 128 256), losses := [] }

theorem u15324 : Upper (D 6) (R 6) [10,129,33,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15324 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15325 : Route 9 := (fun mask => (mask,id))

def c15325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15325 : Upper (D 6) (R 6) [10,129,33,288,66,64] 13 := by
  apply FastRouting.sound _ _ [10,129,33,288,66,64] 13 (by decide) (choices 1) [4,16] r15325 c15325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3538
  · exact u3539

def b15326 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 296 84 34 84 212 340), lower := (rows 11 131 37 296 84 34 64 128 256), losses := [] }

theorem u15326 : Upper (D 6) (R 6) [10,129,33,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15327 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 131 37 296 84 36 82 210 338), lower := (rows 11 131 37 296 84 36 64 128 256), losses := [] }

theorem u15327 : Upper (D 6) (R 6) [10,129,33,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15328 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 131 37 296 84 48 70 198 326), lower := (rows 11 131 37 296 84 48 64 128 256), losses := [] }

theorem u15328 : Upper (D 6) (R 6) [10,129,33,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15328 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15329 : Route 9 := (fun mask => (mask,id))

def c15329 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15329 : Upper (D 6) (R 6) [10,129,33,288,68,64] 13 := by
  apply FastRouting.sound _ _ [10,129,33,288,68,64] 13 (by decide) (choices 1) [2,4,16] r15329 c15329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3540
  · exact u3541
  · exact u3542

def b15330 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 360, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 37 328 22 36 112 240 368), lower := (rows 11 131 37 328 22 36 64 128 256), losses := [] }

theorem u15330 : Upper (D 6) (R 6) [10,129,33,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15331 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 131 37 328 22 48 100 228 356), lower := (rows 11 131 37 328 22 48 64 128 256), losses := [] }

theorem u15331 : Upper (D 6) (R 6) [10,129,33,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15331 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15332 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 146, targets := 64 },{ cop := 4, region := 360, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 131 37 328 22 96 116 180 308), lower := (rows 11 131 37 328 22 96 64 128 256), losses := [] }

theorem u15332 : Upper (D 6) (R 6) [10,129,33,320,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15333 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 131 37 328 50 36 84 212 340), lower := (rows 11 131 37 328 50 36 64 128 256), losses := [] }

theorem u15333 : Upper (D 6) (R 6) [10,129,33,320,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15334 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 328 50 48 68 196 324), lower := (rows 11 131 37 328 50 48 64 128 256), losses := [] }

theorem u15334 : Upper (D 6) (R 6) [10,129,33,320,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15334 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15335 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 146, targets := 64 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 131 37 328 50 96 84 148 276), lower := (rows 11 131 37 328 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 108 68 132 260), good := (rows 58 146 508 360 50 96 96 128 256) }] }

theorem u15335 : Upper (D 6) (R 6) [10,129,33,320,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15336 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 131 37 328 82 36 116 180 308), lower := (rows 11 131 37 328 82 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 55 80 144 272), good := (rows 45 165 37 328 508 36 64 128 256) }] }

theorem u15336 : Upper (D 6) (R 6) [10,129,33,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15337 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 328 82 48 100 164 292), lower := (rows 11 131 37 328 82 48 64 128 256), losses := [] }

theorem u15337 : Upper (D 6) (R 6) [10,129,33,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15337 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15338 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 328 84 34 116 180 308), lower := (rows 11 131 37 328 84 34 64 128 256), losses := [] }

theorem u15338 : Upper (D 6) (R 6) [10,129,33,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15339 : Route 9 := (fun mask => (mask,id))

def c15339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15339 : Upper (D 6) (R 6) [10,129,33,320,68,4] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320,68,4] 13 (by decide) (choices 1) [2,16,32] r15339 c15339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3543
  · exact u3544
  · exact u3545

def r15340 : Route 9 := (fun mask => (mask,id))

def c15340 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15340 : Upper (D 6) (R 6) [10,129,33,320,68,16] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320,68,16] 13 (by decide) (choices 1) [2,4,32] r15340 c15340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3546
  · exact u3547
  · exact u3548

def b15341 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 328 112 34 84 148 276), lower := (rows 11 131 37 328 112 34 64 128 256), losses := [] }

theorem u15341 : Upper (D 6) (R 6) [10,129,33,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15342 : Route 9 := (fun mask => (mask,id))

def c15342 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15342 : Upper (D 6) (R 6) [10,129,33,320,96,4] 13 := by
  apply FastRouting.sound _ _ [10,129,33,320,96,4] 13 (by decide) (choices 1) [2,4,16] r15342 c15342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3549
  · exact u3550
  · exact u3551

def b15343 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 328 112 48 70 134 262), lower := (rows 11 131 37 328 112 48 64 128 256), losses := [] }

theorem u15343 : Upper (D 6) (R 6) [10,129,33,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15343 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15344 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 28 112 33 324 452 324), lower := (rows 11 131 38 28 112 33 64 128 256), losses := [] }

theorem u15344 : Upper (D 6) (R 6) [10,129,34,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15345 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 28 112 36 321 449 321), lower := (rows 11 131 38 28 112 36 64 128 256), losses := [] }

theorem u15345 : Upper (D 6) (R 6) [10,129,34,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15346 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 28 112 96 325 389 261), lower := (rows 11 131 38 28 112 96 64 128 256), losses := [] }

theorem u15346 : Upper (D 6) (R 6) [10,129,34,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15347 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 28 112 288 69 197 325), lower := (rows 11 131 38 28 112 288 64 128 256), losses := [] }

theorem u15347 : Upper (D 6) (R 6) [10,129,34,20,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15347 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15348 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 28 304 33 68 196 324), lower := (rows 11 131 38 28 304 33 64 128 256), losses := [] }

theorem u15348 : Upper (D 6) (R 6) [10,129,34,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15349 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 28 304 36 65 193 321), lower := (rows 11 131 38 28 304 36 64 128 256), losses := [] }

theorem u15349 : Upper (D 6) (R 6) [10,129,34,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15350 : Route 9 := (fun mask => (mask,id))

def c15350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15350 : Upper (D 6) (R 6) [10,129,34,20,288,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,20,288,64] 13 (by decide) (choices 1) [1,4] r15350 c15350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3552
  · exact u3553

def b15351 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 28 336 33 100 228 356), lower := (rows 11 131 38 28 336 33 64 128 256), losses := [] }

theorem u15351 : Upper (D 6) (R 6) [10,129,34,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15352 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,1)], upper := (rows 11 131 38 28 336 36 97 225 353), lower := (rows 11 131 38 28 336 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 19 44 65 129 257), good := (rows 505 465 60 60 336 44 64 128 256) }] }

theorem u15352 : Upper (D 6) (R 6) [10,129,34,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15353 : Route 9 := (fun mask => (mask,id))

def c15353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15353 : Upper (D 6) (R 6) [10,129,34,20,320,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,20,320,64] 13 (by decide) (choices 1) [1,4,32] r15353 c15353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3554
  · exact u3555
  · exact u3556

def b15354 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 36, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 56 81 36 324 452 324), lower := (rows 11 131 38 56 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) }] }

theorem u15354 : Upper (D 6) (R 6) [10,129,34,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15355 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 56 81 96 324 388 260), lower := (rows 11 131 38 56 81 96 64 128 256), losses := [] }

theorem u15355 : Upper (D 6) (R 6) [10,129,34,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15356 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 131 38 56 81 288 68 196 324), lower := (rows 11 131 38 56 81 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 319 87 151 279), good := (rows 494 486 486 504 508 288 64 128 288) }] }

theorem u15356 : Upper (D 6) (R 6) [10,129,34,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15356 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15357 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 56 84 33 324 452 324), lower := (rows 11 131 38 56 84 33 64 128 256), losses := [] }

theorem u15357 : Upper (D 6) (R 6) [10,129,34,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15358 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 56 84 36 321 449 321), lower := (rows 11 131 38 56 84 36 64 128 256), losses := [] }

theorem u15358 : Upper (D 6) (R 6) [10,129,34,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15359 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 56 84 96 325 389 261), lower := (rows 11 131 38 56 84 96 64 128 256), losses := [] }

theorem u15359 : Upper (D 6) (R 6) [10,129,34,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15359
end Delivery.IrregularNine14.P06
