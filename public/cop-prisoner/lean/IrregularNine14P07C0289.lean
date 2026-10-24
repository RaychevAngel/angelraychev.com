import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0070
import IrregularNine14P07C0071

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17340 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 37 74 176 96 210 146 402), lower := (rows 13 259 37 74 176 96 64 128 256), losses := [] }

theorem u17340 : Upper (D 7) (R 7) [12,257,33,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17341 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 37 74 176 160 82 210 338), lower := (rows 13 259 37 74 176 160 64 128 256), losses := [] }

theorem u17341 : Upper (D 7) (R 7) [12,257,33,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17342 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 259 37 74 208 34 240 176 432), lower := (rows 13 259 37 74 208 34 64 128 256), losses := [] }

theorem u17342 : Upper (D 7) (R 7) [12,257,33,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17343 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 13 259 37 74 208 48 226 162 418), lower := (rows 13 259 37 74 208 48 64 128 256), losses := [] }

theorem u17343 : Upper (D 7) (R 7) [12,257,33,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17343 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17344 : Route 9 := (fun mask => (mask,id))

def c17344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17344 : Upper (D 7) (R 7) [12,257,33,66,192,128] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66,192,128] 13 (by decide) (choices 1) [2,16,32] r17344 c17344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4235
  · exact u4236
  · exact u4237

def b17345 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 1, region := 36, targets := 192 }], pairs := [(2,6),(2,7),(3,0),(4,0)], upper := (rows 13 259 37 88 146 34 224 224 480), lower := (rows 13 259 37 88 146 34 64 128 256), losses := [] }

theorem u17345 : Upper (D 7) (R 7) [12,257,33,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17346 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 37 88 146 96 226 162 418), lower := (rows 13 259 37 88 146 96 64 128 256), losses := [] }

theorem u17346 : Upper (D 7) (R 7) [12,257,33,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17347 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 2, region := 322, targets := 128 }], pairs := [(0,1),(1,7),(3,0),(4,0)], upper := (rows 13 259 37 88 146 160 98 226 354), lower := (rows 13 259 37 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 13 257 37 125 176 160 64 160 256) }] }

theorem u17347 : Upper (D 7) (R 7) [12,257,33,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17348 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 1, region := 36, targets := 192 }], pairs := [(2,6),(2,7),(3,0),(4,0)], upper := (rows 13 259 37 88 176 34 194 194 450), lower := (rows 13 259 37 88 176 34 64 128 256), losses := [] }

theorem u17348 : Upper (D 7) (R 7) [12,257,33,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17349 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 37 88 176 96 194 130 386), lower := (rows 13 259 37 88 176 96 64 128 256), losses := [] }

theorem u17349 : Upper (D 7) (R 7) [12,257,33,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17350 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 37 88 176 160 66 194 322), lower := (rows 13 259 37 88 176 160 64 128 256), losses := [] }

theorem u17350 : Upper (D 7) (R 7) [12,257,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17351 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 52, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 259 37 200 50 34 208 208 464), lower := (rows 13 259 37 200 50 34 64 128 256), losses := [] }

theorem u17351 : Upper (D 7) (R 7) [12,257,33,192,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17352 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 52, targets := 192 }], pairs := [(2,6),(2,7),(4,6)], upper := (rows 13 259 37 200 50 48 194 194 450), lower := (rows 13 259 37 200 50 48 64 128 256), losses := [] }

theorem u17352 : Upper (D 7) (R 7) [12,257,33,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17352 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17353 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 37 200 50 96 210 146 402), lower := (rows 13 259 37 200 50 96 64 128 256), losses := [] }

theorem u17353 : Upper (D 7) (R 7) [12,257,33,192,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17354 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 1, region := 36, targets := 192 }], pairs := [(2,6),(2,7),(3,0),(4,0)], upper := (rows 13 259 37 200 82 34 240 176 432), lower := (rows 13 259 37 200 82 34 64 128 256), losses := [] }

theorem u17354 : Upper (D 7) (R 7) [12,257,33,192,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17355 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 13 259 37 200 82 48 226 162 418), lower := (rows 13 259 37 200 82 48 64 128 256), losses := [] }

theorem u17355 : Upper (D 7) (R 7) [12,257,33,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17355 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17356 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 259 37 200 82 160 114 178 306), lower := (rows 13 259 37 200 82 160 64 128 256), losses := [] }

theorem u17356 : Upper (D 7) (R 7) [12,257,33,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17357 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 1, region := 36, targets := 192 }], pairs := [(2,6),(2,7),(3,0),(4,0)], upper := (rows 13 259 37 200 112 34 210 146 402), lower := (rows 13 259 37 200 112 34 64 128 256), losses := [] }

theorem u17357 : Upper (D 7) (R 7) [12,257,33,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17358 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 13 259 37 200 112 48 194 130 386), lower := (rows 13 259 37 200 112 48 64 128 256), losses := [] }

theorem u17358 : Upper (D 7) (R 7) [12,257,33,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17358 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17359 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 13 259 37 200 112 160 82 146 274), lower := (rows 13 259 37 200 112 160 64 128 256), losses := [] }

theorem u17359 : Upper (D 7) (R 7) [12,257,33,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17360 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 217, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(1,5),(3,1),(4,1)], upper := (rows 13 259 38 56 81 34 192 192 448), lower := (rows 13 259 38 56 81 34 64 128 256), losses := [] }

theorem u17360 : Upper (D 7) (R 7) [12,257,34,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17361 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 13 259 38 56 81 96 194 130 386), lower := (rows 13 259 38 56 81 96 64 128 256), losses := [] }

theorem u17361 : Upper (D 7) (R 7) [12,257,34,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17362 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 228, targets := 1 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 13 259 38 56 81 160 194 194 450), lower := (rows 13 259 38 56 81 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 24 16 167 70 134 262), good := (rows 492 486 486 56 120 160 64 160 256) }] }

theorem u17362 : Upper (D 7) (R 7) [12,257,34,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17363 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 259 38 56 82 33 192 192 448), lower := (rows 13 259 38 56 82 33 64 128 256), losses := [] }

theorem u17363 : Upper (D 7) (R 7) [12,257,34,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17364 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 45, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 13 259 38 56 82 96 193 129 385), lower := (rows 13 259 38 56 82 96 64 128 256), losses := [] }

theorem u17364 : Upper (D 7) (R 7) [12,257,34,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17365 : Route 9 := (fun mask => (mask,id))

def c17365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17365 : Upper (D 7) (R 7) [12,257,34,48,66,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,48,66,128] 13 (by decide) (choices 1) [1,128] r17365 c17365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4238
  · exact u4239

def b17366 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 36, targets := 192 }], pairs := [(1,5),(2,6),(2,7),(4,5)], upper := (rows 13 259 38 56 208 33 194 194 450), lower := (rows 13 259 38 56 208 33 64 128 256), losses := [] }

theorem u17366 : Upper (D 7) (R 7) [12,257,34,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17367 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 259 38 56 208 34 193 193 449), lower := (rows 13 259 38 56 208 34 64 128 256), losses := [] }

theorem u17367 : Upper (D 7) (R 7) [12,257,34,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17368 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 13 259 38 56 208 96 195 131 387), lower := (rows 13 259 38 56 208 96 64 128 256), losses := [] }

theorem u17368 : Upper (D 7) (R 7) [12,257,34,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17369 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 13 259 38 74 49 48 192 192 448), lower := (rows 13 259 38 74 49 48 64 128 256), losses := [] }

theorem u17369 : Upper (D 7) (R 7) [12,257,34,66,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17369 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17370 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 4, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 13 259 38 74 49 96 208 144 400), lower := (rows 13 259 38 74 49 96 64 128 256), losses := [] }

theorem u17370 : Upper (D 7) (R 7) [12,257,34,66,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17371 : Route 9 := (fun mask => (mask,id))

def c17371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17371 : Upper (D 7) (R 7) [12,257,34,66,33,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,33,128] 13 (by decide) (choices 1) [16,128] r17371 c17371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4240
  · exact u4241

def b17372 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 2, region := 216, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 13 259 38 74 112 33 208 144 400), lower := (rows 13 259 38 74 112 33 64 128 256), losses := [] }

theorem u17372 : Upper (D 7) (R 7) [12,257,34,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17373 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 13 259 38 74 112 48 193 129 385), lower := (rows 13 259 38 74 112 48 64 128 256), losses := [] }

theorem u17373 : Upper (D 7) (R 7) [12,257,34,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17373 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17374_1 : Upper (D 7) (R 7) [12,257,34,66,96,128,1] 13 :=
  permutation_upper _ _ _ [12,257,34,66,96,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4242

theorem m17374_16 : Upper (D 7) (R 7) [12,257,34,66,96,128,16] 13 :=
  permutation_upper _ _ _ [12,257,34,66,96,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4243

def r17374 : Route 9 := (fun mask => (mask,id))

def c17374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17374 : Upper (D 7) (R 7) [12,257,34,66,96,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,96,128] 13 (by decide) (choices 1) [1,16,128] r17374 c17374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m17374_1
  · exact m17374_16
  · exact u4244

def r17375 : Route 9 := (fun mask => (mask,id))

def c17375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17375 : Upper (D 7) (R 7) [12,257,34,66,129,16] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,129,16] 13 (by decide) (choices 1) [32,128] r17375 c17375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4245
  · exact u4246

def b17376 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 128 },{ cop := 0, region := 240, targets := 2 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(2,0),(2,7),(4,1)], upper := (rows 13 259 38 74 145 96 240 176 432), lower := (rows 13 259 38 74 145 96 64 128 256), losses := [] }

theorem u17376 : Upper (D 7) (R 7) [12,257,34,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17377_16 : Upper (D 7) (R 7) [12,257,34,66,129,128,16] 13 :=
  permutation_upper _ _ _ [12,257,34,66,129,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4246

theorem m17377_32 : Upper (D 7) (R 7) [12,257,34,66,129,128,32] 13 :=
  permutation_upper _ _ _ [12,257,34,66,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4247

def r17377 : Route 9 := (fun mask => (mask,id))

def c17377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17377 : Upper (D 7) (R 7) [12,257,34,66,129,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,129,128] 13 (by decide) (choices 1) [16,32] r17377 c17377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17377_16
  · exact m17377_32

def b17378 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 259 38 74 176 33 208 208 464), lower := (rows 13 259 38 74 176 33 64 128 256), losses := [] }

theorem u17378 : Upper (D 7) (R 7) [12,257,34,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17379 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 13 259 38 74 176 48 193 193 449), lower := (rows 13 259 38 74 176 48 64 128 256), losses := [] }

theorem u17379 : Upper (D 7) (R 7) [12,257,34,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17379 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17380 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 128 },{ cop := 0, region := 240, targets := 2 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(2,0),(2,7),(4,1)], upper := (rows 13 259 38 74 176 96 209 145 401), lower := (rows 13 259 38 74 176 96 64 128 256), losses := [] }

theorem u17380 : Upper (D 7) (R 7) [12,257,34,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17381 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 38 74 176 160 81 209 337), lower := (rows 13 259 38 74 176 160 64 128 256), losses := [] }

theorem u17381 : Upper (D 7) (R 7) [12,257,34,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17382 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 52, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 259 38 88 49 34 192 192 448), lower := (rows 13 259 38 88 49 34 64 128 256), losses := [] }

theorem u17382 : Upper (D 7) (R 7) [12,257,34,80,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17383 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 390, targets := 64 }], pairs := [(1,5),(1,6),(2,6),(3,5)], upper := (rows 13 259 38 88 49 96 194 130 386), lower := (rows 13 259 38 88 49 96 64 128 256), losses := [] }

theorem u17383 : Upper (D 7) (R 7) [12,257,34,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17384 : Route 9 := (fun mask => (mask,id))

def c17384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17384 : Upper (D 7) (R 7) [12,257,34,80,33,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,33,128] 13 (by decide) (choices 1) [2,128] r17384 c17384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4248
  · exact u4249

def b17385 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 217, targets := 2 },{ cop := 1, region := 36, targets := 64 }], pairs := [(0,1),(2,6),(3,1),(4,1)], upper := (rows 13 259 38 88 145 34 224 224 480), lower := (rows 13 259 38 88 145 34 64 128 256), losses := [] }

theorem u17385 : Upper (D 7) (R 7) [12,257,34,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17386 : Route 9 := (fun mask => (mask,id))

def c17386 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17386 : Upper (D 7) (R 7) [12,257,34,80,129,64] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,129,64] 13 (by decide) (choices 1) [2,32,128] r17386 c17386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4250
  · exact u4251
  · exact u4252

def r17387 : Route 9 := (fun mask => (mask,id))

def c17387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17387 : Upper (D 7) (R 7) [12,257,34,80,129,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,129,128] 13 (by decide) (choices 1) [2,32] r17387 c17387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4253
  · exact u4254

def b17388 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 36, targets := 192 },{ cop := 2, region := 216, targets := 1 }], pairs := [(2,6),(2,7),(3,0),(4,0)], upper := (rows 13 259 38 88 146 33 224 224 480), lower := (rows 13 259 38 88 146 33 64 128 256), losses := [] }

theorem u17388 : Upper (D 7) (R 7) [12,257,34,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17389 : Route 9 := (fun mask => (mask,id))

def c17389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17389 : Upper (D 7) (R 7) [12,257,34,80,130,64] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,130,64] 13 (by decide) (choices 1) [1,32,128] r17389 c17389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4255
  · exact u4256
  · exact u4257

def b17390 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 65 }], pairs := [(0,6),(2,0),(2,6),(3,1)], upper := (rows 13 259 38 88 146 160 97 225 353), lower := (rows 13 259 38 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 183 67 131 259), good := (rows 493 481 484 120 504 160 64 160 256) },{ target := 6, region := (rows 9 2 20 8 16 176 0 128 256), good := (rows 13 259 38 61 182 160 0 160 256) }] }

theorem u17390 : Upper (D 7) (R 7) [12,257,34,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17391 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 36, targets := 192 },{ cop := 2, region := 216, targets := 1 }], pairs := [(2,6),(2,7),(3,0),(4,0)], upper := (rows 13 259 38 88 176 33 194 194 450), lower := (rows 13 259 38 88 176 33 64 128 256), losses := [] }

theorem u17391 : Upper (D 7) (R 7) [12,257,34,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17392 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 259 38 88 176 34 193 193 449), lower := (rows 13 259 38 88 176 34 64 128 256), losses := [] }

theorem u17392 : Upper (D 7) (R 7) [12,257,34,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17393 : Route 9 := (fun mask => (mask,id))

def c17393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17393 : Upper (D 7) (R 7) [12,257,34,80,160,64] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80,160,64] 13 (by decide) (choices 1) [1,2,128] r17393 c17393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4258
  · exact u4259
  · exact u4260

def b17394 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 38 88 176 160 67 195 323), lower := (rows 13 259 38 88 176 160 64 128 256), losses := [] }

theorem u17394 : Upper (D 7) (R 7) [12,257,34,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17395 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 13 259 38 104 82 33 208 144 400), lower := (rows 13 259 38 104 82 33 64 128 256), losses := [] }

theorem u17395 : Upper (D 7) (R 7) [12,257,34,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17396 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 13 259 38 104 82 48 193 129 385), lower := (rows 13 259 38 104 82 48 64 128 256), losses := [] }

theorem u17396 : Upper (D 7) (R 7) [12,257,34,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17396 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17397 : Route 9 := (fun mask => (mask,id))

def c17397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17397 : Upper (D 7) (R 7) [12,257,34,96,66,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,96,66,128] 13 (by decide) (choices 1) [1,16,128] r17397 c17397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4261
  · exact u4262
  · exact u4263

def b17398 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 259 38 104 145 34 208 208 464), lower := (rows 13 259 38 104 145 34 64 128 256), losses := [] }

theorem u17398 : Upper (D 7) (R 7) [12,257,34,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17399 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 200, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 13 259 38 104 145 48 194 194 450), lower := (rows 13 259 38 104 145 48 64 128 256), losses := [] }

theorem u17399 : Upper (D 7) (R 7) [12,257,34,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17399 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17399
end Delivery.IrregularNine14.P07
