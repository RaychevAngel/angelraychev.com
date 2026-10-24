import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9360 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 266 21 104 82 160 66 129 385), lower := (rows 37 266 21 104 82 160 66 128 256), losses := [] }

theorem u9360 : Upper (D 7) (R 7) [36,264,17,96,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9361 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 21 104 82 160 192 131 259), lower := (rows 37 266 21 104 82 160 192 128 256), losses := [] }

theorem u9361 : Upper (D 7) (R 7) [36,264,17,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9362 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 266 21 104 208 34 65 130 386), lower := (rows 37 266 21 104 208 34 65 128 256), losses := [] }

theorem u9362 : Upper (D 7) (R 7) [36,264,17,96,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9363 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 266 21 104 208 34 66 129 385), lower := (rows 37 266 21 104 208 34 66 128 256), losses := [] }

theorem u9363 : Upper (D 7) (R 7) [36,264,17,96,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9364 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 21 104 208 34 192 131 259), lower := (rows 37 266 21 104 208 34 192 128 256), losses := [] }

theorem u9364 : Upper (D 7) (R 7) [36,264,17,96,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9365 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 266 21 200 82 160 65 162 290), lower := (rows 37 266 21 200 82 160 65 128 256), losses := [] }

theorem u9365 : Upper (D 7) (R 7) [36,264,17,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9366 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 266 21 200 82 160 66 161 289), lower := (rows 37 266 21 200 82 160 66 128 256), losses := [] }

theorem u9366 : Upper (D 7) (R 7) [36,264,17,192,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9367 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 37 266 21 200 82 160 96 131 259), lower := (rows 37 266 21 200 82 160 96 128 256), losses := [] }

theorem u9367 : Upper (D 7) (R 7) [36,264,17,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9368 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,5)], upper := (rows 37 266 22 11 81 160 96 192 448), lower := (rows 37 266 22 11 81 160 96 128 256), losses := [] }

theorem u9368 : Upper (D 7) (R 7) [36,264,18,3,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9369 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(2,5),(4,1)], upper := (rows 37 266 22 11 81 160 192 224 352), lower := (rows 37 266 22 11 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 17 0 224 128 256), good := (rows 85 270 22 31 81 192 192 192 256) }] }

theorem u9369 : Upper (D 7) (R 7) [36,264,18,3,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9370 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 266 22 42 81 160 65 192 448), lower := (rows 37 266 22 42 81 160 65 128 256), losses := [] }

theorem u9370 : Upper (D 7) (R 7) [36,264,18,34,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9371 : Route 9 := (fun mask => (mask,id))

def c9371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9371 : Upper (D 7) (R 7) [36,264,18,34,65,128,128] 13 := by
  apply FastRouting.sound _ _ [36,264,18,34,65,128,128] 13 (by decide) (choices 1) [1,64] r9371 c9371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u741
  · exact u742

def b9372 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,7),(3,7),(4,1),(4,6)], upper := (rows 37 266 22 73 145 96 66 160 416), lower := (rows 37 266 22 73 145 96 66 128 256), losses := [] }

theorem u9372 : Upper (D 7) (R 7) [36,264,18,65,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9373 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6)], upper := (rows 37 266 22 73 145 96 96 130 386), lower := (rows 37 266 22 73 145 96 96 128 256), losses := [] }

theorem u9373 : Upper (D 7) (R 7) [36,264,18,65,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9374 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 290, targets := 1 },{ cop := 3, region := 290, targets := 128 },{ cop := 4, region := 72, targets := 2 },{ cop := 4, region := 72, targets := 32 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 266 22 73 145 96 192 162 290), lower := (rows 37 266 22 73 145 96 192 128 256), losses := [] }

theorem u9374 : Upper (D 7) (R 7) [36,264,18,65,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9375 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 105, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 22 73 176 96 65 130 386), lower := (rows 37 266 22 73 176 96 65 128 256), losses := [] }

theorem u9375 : Upper (D 7) (R 7) [36,264,18,65,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9376 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 37 266 22 73 176 96 66 129 385), lower := (rows 37 266 22 73 176 96 66 128 256), losses := [] }

theorem u9376 : Upper (D 7) (R 7) [36,264,18,65,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9377 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 6, region := 48, targets := 3 }], pairs := [(1,5),(3,5),(4,0),(4,1)], upper := (rows 37 266 22 73 176 96 192 131 259), lower := (rows 37 266 22 73 176 96 192 128 256), losses := [] }

theorem u9377 : Upper (D 7) (R 7) [36,264,18,65,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9378 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(4,5)], upper := (rows 37 266 22 74 81 160 65 160 416), lower := (rows 37 266 22 74 81 160 65 128 256), losses := [] }

theorem u9378 : Upper (D 7) (R 7) [36,264,18,66,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9379 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,5)], upper := (rows 37 266 22 74 81 160 96 129 385), lower := (rows 37 266 22 74 81 160 96 128 256), losses := [] }

theorem u9379 : Upper (D 7) (R 7) [36,264,18,66,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9380 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(4,1),(4,5)], upper := (rows 37 266 22 74 81 160 192 161 289), lower := (rows 37 266 22 74 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 224 128 256), good := (rows 85 266 22 74 81 192 192 192 256) }] }

theorem u9380 : Upper (D 7) (R 7) [36,264,18,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9381 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 37 266 22 74 145 96 65 160 416), lower := (rows 37 266 22 74 145 96 65 128 256), losses := [] }

theorem u9381 : Upper (D 7) (R 7) [36,264,18,66,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9382 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 266 22 74 145 96 96 129 385), lower := (rows 37 266 22 74 145 96 96 128 256), losses := [] }

theorem u9382 : Upper (D 7) (R 7) [36,264,18,66,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9383 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,1),(3,0),(4,1),(4,6)], upper := (rows 37 266 22 74 145 96 192 161 289), lower := (rows 37 266 22 74 145 96 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 252 208 128 256), good := (rows 44 298 126 106 240 96 224 224 256) }] }

theorem u9383 : Upper (D 7) (R 7) [36,264,18,66,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9384 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 266 22 104 81 160 65 130 386), lower := (rows 37 266 22 104 81 160 65 128 256), losses := [] }

theorem u9384 : Upper (D 7) (R 7) [36,264,18,96,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9385 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 4, region := 168, targets := 2 }], pairs := [(0,1),(0,6),(3,0),(3,1)], upper := (rows 37 266 22 104 81 160 66 129 385), lower := (rows 37 266 22 104 81 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 16 160 70 128 256), good := (rows 108 330 86 104 88 160 66 160 256) }] }

theorem u9385 : Upper (D 7) (R 7) [36,264,18,96,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9386 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 22 104 81 160 192 131 259), lower := (rows 37 266 22 104 81 160 192 128 256), losses := [] }

theorem u9386 : Upper (D 7) (R 7) [36,264,18,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9387 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 266 22 104 208 33 65 130 386), lower := (rows 37 266 22 104 208 33 65 128 256), losses := [] }

theorem u9387 : Upper (D 7) (R 7) [36,264,18,96,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9388 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(3,7)], upper := (rows 37 266 22 104 208 33 66 129 385), lower := (rows 37 266 22 104 208 33 66 128 256), losses := [] }

theorem u9388 : Upper (D 7) (R 7) [36,264,18,96,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9389 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 22 104 208 33 192 131 259), lower := (rows 37 266 22 104 208 33 192 128 256), losses := [] }

theorem u9389 : Upper (D 7) (R 7) [36,264,18,96,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9390 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 266 22 200 81 160 65 162 290), lower := (rows 37 266 22 200 81 160 65 128 256), losses := [] }

theorem u9390 : Upper (D 7) (R 7) [36,264,18,192,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9391 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 4, region := 168, targets := 2 }], pairs := [(0,1),(0,6),(3,1),(4,5)], upper := (rows 37 266 22 200 81 160 66 161 289), lower := (rows 37 266 22 200 81 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 70 128 256), good := (rows 85 330 86 200 81 128 66 128 256) }] }

theorem u9391 : Upper (D 7) (R 7) [36,264,18,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9392 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 266 22 200 81 160 96 131 259), lower := (rows 37 266 22 200 81 160 96 128 256), losses := [] }

theorem u9392 : Upper (D 7) (R 7) [36,264,18,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9393 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 173, targets := 2 },{ cop := 1, region := 80, targets := 32 }], pairs := [(0,1),(2,1),(3,1),(4,5)], upper := (rows 37 266 69 25 82 160 66 160 416), lower := (rows 37 266 69 25 82 160 66 128 256), losses := [] }

theorem u9393 : Upper (D 7) (R 7) [36,264,65,17,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9394 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 25 82 160 96 130 386), lower := (rows 37 266 69 25 82 160 96 128 256), losses := [] }

theorem u9394 : Upper (D 7) (R 7) [36,264,65,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9395 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 266 69 25 82 160 192 162 290), lower := (rows 37 266 69 25 82 160 192 128 256), losses := [] }

theorem u9395 : Upper (D 7) (R 7) [36,264,65,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9396 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 6, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 266 69 25 146 160 66 224 352), lower := (rows 37 266 69 25 146 160 66 128 256), losses := [] }

theorem u9396 : Upper (D 7) (R 7) [36,264,65,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9397 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 25 146 160 96 194 322), lower := (rows 37 266 69 25 146 160 96 128 256), losses := [] }

theorem u9397 : Upper (D 7) (R 7) [36,264,65,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9398 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 266 69 25 208 34 66 160 416), lower := (rows 37 266 69 25 208 34 66 128 256), losses := [] }

theorem u9398 : Upper (D 7) (R 7) [36,264,65,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9399 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 25 208 34 96 130 386), lower := (rows 37 266 69 25 208 34 96 128 256), losses := [] }

theorem u9399 : Upper (D 7) (R 7) [36,264,65,17,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9400 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 69 25 208 34 192 162 290), lower := (rows 37 266 69 25 208 34 192 128 256), losses := [] }

theorem u9400 : Upper (D 7) (R 7) [36,264,65,17,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9401 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 181, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 69 26 145 160 66 224 352), lower := (rows 37 266 69 26 145 160 66 128 256), losses := [] }

theorem u9401 : Upper (D 7) (R 7) [36,264,65,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9402 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 26 145 160 96 194 322), lower := (rows 37 266 69 26 145 160 96 128 256), losses := [] }

theorem u9402 : Upper (D 7) (R 7) [36,264,65,18,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9403 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 266 69 26 208 34 65 160 416), lower := (rows 37 266 69 26 208 34 65 128 256), losses := [] }

theorem u9403 : Upper (D 7) (R 7) [36,264,65,18,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9404 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 266 69 26 208 34 96 129 385), lower := (rows 37 266 69 26 208 34 96 128 256), losses := [] }

theorem u9404 : Upper (D 7) (R 7) [36,264,65,18,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9405 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 69 26 208 34 192 161 289), lower := (rows 37 266 69 26 208 34 192 128 256), losses := [] }

theorem u9405 : Upper (D 7) (R 7) [36,264,65,18,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9406 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 266 69 26 208 160 65 162 290), lower := (rows 37 266 69 26 208 160 65 128 256), losses := [] }

theorem u9406 : Upper (D 7) (R 7) [36,264,65,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9407 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 181, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(4,1)], upper := (rows 37 266 69 26 208 160 66 161 289), lower := (rows 37 266 69 26 208 160 66 128 256), losses := [] }

theorem u9407 : Upper (D 7) (R 7) [36,264,65,18,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9408 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 26 208 160 96 131 259), lower := (rows 37 266 69 26 208 160 96 128 256), losses := [] }

theorem u9408 : Upper (D 7) (R 7) [36,264,65,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9409 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 266 69 42 82 160 65 144 400), lower := (rows 37 266 69 42 82 160 65 128 256), losses := [] }

theorem u9409 : Upper (D 7) (R 7) [36,264,65,34,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9410 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 37 266 69 42 82 160 80 129 385), lower := (rows 37 266 69 42 82 160 80 128 256), losses := [] }

theorem u9410 : Upper (D 7) (R 7) [36,264,65,34,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9410 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9411 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 266 69 42 82 160 192 145 273), lower := (rows 37 266 69 42 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 224 224 128 256), good := (rows 100 282 100 122 122 224 224 224 256) }] }

theorem u9411 : Upper (D 7) (R 7) [36,264,65,34,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9412 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 181, targets := 2 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 266 69 42 145 160 66 208 336), lower := (rows 37 266 69 42 145 160 66 128 256), losses := [] }

theorem u9412 : Upper (D 7) (R 7) [36,264,65,34,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9413 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 266 69 42 145 160 80 194 322), lower := (rows 37 266 69 42 145 160 80 128 256), losses := [] }

theorem u9413 : Upper (D 7) (R 7) [36,264,65,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9413 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9414 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 42 208 160 65 146 274), lower := (rows 37 266 69 42 208 160 65 128 256), losses := [] }

theorem u9414 : Upper (D 7) (R 7) [36,264,65,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9415 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 181, targets := 2 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 266 69 42 208 160 66 145 273), lower := (rows 37 266 69 42 208 160 66 128 256), losses := [] }

theorem u9415 : Upper (D 7) (R 7) [36,264,65,34,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9416 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 69 42 208 160 80 131 259), lower := (rows 37 266 69 42 208 160 80 128 256), losses := [] }

theorem u9416 : Upper (D 7) (R 7) [36,264,65,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9416 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9417 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 56 82 160 65 130 386), lower := (rows 37 266 69 56 82 160 65 128 256), losses := [] }

theorem u9417 : Upper (D 7) (R 7) [36,264,65,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9418 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 266 69 56 82 160 66 129 385), lower := (rows 37 266 69 56 82 160 66 128 256), losses := [] }

theorem u9418 : Upper (D 7) (R 7) [36,264,65,48,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9419 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(3,1)], upper := (rows 37 266 69 56 82 160 192 131 259), lower := (rows 37 266 69 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 100 266 100 120 122 224 224 224 256) },{ target := 1, region := (rows 253 0 253 24 16 224 224 128 256), good := (rows 101 269 101 125 125 229 229 229 256) }] }

theorem u9419 : Upper (D 7) (R 7) [36,264,65,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9419
end Delivery.IrregularNine14.P07
