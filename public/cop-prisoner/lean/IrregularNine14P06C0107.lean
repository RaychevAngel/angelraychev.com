import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0007

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6420 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 70 25 276 96 96 140 268), lower := (rows 35 131 70 25 276 96 96 128 256), losses := [] }

theorem u6420 : Upper (D 6) (R 6) [34,129,66,17,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6421 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,5)], upper := (rows 35 131 70 25 336 36 68 168 296), lower := (rows 35 131 70 25 336 36 68 128 256), losses := [] }

theorem u6421 : Upper (D 6) (R 6) [34,129,66,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6422 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 70 25 336 36 72 164 292), lower := (rows 35 131 70 25 336 36 72 128 256), losses := [] }

theorem u6422 : Upper (D 6) (R 6) [34,129,66,17,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6422 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6423 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 35 131 70 25 336 36 96 140 268), lower := (rows 35 131 70 25 336 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 47 111 136 264), good := (rows 102 230 102 508 336 100 96 128 256) }] }

theorem u6423 : Upper (D 6) (R 6) [34,129,66,17,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6424 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 387, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 70 28 81 36 72 416 288), lower := (rows 35 131 70 28 81 36 72 128 256), losses := [] }

theorem u6424 : Upper (D 6) (R 6) [34,129,66,20,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6424 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6425 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 131 70 28 81 36 96 392 264), lower := (rows 35 131 70 28 81 36 96 128 256), losses := [] }

theorem u6425 : Upper (D 6) (R 6) [34,129,66,20,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6426 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 28 81 36 320 168 296), lower := (rows 35 131 70 28 81 36 320 128 256), losses := [] }

theorem u6426 : Upper (D 6) (R 6) [34,129,66,20,65,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6426 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6427 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1)], upper := (rows 35 131 70 28 273 36 72 224 352), lower := (rows 35 131 70 28 273 36 72 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 19 44 108 237 365), good := (rows 497 401 508 508 401 492 488 128 256) }] }

theorem u6427 : Upper (D 6) (R 6) [34,129,66,20,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6427 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6428 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0)], upper := (rows 35 131 70 28 273 36 96 200 328), lower := (rows 35 131 70 28 273 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 127 152 280), good := (rows 102 230 102 508 508 100 96 128 256) }] }

theorem u6428 : Upper (D 6) (R 6) [34,129,66,20,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6429 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,5)], upper := (rows 35 131 70 28 273 96 68 168 296), lower := (rows 35 131 70 28 273 96 68 128 256), losses := [] }

theorem u6429 : Upper (D 6) (R 6) [34,129,66,20,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6430 : Route 9 := (fun mask => (mask,id))

def c6430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6430 : Upper (D 6) (R 6) [34,129,66,20,257,64,8] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,257,64,8] 13 (by decide) (choices 1) [4,32] r6430 c6430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u473
  · exact u474

def b6431 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 70 28 273 96 96 140 268), lower := (rows 35 131 70 28 273 96 96 128 256), losses := [] }

theorem u6431 : Upper (D 6) (R 6) [34,129,66,20,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6432 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 28 280 96 65 164 292), lower := (rows 35 131 70 28 280 96 65 128 256), losses := [] }

theorem u6432 : Upper (D 6) (R 6) [34,129,66,20,264,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6433 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 28 280 96 68 161 289), lower := (rows 35 131 70 28 280 96 68 128 256), losses := [] }

theorem u6433 : Upper (D 6) (R 6) [34,129,66,20,264,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6434 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 70 28 280 96 96 133 261), lower := (rows 35 131 70 28 280 96 96 128 256), losses := [] }

theorem u6434 : Upper (D 6) (R 6) [34,129,66,20,264,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6435 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 28 304 36 65 200 328), lower := (rows 35 131 70 28 304 36 65 128 256), losses := [] }

theorem u6435 : Upper (D 6) (R 6) [34,129,66,20,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6436 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1)], upper := (rows 35 131 70 28 304 36 72 193 321), lower := (rows 35 131 70 28 304 36 72 128 256), losses := [{ target := 1, region := (rows 1 0 4 44 21 44 125 131 259), good := (rows 505 465 508 124 376 124 104 128 256) }] }

theorem u6436 : Upper (D 6) (R 6) [34,129,66,20,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6436 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6437 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 28 304 96 65 140 268), lower := (rows 35 131 70 28 304 96 65 128 256), losses := [] }

theorem u6437 : Upper (D 6) (R 6) [34,129,66,20,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6438 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,5)], upper := (rows 35 131 70 28 304 96 68 137 265), lower := (rows 35 131 70 28 304 96 68 128 256), losses := [] }

theorem u6438 : Upper (D 6) (R 6) [34,129,66,20,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6439 : Route 9 := (fun mask => (mask,id))

def c6439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6439 : Upper (D 6) (R 6) [34,129,66,20,288,64,8] 13 := by
  apply FastRouting.sound _ _ [34,129,66,20,288,64,8] 13 (by decide) (choices 1) [1,4] r6439 c6439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u475
  · exact u476

def b6440 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 28 336 36 65 168 296), lower := (rows 35 131 70 28 336 36 65 128 256), losses := [] }

theorem u6440 : Upper (D 6) (R 6) [34,129,66,20,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6441 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 70 28 336 36 72 161 289), lower := (rows 35 131 70 28 336 36 72 128 256), losses := [] }

theorem u6441 : Upper (D 6) (R 6) [34,129,66,20,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6441 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6442 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 70 28 336 36 96 137 265), lower := (rows 35 131 70 28 336 36 96 128 256), losses := [] }

theorem u6442 : Upper (D 6) (R 6) [34,129,66,20,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6443 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 70 44 81 288 68 152 280), lower := (rows 35 131 70 44 81 288 68 128 256), losses := [] }

theorem u6443 : Upper (D 6) (R 6) [34,129,66,36,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6443 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6444 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 35 131 70 44 81 288 72 148 276), lower := (rows 35 131 70 44 81 288 72 128 256), losses := [] }

theorem u6444 : Upper (D 6) (R 6) [34,129,66,36,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6444 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6445 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 35 131 70 44 81 288 80 140 268), lower := (rows 35 131 70 44 81 288 80 128 256), losses := [] }

theorem u6445 : Upper (D 6) (R 6) [34,129,66,36,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6445 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6446 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 44 88 288 65 148 276), lower := (rows 35 131 70 44 88 288 65 128 256), losses := [] }

theorem u6446 : Upper (D 6) (R 6) [34,129,66,36,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6446 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6447 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 70 44 88 288 68 145 273), lower := (rows 35 131 70 44 88 288 68 128 256), losses := [] }

theorem u6447 : Upper (D 6) (R 6) [34,129,66,36,72,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6447 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6448 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 131 70 44 88 288 80 133 261), lower := (rows 35 131 70 44 88 288 80 128 256), losses := [] }

theorem u6448 : Upper (D 6) (R 6) [34,129,66,36,72,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6448 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6449 : PairBound 9 := { available := 264, camps := [{ cop := 3, region := 387, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 56 81 36 68 392 264), lower := (rows 35 131 70 56 81 36 68 128 256), losses := [] }

theorem u6449 : Upper (D 6) (R 6) [34,129,66,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6450 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 70 56 81 36 72 388 260), lower := (rows 35 131 70 56 81 36 72 128 256), losses := [] }

theorem u6450 : Upper (D 6) (R 6) [34,129,66,48,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6450 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6451 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1)], upper := (rows 35 131 70 56 81 36 320 140 268), lower := (rows 35 131 70 56 81 36 320 128 256), losses := [{ target := 1, region := (rows 1 0 4 13 19 36 365 164 292), good := (rows 505 217 508 504 89 492 320 128 320) }] }

theorem u6451 : Upper (D 6) (R 6) [34,129,66,48,65,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6451 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6452 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 131 70 56 81 288 68 140 268), lower := (rows 35 131 70 56 81 288 68 128 256), losses := [] }

theorem u6452 : Upper (D 6) (R 6) [34,129,66,48,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6452 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6453 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 88, targets := 2 }], pairs := [(3,1)], upper := (rows 35 131 70 56 81 288 72 132 260), lower := (rows 35 131 70 56 81 288 72 128 256), losses := [] }

theorem u6453 : Upper (D 6) (R 6) [34,129,66,48,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6453 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6454 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,5)], upper := (rows 35 131 70 56 273 36 68 200 328), lower := (rows 35 131 70 56 273 36 68 128 256), losses := [] }

theorem u6454 : Upper (D 6) (R 6) [34,129,66,48,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6455 : Route 9 := (fun mask => (mask,id))

def c6455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6455 : Upper (D 6) (R 6) [34,129,66,48,257,4,8] 13 := by
  apply FastRouting.sound _ _ [34,129,66,48,257,4,8] 13 (by decide) (choices 1) [4,64] r6455 c6455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u477
  · exact u478

def b6456 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,5)], upper := (rows 35 131 70 56 273 96 68 140 268), lower := (rows 35 131 70 56 273 96 68 128 256), losses := [] }

theorem u6456 : Upper (D 6) (R 6) [34,129,66,48,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6457 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 56 273 96 72 132 260), lower := (rows 35 131 70 56 273 96 72 128 256), losses := [] }

theorem u6457 : Upper (D 6) (R 6) [34,129,66,48,257,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6457 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6458 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 56 336 36 65 140 268), lower := (rows 35 131 70 56 336 36 65 128 256), losses := [] }

theorem u6458 : Upper (D 6) (R 6) [34,129,66,48,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6459 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 56 336 36 68 137 265), lower := (rows 35 131 70 56 336 36 68 128 256), losses := [] }

theorem u6459 : Upper (D 6) (R 6) [34,129,66,48,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6460 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 56 336 36 72 133 261), lower := (rows 35 131 70 56 336 36 72 128 256), losses := [] }

theorem u6460 : Upper (D 6) (R 6) [34,129,66,48,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6460 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6461 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 76, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 131 70 73 276 48 68 168 296), lower := (rows 35 131 70 73 276 48 68 128 256), losses := [] }

theorem u6461 : Upper (D 6) (R 6) [34,129,66,65,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6461 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6462 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 131 70 73 276 48 72 164 292), lower := (rows 35 131 70 73 276 48 72 128 256), losses := [] }

theorem u6462 : Upper (D 6) (R 6) [34,129,66,65,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6462 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6463 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 134, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 73 276 48 96 140 268), lower := (rows 35 131 70 73 276 48 96 128 256), losses := [] }

theorem u6463 : Upper (D 6) (R 6) [34,129,66,65,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6463 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6464 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(3,5)], upper := (rows 35 131 70 73 280 36 68 176 304), lower := (rows 35 131 70 73 280 36 68 128 256), losses := [] }

theorem u6464 : Upper (D 6) (R 6) [34,129,66,65,264,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6465 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 73 280 36 80 164 292), lower := (rows 35 131 70 73 280 36 80 128 256), losses := [] }

theorem u6465 : Upper (D 6) (R 6) [34,129,66,65,264,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6465 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6466 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 131 70 73 280 36 96 148 276), lower := (rows 35 131 70 73 280 36 96 128 256), losses := [] }

theorem u6466 : Upper (D 6) (R 6) [34,129,66,65,264,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6467 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 76, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(3,5)], upper := (rows 35 131 70 73 304 36 68 152 280), lower := (rows 35 131 70 73 304 36 68 128 256), losses := [] }

theorem u6467 : Upper (D 6) (R 6) [34,129,66,65,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6468 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 73 304 36 72 148 276), lower := (rows 35 131 70 73 304 36 72 128 256), losses := [] }

theorem u6468 : Upper (D 6) (R 6) [34,129,66,65,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6468 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6469 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 134, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 73 304 36 80 140 268), lower := (rows 35 131 70 73 304 36 80 128 256), losses := [] }

theorem u6469 : Upper (D 6) (R 6) [34,129,66,65,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6469 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6470 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,5)], upper := (rows 35 131 70 88 273 36 68 168 296), lower := (rows 35 131 70 88 273 36 68 128 256), losses := [] }

theorem u6470 : Upper (D 6) (R 6) [34,129,66,80,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6471 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 88 273 36 72 164 292), lower := (rows 35 131 70 88 273 36 72 128 256), losses := [] }

theorem u6471 : Upper (D 6) (R 6) [34,129,66,80,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6471 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6472 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0)], upper := (rows 35 131 70 88 273 36 96 140 268), lower := (rows 35 131 70 88 273 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 127 144 272), good := (rows 102 230 102 504 508 100 96 128 256) }] }

theorem u6472 : Upper (D 6) (R 6) [34,129,66,80,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6473 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 88 276 36 65 168 296), lower := (rows 35 131 70 88 276 36 65 128 256), losses := [] }

theorem u6473 : Upper (D 6) (R 6) [34,129,66,80,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6474 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 70 88 276 36 72 161 289), lower := (rows 35 131 70 88 276 36 72 128 256), losses := [] }

theorem u6474 : Upper (D 6) (R 6) [34,129,66,80,260,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6474 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6475 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 35 131 70 88 276 36 96 137 265), lower := (rows 35 131 70 88 276 36 96 128 256), losses := [] }

theorem u6475 : Upper (D 6) (R 6) [34,129,66,80,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6476 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 88 276 40 65 164 292), lower := (rows 35 131 70 88 276 40 65 128 256), losses := [] }

theorem u6476 : Upper (D 6) (R 6) [34,129,66,80,260,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6476 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6477 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 70 88 276 40 68 161 289), lower := (rows 35 131 70 88 276 40 68 128 256), losses := [] }

theorem u6477 : Upper (D 6) (R 6) [34,129,66,80,260,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6477 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6478 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 88 276 40 96 133 261), lower := (rows 35 131 70 88 276 40 96 128 256), losses := [] }

theorem u6478 : Upper (D 6) (R 6) [34,129,66,80,260,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6478 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6479 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 88 280 36 65 164 292), lower := (rows 35 131 70 88 280 36 65 128 256), losses := [] }

theorem u6479 : Upper (D 6) (R 6) [34,129,66,80,264,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6479
end Delivery.IrregularNine14.P06
