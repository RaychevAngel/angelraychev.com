import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3480 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 164 268 84 33 65 146 274), lower := (rows 11 98 164 268 84 33 65 128 256), losses := [] }

theorem u3480 : Upper (D 6) (R 6) [10,96,160,260,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3481 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 82, targets := 1 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 11 98 164 268 84 33 66 145 273), lower := (rows 11 98 164 268 84 33 66 128 256), losses := [] }

theorem u3481 : Upper (D 6) (R 6) [10,96,160,260,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3482 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 268 84 33 80 131 259), lower := (rows 11 98 164 268 84 33 80 128 256), losses := [] }

theorem u3482 : Upper (D 6) (R 6) [10,96,160,260,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3482 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3483 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 164 268 84 34 65 145 273), lower := (rows 11 98 164 268 84 34 65 128 256), losses := [] }

theorem u3483 : Upper (D 6) (R 6) [10,96,160,260,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3484 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 268 84 34 80 129 257), lower := (rows 11 98 164 268 84 34 80 128 256), losses := [] }

theorem u3484 : Upper (D 6) (R 6) [10,96,160,260,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3484 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3485 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 164 280 84 33 65 134 262), lower := (rows 11 98 164 280 84 33 65 128 256), losses := [] }

theorem u3485 : Upper (D 6) (R 6) [10,96,160,272,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3486 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 164 280 84 33 66 133 261), lower := (rows 11 98 164 280 84 33 66 128 256), losses := [] }

theorem u3486 : Upper (D 6) (R 6) [10,96,160,272,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3487 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 164 280 84 33 68 131 259), lower := (rows 11 98 164 280 84 33 68 128 256), losses := [] }

theorem u3487 : Upper (D 6) (R 6) [10,96,160,272,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3488 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 388 44 84 33 65 146 274), lower := (rows 11 98 388 44 84 33 65 128 256), losses := [] }

theorem u3488 : Upper (D 6) (R 6) [10,96,384,36,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3489 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 388 44 84 33 66 145 273), lower := (rows 11 98 388 44 84 33 66 128 256), losses := [] }

theorem u3489 : Upper (D 6) (R 6) [10,96,384,36,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3490 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 388 44 84 33 80 131 259), lower := (rows 11 98 388 44 84 33 80 128 256), losses := [] }

theorem u3490 : Upper (D 6) (R 6) [10,96,384,36,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3490 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3491 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5),(3,1)], upper := (rows 11 131 22 44 304 96 65 196 324), lower := (rows 11 131 22 44 304 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 28 103 67 132 260), good := (rows 121 225 508 444 304 96 97 128 256) }] }

theorem u3491 : Upper (D 6) (R 6) [10,129,18,36,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3492 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(3,0),(3,1)], upper := (rows 11 131 22 44 304 96 68 193 321), lower := (rows 11 131 22 44 304 96 68 128 256), losses := [] }

theorem u3492 : Upper (D 6) (R 6) [10,129,18,36,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3493 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0)], upper := (rows 11 131 22 104 52 288 65 196 324), lower := (rows 11 131 22 104 52 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 72 81 360 64 192 320), good := (rows 62 150 22 504 52 288 508 128 288) }] }

theorem u3493 : Upper (D 6) (R 6) [10,129,18,96,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3493 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3494 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 22 104 52 288 68 193 321), lower := (rows 11 131 22 104 52 288 68 128 256), losses := [] }

theorem u3494 : Upper (D 6) (R 6) [10,129,18,96,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3494 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3495 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 403, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 22 104 273 36 68 224 352), lower := (rows 11 131 22 104 273 36 68 128 256), losses := [] }

theorem u3495 : Upper (D 6) (R 6) [10,129,18,96,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3496 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 22 104 273 36 96 196 324), lower := (rows 11 131 22 104 273 36 96 128 256), losses := [] }

theorem u3496 : Upper (D 6) (R 6) [10,129,18,96,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3497 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 22 104 276 33 68 224 352), lower := (rows 11 131 22 104 276 33 68 128 256), losses := [] }

theorem u3497 : Upper (D 6) (R 6) [10,129,18,96,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3498 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 22 104 276 33 96 196 324), lower := (rows 11 131 22 104 276 33 96 128 256), losses := [] }

theorem u3498 : Upper (D 6) (R 6) [10,129,18,96,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3499 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 22 104 304 36 65 196 324), lower := (rows 11 131 22 104 304 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 5 72 88 103 64 192 320), good := (rows 62 166 54 504 304 36 508 128 256) }] }

theorem u3499 : Upper (D 6) (R 6) [10,129,18,96,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3500 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 403, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 22 104 304 36 68 193 321), lower := (rows 11 131 22 104 304 36 68 128 256), losses := [] }

theorem u3500 : Upper (D 6) (R 6) [10,129,18,96,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3501 : PairBound 9 := { available := 96, camps := [], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 22 268 112 33 68 224 352), lower := (rows 11 131 22 268 112 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 76 144 272), good := (rows 74 130 478 332 496 32 76 128 256) },{ target := 1, region := (rows 1 0 4 76 21 35 76 149 277), good := (rows 505 433 508 476 504 433 476 128 256) }] }

theorem u3501 : Upper (D 6) (R 6) [10,129,18,260,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3502 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 22 268 112 33 96 196 324), lower := (rows 11 131 22 268 112 33 96 128 256), losses := [] }

theorem u3502 : Upper (D 6) (R 6) [10,129,18,260,96,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3503 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 22 268 112 36 96 193 321), lower := (rows 11 131 22 268 112 36 96 128 256), losses := [] }

theorem u3503 : Upper (D 6) (R 6) [10,129,18,260,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3504 : Route 9 := (fun mask => (mask,id))

def c3504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3504 : Upper (D 6) (R 6) [10,129,18,288,36,64,1] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,36,64,1] 13 (by decide) (choices 1) [4,64] r3504 c3504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u250
  · exact u251

def b3505 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 22 296 52 96 68 193 321), lower := (rows 11 131 22 296 52 96 68 128 256), losses := [] }

theorem u3505 : Upper (D 6) (R 6) [10,129,18,288,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3506 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 360, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 131 22 296 81 36 68 224 352), lower := (rows 11 131 22 296 81 36 68 128 256), losses := [] }

theorem u3506 : Upper (D 6) (R 6) [10,129,18,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3507 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 360, targets := 3 },{ cop := 4, region := 134, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 131 22 296 81 36 96 196 324), lower := (rows 11 131 22 296 81 36 96 128 256), losses := [] }

theorem u3507 : Upper (D 6) (R 6) [10,129,18,288,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3508 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 360, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 131 22 296 81 96 68 164 292), lower := (rows 11 131 22 296 81 96 68 128 256), losses := [] }

theorem u3508 : Upper (D 6) (R 6) [10,129,18,288,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3509 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 134, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 11 131 22 296 81 96 96 132 260), lower := (rows 11 131 22 296 81 96 96 128 256), losses := [] }

theorem u3509 : Upper (D 6) (R 6) [10,129,18,288,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3510 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 11 131 22 296 84 33 68 224 352), lower := (rows 11 131 22 296 84 33 68 128 256), losses := [] }

theorem u3510 : Upper (D 6) (R 6) [10,129,18,288,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3511 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 22 296 84 33 96 196 324), lower := (rows 11 131 22 296 84 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 7 104 49 32 104 177 305), good := (rows 478 406 406 504 476 508 504 128 256) }] }

theorem u3511 : Upper (D 6) (R 6) [10,129,18,288,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3512 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 296, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 131 22 296 84 96 65 164 292), lower := (rows 11 131 22 296 84 96 65 128 256), losses := [] }

theorem u3512 : Upper (D 6) (R 6) [10,129,18,288,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3513 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 22 296 84 96 68 161 289), lower := (rows 11 131 22 296 84 96 68 128 256), losses := [] }

theorem u3513 : Upper (D 6) (R 6) [10,129,18,288,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3514 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 22 296 84 96 96 133 261), lower := (rows 11 131 22 296 84 96 96 128 256), losses := [] }

theorem u3514 : Upper (D 6) (R 6) [10,129,18,288,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3515 : Route 9 := (fun mask => (mask,id))

def c3515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3515 : Upper (D 6) (R 6) [10,129,18,288,96,4,1] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,96,4,1] 13 (by decide) (choices 1) [4,64] r3515 c3515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u252
  · exact u253

def b3516 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 22 296 112 36 68 193 321), lower := (rows 11 131 22 296 112 36 68 128 256), losses := [] }

theorem u3516 : Upper (D 6) (R 6) [10,129,18,288,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3517 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5),(3,0)], upper := (rows 11 131 37 28 304 96 66 196 324), lower := (rows 11 131 37 28 304 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 28 103 67 132 260), good := (rows 122 226 508 444 304 96 98 128 256) }] }

theorem u3517 : Upper (D 6) (R 6) [10,129,33,20,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3518 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 11 131 37 28 304 96 68 194 322), lower := (rows 11 131 37 28 304 96 68 128 256), losses := [] }

theorem u3518 : Upper (D 6) (R 6) [10,129,33,20,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3519 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 131 37 28 336 96 66 164 292), lower := (rows 11 131 37 28 336 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 21 119 67 140 268), good := (rows 506 242 508 444 368 96 98 128 256) }] }

theorem u3519 : Upper (D 6) (R 6) [10,129,33,20,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3520 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 130, targets := 4 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 11 131 37 28 336 96 68 162 290), lower := (rows 11 131 37 28 336 96 68 128 256), losses := [] }

theorem u3520 : Upper (D 6) (R 6) [10,129,33,20,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3521 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 37 28 336 96 96 134 262), lower := (rows 11 131 37 28 336 96 96 128 256), losses := [] }

theorem u3521 : Upper (D 6) (R 6) [10,129,33,20,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3522 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 76 82 288 68 176 304), lower := (rows 11 131 37 76 82 288 68 128 256), losses := [] }

theorem u3522 : Upper (D 6) (R 6) [10,129,33,68,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3522 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3523 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 11 131 37 76 82 288 80 164 292), lower := (rows 11 131 37 76 82 288 80 128 256), losses := [] }

theorem u3523 : Upper (D 6) (R 6) [10,129,33,68,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3523 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3524 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 76 82 288 96 148 276), lower := (rows 11 131 37 76 82 288 96 128 256), losses := [] }

theorem u3524 : Upper (D 6) (R 6) [10,129,33,68,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3524 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3525 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 131 37 76 112 288 66 148 276), lower := (rows 11 131 37 76 112 288 66 128 256), losses := [] }

theorem u3525 : Upper (D 6) (R 6) [10,129,33,68,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3525 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3526 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 76 112 288 68 146 274), lower := (rows 11 131 37 76 112 288 68 128 256), losses := [] }

theorem u3526 : Upper (D 6) (R 6) [10,129,33,68,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3526 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3527 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 11 131 37 76 112 288 80 134 262), lower := (rows 11 131 37 76 112 288 80 128 256), losses := [] }

theorem u3527 : Upper (D 6) (R 6) [10,129,33,68,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3527 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3528 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 360, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 268 22 96 80 224 352), lower := (rows 11 131 37 268 22 96 80 128 256), losses := [] }

theorem u3528 : Upper (D 6) (R 6) [10,129,33,260,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3528 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3529 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 37 268 22 96 96 208 336), lower := (rows 11 131 37 268 22 96 96 128 256), losses := [] }

theorem u3529 : Upper (D 6) (R 6) [10,129,33,260,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3530 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 131 37 268 50 96 68 208 336), lower := (rows 11 131 37 268 50 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 19 109 76 133 261), good := (rows 506 434 508 492 50 104 492 128 256) }] }

theorem u3530 : Upper (D 6) (R 6) [10,129,33,260,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3531 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 112, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 131 37 268 50 96 80 196 324), lower := (rows 11 131 37 268 50 96 80 128 256), losses := [] }

theorem u3531 : Upper (D 6) (R 6) [10,129,33,260,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3531 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3532 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 131 37 268 82 96 68 176 304), lower := (rows 11 131 37 268 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 17 125 76 151 279), good := (rows 506 434 508 492 506 104 492 128 256) }] }

theorem u3532 : Upper (D 6) (R 6) [10,129,33,260,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3533 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 268 82 96 80 164 292), lower := (rows 11 131 37 268 82 96 80 128 256), losses := [] }

theorem u3533 : Upper (D 6) (R 6) [10,129,33,260,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3533 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3534 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 11 131 37 268 82 96 96 148 276), lower := (rows 11 131 37 268 82 96 96 128 256), losses := [] }

theorem u3534 : Upper (D 6) (R 6) [10,129,33,260,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3535 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 37 268 84 96 66 176 304), lower := (rows 11 131 37 268 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 119 67 156 284), good := (rows 490 226 508 444 508 96 98 128 256) }] }

theorem u3535 : Upper (D 6) (R 6) [10,129,33,260,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3536 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 268 84 96 80 162 290), lower := (rows 11 131 37 268 84 96 80 128 256), losses := [] }

theorem u3536 : Upper (D 6) (R 6) [10,129,33,260,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3536 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3537 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 37 268 84 96 96 146 274), lower := (rows 11 131 37 268 84 96 96 128 256), losses := [] }

theorem u3537 : Upper (D 6) (R 6) [10,129,33,260,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3538 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 131 37 296 82 96 68 148 276), lower := (rows 11 131 37 296 82 96 68 128 256), losses := [] }

theorem u3538 : Upper (D 6) (R 6) [10,129,33,288,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3539 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 296 82 96 80 132 260), lower := (rows 11 131 37 296 82 96 80 128 256), losses := [] }

theorem u3539 : Upper (D 6) (R 6) [10,129,33,288,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3539 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3539
end Delivery.IrregularNine14.P06
