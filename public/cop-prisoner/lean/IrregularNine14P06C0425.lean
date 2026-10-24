import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0131

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25500 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 328 84 33 70 134 262), lower := (rows 41 50 133 328 84 33 64 128 256), losses := [] }

theorem u25500 : Upper (D 6) (R 6) [40,48,129,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25501 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 133 328 84 34 71 135 263), lower := (rows 41 50 133 328 84 34 64 128 256), losses := [] }

theorem u25501 : Upper (D 6) (R 6) [40,48,129,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25502 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 133 328 84 36 67 131 259), lower := (rows 41 50 133 328 84 36 64 128 256), losses := [] }

theorem u25502 : Upper (D 6) (R 6) [40,48,129,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25503 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 196 13 82 33 326 390 262), lower := (rows 41 50 196 13 82 33 64 128 256), losses := [] }

theorem u25503 : Upper (D 6) (R 6) [40,48,192,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25504 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 196 13 82 34 325 389 261), lower := (rows 41 50 196 13 82 34 64 128 256), losses := [] }

theorem u25504 : Upper (D 6) (R 6) [40,48,192,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25505 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 50 196 13 82 36 323 387 259), lower := (rows 41 50 196 13 82 36 64 128 256), losses := [] }

theorem u25505 : Upper (D 6) (R 6) [40,48,192,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25506 : Route 9 := (fun mask => (mask,id))

def c25506 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25506 : Upper (D 6) (R 6) [40,48,192,5,66,256] 13 := by
  apply FastRouting.sound _ _ [40,48,192,5,66,256] 13 (by decide) (choices 1) [1,2,4] r25506 c25506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7884
  · exact u7885
  · exact u7886

def b25507 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 196 13 274 33 70 198 326), lower := (rows 41 50 196 13 274 33 64 128 256), losses := [] }

theorem u25507 : Upper (D 6) (R 6) [40,48,192,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25508 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 50, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 196 13 274 34 69 197 325), lower := (rows 41 50 196 13 274 34 64 128 256), losses := [] }

theorem u25508 : Upper (D 6) (R 6) [40,48,192,5,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25509 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 50 196 13 274 36 67 195 323), lower := (rows 41 50 196 13 274 36 64 128 256), losses := [] }

theorem u25509 : Upper (D 6) (R 6) [40,48,192,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25510 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 50 196 13 274 96 71 135 263), lower := (rows 41 50 196 13 274 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 100 64 128 256), good := (rows 41 50 224 41 274 96 96 128 256) }] }

theorem u25510 : Upper (D 6) (R 6) [40,48,192,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25511 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 196 13 276 33 66 194 322), lower := (rows 41 50 196 13 276 33 64 128 256), losses := [] }

theorem u25511 : Upper (D 6) (R 6) [40,48,192,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25512 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 50 196 13 276 34 67 195 323), lower := (rows 41 50 196 13 276 34 64 128 256), losses := [] }

theorem u25512 : Upper (D 6) (R 6) [40,48,192,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25513 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 41 50 196 13 276 96 67 131 259), lower := (rows 41 50 196 13 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 64 128 256), good := (rows 40 50 228 44 310 96 96 128 256) }] }

theorem u25513 : Upper (D 6) (R 6) [40,48,192,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25514 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 196 13 336 33 70 134 262), lower := (rows 41 50 196 13 336 33 64 128 256), losses := [] }

theorem u25514 : Upper (D 6) (R 6) [40,48,192,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25515 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 196 13 336 34 71 135 263), lower := (rows 41 50 196 13 336 34 64 128 256), losses := [] }

theorem u25515 : Upper (D 6) (R 6) [40,48,192,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25516 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 50 196 13 336 36 67 131 259), lower := (rows 41 50 196 13 336 36 64 128 256), losses := [] }

theorem u25516 : Upper (D 6) (R 6) [40,48,192,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25517 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 50 196 14 81 33 326 390 262), lower := (rows 41 50 196 14 81 33 64 128 256), losses := [] }

theorem u25517 : Upper (D 6) (R 6) [40,48,192,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25518 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 196 14 81 34 325 389 261), lower := (rows 41 50 196 14 81 34 64 128 256), losses := [] }

theorem u25518 : Upper (D 6) (R 6) [40,48,192,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25519 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 196 14 81 36 323 387 259), lower := (rows 41 50 196 14 81 36 64 128 256), losses := [] }

theorem u25519 : Upper (D 6) (R 6) [40,48,192,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25520 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 289, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 50 196 14 81 288 71 135 263), lower := (rows 41 50 196 14 81 288 64 128 256), losses := [{ target := 6, region := (rows 9 18 4 8 16 297 0 136 264), good := (rows 425 50 132 431 51 288 0 128 288) }] }

theorem u25520 : Upper (D 6) (R 6) [40,48,192,6,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25520 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25521 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 50 196 14 273 33 70 198 326), lower := (rows 41 50 196 14 273 33 64 128 256), losses := [] }

theorem u25521 : Upper (D 6) (R 6) [40,48,192,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25522 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 196 14 273 34 69 197 325), lower := (rows 41 50 196 14 273 34 64 128 256), losses := [] }

theorem u25522 : Upper (D 6) (R 6) [40,48,192,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25523 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 196 14 273 36 67 195 323), lower := (rows 41 50 196 14 273 36 64 128 256), losses := [] }

theorem u25523 : Upper (D 6) (R 6) [40,48,192,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25524 : Route 9 := (fun mask => (mask,id))

def c25524 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25524 : Upper (D 6) (R 6) [40,48,192,6,257,64] 13 := by
  apply FastRouting.sound _ _ [40,48,192,6,257,64] 13 (by decide) (choices 1) [1,2,4] r25524 c25524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7887
  · exact u7888
  · exact u7889

def b25525 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 50 196 14 276 33 67 195 323), lower := (rows 41 50 196 14 276 33 64 128 256), losses := [] }

theorem u25525 : Upper (D 6) (R 6) [40,48,192,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25526 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 196 14 276 34 65 193 321), lower := (rows 41 50 196 14 276 34 64 128 256), losses := [] }

theorem u25526 : Upper (D 6) (R 6) [40,48,192,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25527 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(3,0)], upper := (rows 41 50 196 14 276 96 67 131 259), lower := (rows 41 50 196 14 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 100 64 128 256), good := (rows 40 58 228 46 318 96 96 128 256) }] }

theorem u25527 : Upper (D 6) (R 6) [40,48,192,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25528 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 196 14 336 33 71 135 263), lower := (rows 41 50 196 14 336 33 64 128 256), losses := [] }

theorem u25528 : Upper (D 6) (R 6) [40,48,192,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25529 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 196 14 336 34 69 133 261), lower := (rows 41 50 196 14 336 34 64 128 256), losses := [] }

theorem u25529 : Upper (D 6) (R 6) [40,48,192,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25530 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 196 14 336 36 67 131 259), lower := (rows 41 50 196 14 336 36 64 128 256), losses := [] }

theorem u25530 : Upper (D 6) (R 6) [40,48,192,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25531 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 196 73 274 33 70 134 262), lower := (rows 41 50 196 73 274 33 64 128 256), losses := [] }

theorem u25531 : Upper (D 6) (R 6) [40,48,192,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25532 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 50, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 196 73 274 34 69 133 261), lower := (rows 41 50 196 73 274 34 64 128 256), losses := [] }

theorem u25532 : Upper (D 6) (R 6) [40,48,192,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25533 : Route 9 := (fun mask => (mask,id))

def c25533 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25533 : Upper (D 6) (R 6) [40,48,192,65,258,4] 13 := by
  apply FastRouting.sound _ _ [40,48,192,65,258,4] 13 (by decide) (choices 1) [1,2,4] r25533 c25533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7890
  · exact u7891
  · exact u7892

def b25534 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 196 73 276 33 70 134 262), lower := (rows 41 50 196 73 276 33 64 128 256), losses := [] }

theorem u25534 : Upper (D 6) (R 6) [40,48,192,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25535 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 196 73 276 34 71 135 263), lower := (rows 41 50 196 73 276 34 64 128 256), losses := [] }

theorem u25535 : Upper (D 6) (R 6) [40,48,192,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25536 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 50 196 73 276 36 67 131 259), lower := (rows 41 50 196 73 276 36 64 128 256), losses := [] }

theorem u25536 : Upper (D 6) (R 6) [40,48,192,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25537 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 50 196 74 273 33 70 134 262), lower := (rows 41 50 196 74 273 33 64 128 256), losses := [] }

theorem u25537 : Upper (D 6) (R 6) [40,48,192,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25538 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 196 74 273 34 69 133 261), lower := (rows 41 50 196 74 273 34 64 128 256), losses := [] }

theorem u25538 : Upper (D 6) (R 6) [40,48,192,66,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25539 : Route 9 := (fun mask => (mask,id))

def c25539 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25539 : Upper (D 6) (R 6) [40,48,192,66,257,4] 13 := by
  apply FastRouting.sound _ _ [40,48,192,66,257,4] 13 (by decide) (choices 1) [1,2,4] r25539 c25539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7893
  · exact u7894
  · exact u7895

def b25540 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 196 74 276 33 71 135 263), lower := (rows 41 50 196 74 276 33 64 128 256), losses := [] }

theorem u25540 : Upper (D 6) (R 6) [40,48,192,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25541 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 196 74 276 34 69 133 261), lower := (rows 41 50 196 74 276 34 64 128 256), losses := [] }

theorem u25541 : Upper (D 6) (R 6) [40,48,192,66,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25542 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 196 74 276 36 67 131 259), lower := (rows 41 50 196 74 276 36 64 128 256), losses := [] }

theorem u25542 : Upper (D 6) (R 6) [40,48,192,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25543 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 388 13 82 33 70 198 326), lower := (rows 41 50 388 13 82 33 64 128 256), losses := [] }

theorem u25543 : Upper (D 6) (R 6) [40,48,384,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25544 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 388 13 82 34 69 197 325), lower := (rows 41 50 388 13 82 34 64 128 256), losses := [] }

theorem u25544 : Upper (D 6) (R 6) [40,48,384,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25545 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 50 388 13 82 36 67 195 323), lower := (rows 41 50 388 13 82 36 64 128 256), losses := [] }

theorem u25545 : Upper (D 6) (R 6) [40,48,384,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25546 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 50 388 13 82 96 71 135 263), lower := (rows 41 50 388 13 82 96 64 128 256), losses := [] }

theorem u25546 : Upper (D 6) (R 6) [40,48,384,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25547 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 388 13 84 33 66 194 322), lower := (rows 41 50 388 13 84 33 64 128 256), losses := [] }

theorem u25547 : Upper (D 6) (R 6) [40,48,384,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25548 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 50 388 13 84 34 67 195 323), lower := (rows 41 50 388 13 84 34 64 128 256), losses := [] }

theorem u25548 : Upper (D 6) (R 6) [40,48,384,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25549 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 388 13 84 96 67 131 259), lower := (rows 41 50 388 13 84 96 64 128 256), losses := [] }

theorem u25549 : Upper (D 6) (R 6) [40,48,384,5,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25550 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 50 388 14 81 33 70 198 326), lower := (rows 41 50 388 14 81 33 64 128 256), losses := [] }

theorem u25550 : Upper (D 6) (R 6) [40,48,384,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25551 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 388 14 81 34 69 197 325), lower := (rows 41 50 388 14 81 34 64 128 256), losses := [] }

theorem u25551 : Upper (D 6) (R 6) [40,48,384,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25552 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 388 14 81 36 67 195 323), lower := (rows 41 50 388 14 81 36 64 128 256), losses := [] }

theorem u25552 : Upper (D 6) (R 6) [40,48,384,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25553 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 388 14 81 96 71 135 263), lower := (rows 41 50 388 14 81 96 64 128 256), losses := [] }

theorem u25553 : Upper (D 6) (R 6) [40,48,384,6,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25554 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 50 388 14 84 33 67 195 323), lower := (rows 41 50 388 14 84 33 64 128 256), losses := [] }

theorem u25554 : Upper (D 6) (R 6) [40,48,384,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25555 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 388 14 84 34 65 193 321), lower := (rows 41 50 388 14 84 34 64 128 256), losses := [] }

theorem u25555 : Upper (D 6) (R 6) [40,48,384,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25556 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 388 14 84 96 67 131 259), lower := (rows 41 50 388 14 84 96 64 128 256), losses := [] }

theorem u25556 : Upper (D 6) (R 6) [40,48,384,6,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25557 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 50 388 73 84 33 70 134 262), lower := (rows 41 50 388 73 84 33 64 128 256), losses := [] }

theorem u25557 : Upper (D 6) (R 6) [40,48,384,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25558 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 50 388 73 84 34 71 135 263), lower := (rows 41 50 388 73 84 34 64 128 256), losses := [] }

theorem u25558 : Upper (D 6) (R 6) [40,48,384,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25559 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 388 73 84 36 67 131 259), lower := (rows 41 50 388 73 84 36 64 128 256), losses := [] }

theorem u25559 : Upper (D 6) (R 6) [40,48,384,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25559
end Delivery.IrregularNine14.P06
