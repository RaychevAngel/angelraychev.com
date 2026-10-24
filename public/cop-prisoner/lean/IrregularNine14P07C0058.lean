import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0003

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3480 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 104 273 160 66 192 448), lower := (rows 13 50 7 104 273 160 66 128 256), losses := [] }

theorem u3480 : Upper (D 7) (R 7) [12,48,3,96,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3481 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 104 273 160 192 194 322), lower := (rows 13 50 7 104 273 160 192 128 256), losses := [] }

theorem u3481 : Upper (D 7) (R 7) [12,48,3,96,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3482 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 104 274 160 65 192 448), lower := (rows 13 50 7 104 274 160 65 128 256), losses := [] }

theorem u3482 : Upper (D 7) (R 7) [12,48,3,96,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3483 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 104 274 160 192 193 321), lower := (rows 13 50 7 104 274 160 192 128 256), losses := [] }

theorem u3483 : Upper (D 7) (R 7) [12,48,3,96,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3484 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 104 336 160 65 130 386), lower := (rows 13 50 7 104 336 160 65 128 256), losses := [] }

theorem u3484 : Upper (D 7) (R 7) [12,48,3,96,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3485 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 13 50 7 104 336 160 66 129 385), lower := (rows 13 50 7 104 336 160 66 128 256), losses := [] }

theorem u3485 : Upper (D 7) (R 7) [12,48,3,96,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3486 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 104 336 160 192 131 259), lower := (rows 13 50 7 104 336 160 192 128 256), losses := [] }

theorem u3486 : Upper (D 7) (R 7) [12,48,3,96,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3487 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 50 7 200 82 288 65 160 416), lower := (rows 13 50 7 200 82 288 65 128 256), losses := [] }

theorem u3487 : Upper (D 7) (R 7) [12,48,3,192,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3487 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3488 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 82, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 50 7 200 82 288 96 129 385), lower := (rows 13 50 7 200 82 288 96 128 256), losses := [] }

theorem u3488 : Upper (D 7) (R 7) [12,48,3,192,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3488 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3489 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 50 7 200 82 288 192 161 289), lower := (rows 13 50 7 200 82 288 192 128 256), losses := [] }

theorem u3489 : Upper (D 7) (R 7) [12,48,3,192,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3489 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3490 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 50 7 200 273 96 66 160 416), lower := (rows 13 50 7 200 273 96 66 128 256), losses := [] }

theorem u3490 : Upper (D 7) (R 7) [12,48,3,192,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3491 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 400, targets := 96 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(3,0),(4,5),(4,6)], upper := (rows 13 50 7 200 273 96 96 130 386), lower := (rows 13 50 7 200 273 96 96 128 256), losses := [] }

theorem u3491 : Upper (D 7) (R 7) [12,48,3,192,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3492 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 200 273 96 192 162 290), lower := (rows 13 50 7 200 273 96 192 128 256), losses := [] }

theorem u3492 : Upper (D 7) (R 7) [12,48,3,192,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3493 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 7 200 274 96 65 160 416), lower := (rows 13 50 7 200 274 96 65 128 256), losses := [] }

theorem u3493 : Upper (D 7) (R 7) [12,48,3,192,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3494 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 7 200 274 96 96 129 385), lower := (rows 13 50 7 200 274 96 96 128 256), losses := [] }

theorem u3494 : Upper (D 7) (R 7) [12,48,3,192,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3495 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 200 274 96 192 161 289), lower := (rows 13 50 7 200 274 96 192 128 256), losses := [] }

theorem u3495 : Upper (D 7) (R 7) [12,48,3,192,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3496 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 50 7 200 336 33 66 160 416), lower := (rows 13 50 7 200 336 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 80 37 64 167 295), good := (rows 429 432 421 216 344 417 472 128 256) }] }

theorem u3496 : Upper (D 7) (R 7) [12,48,3,192,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3497 : Route 9 := (fun mask => (mask,id))

def c3497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3497 : Upper (D 7) (R 7) [12,48,3,192,320,1,32] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,320,1,32] 13 (by decide) (choices 1) [2] r3497 c3497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u212

def b3498 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 200 336 33 192 162 290), lower := (rows 13 50 7 200 336 33 192 128 256), losses := [] }

theorem u3498 : Upper (D 7) (R 7) [12,48,3,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3499 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 50 7 200 336 34 65 160 416), lower := (rows 13 50 7 200 336 34 65 128 256), losses := [] }

theorem u3499 : Upper (D 7) (R 7) [12,48,3,192,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3500 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 7 200 336 34 96 129 385), lower := (rows 13 50 7 200 336 34 96 128 256), losses := [] }

theorem u3500 : Upper (D 7) (R 7) [12,48,3,192,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3501 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 200 336 34 192 161 289), lower := (rows 13 50 7 200 336 34 192 128 256), losses := [] }

theorem u3501 : Upper (D 7) (R 7) [12,48,3,192,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3502 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 50 7 200 336 160 65 162 290), lower := (rows 13 50 7 200 336 160 65 128 256), losses := [] }

theorem u3502 : Upper (D 7) (R 7) [12,48,3,192,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3503 : Route 9 := (fun mask => (mask,id))

def c3503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3503 : Upper (D 7) (R 7) [12,48,3,192,320,128,2] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,320,128,2] 13 (by decide) (choices 1) [1,32] r3503 c3503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u213
  · exact u214

def r3504 : Route 9 := (fun mask => (mask,id))

def c3504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3504 : Upper (D 7) (R 7) [12,48,3,192,320,128,32] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,320,128,32] 13 (by decide) (choices 1) [1,2] r3504 c3504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u215
  · exact u216

def b3505 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 296 81 160 66 192 448), lower := (rows 13 50 7 296 81 160 66 128 256), losses := [] }

theorem u3505 : Upper (D 7) (R 7) [12,48,3,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3506 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(1,6),(3,0),(4,5)], upper := (rows 13 50 7 296 81 160 192 194 322), lower := (rows 13 50 7 296 81 160 192 128 256), losses := [{ target := 6, region := (rows 1 18 20 8 16 224 0 128 256), good := (rows 13 54 7 296 55 160 160 160 256) }] }

theorem u3506 : Upper (D 7) (R 7) [12,48,3,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3507 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 296 82 160 65 192 448), lower := (rows 13 50 7 296 82 160 65 128 256), losses := [] }

theorem u3507 : Upper (D 7) (R 7) [12,48,3,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3508 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 489, targets := 2 },{ cop := 5, region := 82, targets := 1 }], pairs := [(0,1),(1,0),(3,1),(4,0)], upper := (rows 13 50 7 296 82 160 192 193 321), lower := (rows 13 50 7 296 82 160 192 128 256), losses := [] }

theorem u3508 : Upper (D 7) (R 7) [12,48,3,288,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3509 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 7 328 82 160 65 160 416), lower := (rows 13 50 7 328 82 160 65 128 256), losses := [] }

theorem u3509 : Upper (D 7) (R 7) [12,48,3,320,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3510 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 82, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 7 328 82 160 96 129 385), lower := (rows 13 50 7 328 82 160 96 128 256), losses := [] }

theorem u3510 : Upper (D 7) (R 7) [12,48,3,320,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3511 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 489, targets := 2 },{ cop := 5, region := 82, targets := 1 }], pairs := [(0,1),(1,0),(3,1),(4,0)], upper := (rows 13 50 7 328 82 160 192 161 289), lower := (rows 13 50 7 328 82 160 192 128 256), losses := [] }

theorem u3511 : Upper (D 7) (R 7) [12,48,3,320,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3512 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 50 7 328 145 96 66 160 416), lower := (rows 13 50 7 328 145 96 66 128 256), losses := [] }

theorem u3512 : Upper (D 7) (R 7) [12,48,3,320,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3513 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 104, targets := 131 },{ cop := 2, region := 144, targets := 32 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 13 50 7 328 145 96 96 130 386), lower := (rows 13 50 7 328 145 96 96 128 256), losses := [] }

theorem u3513 : Upper (D 7) (R 7) [12,48,3,320,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3514 : Route 9 := (fun mask => (mask,id))

def c3514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3514 : Upper (D 7) (R 7) [12,48,3,320,129,64,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,129,64,128] 13 (by decide) (choices 1) [2,32] r3514 c3514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u217
  · exact u218

def b3515 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 7 328 146 96 65 160 416), lower := (rows 13 50 7 328 146 96 65 128 256), losses := [] }

theorem u3515 : Upper (D 7) (R 7) [12,48,3,320,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3516 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 104, targets := 131 },{ cop := 2, region := 144, targets := 32 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 13 50 7 328 146 96 96 129 385), lower := (rows 13 50 7 328 146 96 96 128 256), losses := [] }

theorem u3516 : Upper (D 7) (R 7) [12,48,3,320,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3517 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 489, targets := 2 },{ cop := 6, region := 50, targets := 1 }], pairs := [(0,1),(1,0),(3,1),(4,0)], upper := (rows 13 50 7 328 146 96 192 161 289), lower := (rows 13 50 7 328 146 96 192 128 256), losses := [] }

theorem u3517 : Upper (D 7) (R 7) [12,48,3,320,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3518 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 50 7 328 208 33 66 160 416), lower := (rows 13 50 7 328 208 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 80 37 64 167 295), good := (rows 429 432 421 344 216 417 472 128 256) }] }

theorem u3518 : Upper (D 7) (R 7) [12,48,3,320,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3519 : Route 9 := (fun mask => (mask,id))

def c3519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3519 : Upper (D 7) (R 7) [12,48,3,320,192,1,32] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,192,1,32] 13 (by decide) (choices 1) [2] r3519 c3519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u219

def b3520 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 328 208 33 192 162 290), lower := (rows 13 50 7 328 208 33 192 128 256), losses := [] }

theorem u3520 : Upper (D 7) (R 7) [12,48,3,320,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3521 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 50 7 328 208 34 65 160 416), lower := (rows 13 50 7 328 208 34 65 128 256), losses := [] }

theorem u3521 : Upper (D 7) (R 7) [12,48,3,320,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3522 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 34, targets := 129 },{ cop := 4, region := 34, targets := 64 },{ cop := 7, region := 114, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 7 328 208 34 96 129 385), lower := (rows 13 50 7 328 208 34 96 128 256), losses := [] }

theorem u3522 : Upper (D 7) (R 7) [12,48,3,320,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3523 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 328 208 34 192 161 289), lower := (rows 13 50 7 328 208 34 192 128 256), losses := [] }

theorem u3523 : Upper (D 7) (R 7) [12,48,3,320,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3524 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 173, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 13 50 37 73 274 160 66 192 448), lower := (rows 13 50 37 73 274 160 66 128 256), losses := [] }

theorem u3524 : Upper (D 7) (R 7) [12,48,33,65,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3525 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 77, targets := 2 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 37 73 274 160 192 194 322), lower := (rows 13 50 37 73 274 160 192 128 256), losses := [] }

theorem u3525 : Upper (D 7) (R 7) [12,48,33,65,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3526 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 50 37 74 146 288 65 192 448), lower := (rows 13 50 37 74 146 288 65 128 256), losses := [] }

theorem u3526 : Upper (D 7) (R 7) [12,48,33,66,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3526 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3527 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 293, targets := 2 },{ cop := 3, region := 293, targets := 128 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 13 50 37 74 146 288 192 193 321), lower := (rows 13 50 37 74 146 288 192 128 256), losses := [] }

theorem u3527 : Upper (D 7) (R 7) [12,48,33,66,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3527 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3528 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 50 37 74 208 288 65 130 386), lower := (rows 13 50 37 74 208 288 65 128 256), losses := [] }

theorem u3528 : Upper (D 7) (R 7) [12,48,33,66,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3528 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3529 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 50 37 74 208 288 66 129 385), lower := (rows 13 50 37 74 208 288 66 128 256), losses := [] }

theorem u3529 : Upper (D 7) (R 7) [12,48,33,66,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3529 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3530 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 50 37 74 208 288 192 131 259), lower := (rows 13 50 37 74 208 288 192 128 256), losses := [] }

theorem u3530 : Upper (D 7) (R 7) [12,48,33,66,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3530 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3531 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 37 74 274 160 65 192 448), lower := (rows 13 50 37 74 274 160 65 128 256), losses := [] }

theorem u3531 : Upper (D 7) (R 7) [12,48,33,66,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3532 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(3,5)], upper := (rows 13 50 37 74 274 160 192 193 321), lower := (rows 13 50 37 74 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 224 224 128 256), good := (rows 12 122 100 106 282 224 224 224 256) },{ target := 5, region := (rows 1 2 4 10 16 0 229 133 261), good := (rows 461 90 453 74 282 192 192 192 256) }] }

theorem u3532 : Upper (D 7) (R 7) [12,48,33,66,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3533 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 37 74 336 160 65 130 386), lower := (rows 13 50 37 74 336 160 65 128 256), losses := [] }

theorem u3533 : Upper (D 7) (R 7) [12,48,33,66,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3534 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 13 50 37 74 336 160 66 129 385), lower := (rows 13 50 37 74 336 160 66 128 256), losses := [] }

theorem u3534 : Upper (D 7) (R 7) [12,48,33,66,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3535 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 13 50 37 74 336 160 192 131 259), lower := (rows 13 50 37 74 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 18 4 26 16 224 224 128 256), good := (rows 12 122 100 106 378 224 224 224 256) }] }

theorem u3535 : Upper (D 7) (R 7) [12,48,33,66,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3536 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 50 37 200 82 288 65 130 386), lower := (rows 13 50 37 200 82 288 65 128 256), losses := [] }

theorem u3536 : Upper (D 7) (R 7) [12,48,33,192,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3536 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3537 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 82, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 50 37 200 82 288 66 129 385), lower := (rows 13 50 37 200 82 288 66 128 256), losses := [] }

theorem u3537 : Upper (D 7) (R 7) [12,48,33,192,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3537 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3538 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 50 37 200 82 288 192 131 259), lower := (rows 13 50 37 200 82 288 192 128 256), losses := [] }

theorem u3538 : Upper (D 7) (R 7) [12,48,33,192,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3538 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3539 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 50 37 200 336 34 65 130 386), lower := (rows 13 50 37 200 336 34 65 128 256), losses := [] }

theorem u3539 : Upper (D 7) (R 7) [12,48,33,192,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3539
end Delivery.IrregularNine14.P07
