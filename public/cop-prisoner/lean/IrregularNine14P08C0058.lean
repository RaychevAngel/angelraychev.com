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

def b3480 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 268 41 208 48 97 161 289), lower := (rows 67 134 268 41 208 48 64 128 256), losses := [] }

theorem u3480 : Upper (D 8) (R 8) [66,132,264,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3480 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3481 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 292 25 56 33 224 224 480), lower := (rows 67 134 292 25 56 33 64 128 256), losses := [] }

theorem u3481 : Upper (D 8) (R 8) [66,132,288,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3482 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 56, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 292 25 56 96 225 161 417), lower := (rows 67 134 292 25 56 96 64 128 256), losses := [] }

theorem u3482 : Upper (D 8) (R 8) [66,132,288,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3483 : PairBound 9 := { available := 97, camps := [], pairs := [(3,6)], upper := (rows 67 134 292 25 56 160 97 225 353), lower := (rows 67 134 292 25 56 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 17 162 0 128 256), good := (rows 59 166 292 25 56 160 0 160 256) }] }

theorem u3483 : Upper (D 8) (R 8) [66,132,288,17,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3484 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 292 41 88 33 240 176 432), lower := (rows 67 134 292 41 88 33 64 128 256), losses := [] }

theorem u3484 : Upper (D 8) (R 8) [66,132,288,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3485 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 134 292 41 88 48 225 161 417), lower := (rows 67 134 292 41 88 48 64 128 256), losses := [] }

theorem u3485 : Upper (D 8) (R 8) [66,132,288,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3485 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3486 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 41 88 160 113 177 305), lower := (rows 67 134 292 41 88 160 64 128 256), losses := [] }

theorem u3486 : Upper (D 8) (R 8) [66,132,288,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3487 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 292 41 112 33 216 152 408), lower := (rows 67 134 292 41 112 33 64 128 256), losses := [] }

theorem u3487 : Upper (D 8) (R 8) [66,132,288,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3488 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 134 292 41 112 40 209 145 401), lower := (rows 67 134 292 41 112 40 64 128 256), losses := [] }

theorem u3488 : Upper (D 8) (R 8) [66,132,288,33,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3488 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3489 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 134 292 41 112 48 201 137 393), lower := (rows 67 134 292 41 112 48 64 128 256), losses := [] }

theorem u3489 : Upper (D 8) (R 8) [66,132,288,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3489 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3490 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 41 112 160 89 153 281), lower := (rows 67 134 292 41 112 160 64 128 256), losses := [] }

theorem u3490 : Upper (D 8) (R 8) [66,132,288,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3491 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 292 41 152 33 112 240 368), lower := (rows 67 134 292 41 152 33 64 128 256), losses := [] }

theorem u3491 : Upper (D 8) (R 8) [66,132,288,33,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3492 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 134 292 41 152 48 97 225 353), lower := (rows 67 134 292 41 152 48 64 128 256), losses := [] }

theorem u3492 : Upper (D 8) (R 8) [66,132,288,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3492 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3493 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 41 152 96 113 177 305), lower := (rows 67 134 292 41 152 96 64 128 256), losses := [] }

theorem u3493 : Upper (D 8) (R 8) [66,132,288,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3494 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 292 41 176 33 88 216 344), lower := (rows 67 134 292 41 176 33 64 128 256), losses := [] }

theorem u3494 : Upper (D 8) (R 8) [66,132,288,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3495 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 134 292 41 176 40 81 209 337), lower := (rows 67 134 292 41 176 40 64 128 256), losses := [] }

theorem u3495 : Upper (D 8) (R 8) [66,132,288,33,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3495 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3496 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 134 292 41 176 48 73 201 329), lower := (rows 67 134 292 41 176 48 64 128 256), losses := [] }

theorem u3496 : Upper (D 8) (R 8) [66,132,288,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3496 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3497 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 41 176 96 89 153 281), lower := (rows 67 134 292 41 176 96 64 128 256), losses := [] }

theorem u3497 : Upper (D 8) (R 8) [66,132,288,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3498 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 292 41 208 33 120 184 312), lower := (rows 67 134 292 41 208 33 64 128 256), losses := [] }

theorem u3498 : Upper (D 8) (R 8) [66,132,288,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3499 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 134 292 41 208 40 113 177 305), lower := (rows 67 134 292 41 208 40 64 128 256), losses := [] }

theorem u3499 : Upper (D 8) (R 8) [66,132,288,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3499 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3500 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 134 292 41 208 48 105 169 297), lower := (rows 67 134 292 41 208 48 64 128 256), losses := [] }

theorem u3500 : Upper (D 8) (R 8) [66,132,288,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3500 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3501 : Route 9 := (fun mask => (mask,id))

def c3501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3501 : Upper (D 8) (R 8) [66,132,288,48,192,1] 13 := by
  apply FastRouting.sound _ _ [66,132,288,48,192,1] 13 (by decide) (choices 1) [1,8,32] r3501 c3501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u455
  · exact u456
  · exact u457

def b3502 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 292 56 208 40 97 161 289), lower := (rows 67 134 292 56 208 40 64 128 256), losses := [] }

theorem u3502 : Upper (D 8) (R 8) [66,132,288,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3502 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3503 : Route 9 := (fun mask => (mask,id))

def c3503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3503 : Upper (D 8) (R 8) [66,132,288,80,160,1] 13 := by
  apply FastRouting.sound _ _ [66,132,288,80,160,1] 13 (by decide) (choices 1) [1,8,32] r3503 c3503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u458
  · exact u459
  · exact u460

def b3504 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 292 88 176 40 97 161 289), lower := (rows 67 134 292 88 176 40 64 128 256), losses := [] }

theorem u3504 : Upper (D 8) (R 8) [66,132,288,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3504 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3505 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 292 104 152 33 113 177 305), lower := (rows 67 134 292 104 152 33 64 128 256), losses := [] }

theorem u3505 : Upper (D 8) (R 8) [66,132,288,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3506 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 292 104 152 48 97 161 289), lower := (rows 67 134 292 104 152 48 64 128 256), losses := [] }

theorem u3506 : Upper (D 8) (R 8) [66,132,288,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3506 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3507 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 292 104 176 33 89 153 281), lower := (rows 67 134 292 104 176 33 64 128 256), losses := [] }

theorem u3507 : Upper (D 8) (R 8) [66,132,288,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3508 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 134 292 104 176 40 81 145 273), lower := (rows 67 134 292 104 176 40 64 128 256), losses := [] }

theorem u3508 : Upper (D 8) (R 8) [66,132,288,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3508 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3509 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 67 134 292 104 176 48 73 137 265), lower := (rows 67 134 292 104 176 48 64 128 256), losses := [] }

theorem u3509 : Upper (D 8) (R 8) [66,132,288,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3509 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3510 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 28 304 33 224 224 480), lower := (rows 67 162 13 28 304 33 64 128 256), losses := [] }

theorem u3510 : Upper (D 8) (R 8) [66,160,9,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3511 : Route 9 := (fun mask => (mask,id))

def c3511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3511 : Upper (D 8) (R 8) [66,160,9,20,288,64] 13 := by
  apply FastRouting.sound _ _ [66,160,9,20,288,64] 13 (by decide) (choices 1) [1,32,128] r3511 c3511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u461
  · exact u462
  · exact u463

def b3512 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 28 304 160 97 225 353), lower := (rows 67 162 13 28 304 160 64 128 256), losses := [] }

theorem u3512 : Upper (D 8) (R 8) [66,160,9,20,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3513 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 13 44 112 33 464 400 400), lower := (rows 67 162 13 44 112 33 64 128 256), losses := [] }

theorem u3513 : Upper (D 8) (R 8) [66,160,9,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3514 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 67 162 13 44 112 48 449 385 385), lower := (rows 67 162 13 44 112 48 64 128 256), losses := [] }

theorem u3514 : Upper (D 8) (R 8) [66,160,9,36,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3514 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3515 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 44 112 160 337 401 273), lower := (rows 67 162 13 44 112 160 64 128 256), losses := [] }

theorem u3515 : Upper (D 8) (R 8) [66,160,9,36,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3516 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 162 13 44 112 288 209 145 401), lower := (rows 67 162 13 44 112 288 64 128 256), losses := [] }

theorem u3516 : Upper (D 8) (R 8) [66,160,9,36,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3516 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3517 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 13 44 208 33 368 432 304), lower := (rows 67 162 13 44 208 33 64 128 256), losses := [] }

theorem u3517 : Upper (D 8) (R 8) [66,160,9,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3518 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 162 13 44 208 48 353 417 289), lower := (rows 67 162 13 44 208 48 64 128 256), losses := [] }

theorem u3518 : Upper (D 8) (R 8) [66,160,9,36,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3518 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3519 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 13 44 208 288 113 177 305), lower := (rows 67 162 13 44 208 288 64 128 256), losses := [] }

theorem u3519 : Upper (D 8) (R 8) [66,160,9,36,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3519 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3520 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 13 44 304 33 208 208 464), lower := (rows 67 162 13 44 304 33 64 128 256), losses := [] }

theorem u3520 : Upper (D 8) (R 8) [66,160,9,36,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3521 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 162 13 44 304 48 193 193 449), lower := (rows 67 162 13 44 304 48 64 128 256), losses := [] }

theorem u3521 : Upper (D 8) (R 8) [66,160,9,36,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3521 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3522 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 44, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 44 304 96 209 145 401), lower := (rows 67 162 13 44 304 96 64 128 256), losses := [] }

theorem u3522 : Upper (D 8) (R 8) [66,160,9,36,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3523 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 44 304 160 81 209 337), lower := (rows 67 162 13 44 304 160 64 128 256), losses := [] }

theorem u3523 : Upper (D 8) (R 8) [66,160,9,36,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3524 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 13 44 336 33 240 176 432), lower := (rows 67 162 13 44 336 33 64 128 256), losses := [] }

theorem u3524 : Upper (D 8) (R 8) [66,160,9,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3525 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 13 44 336 48 225 161 417), lower := (rows 67 162 13 44 336 48 64 128 256), losses := [] }

theorem u3525 : Upper (D 8) (R 8) [66,160,9,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3525 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3526 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 44 336 160 113 177 305), lower := (rows 67 162 13 44 336 160 64 128 256), losses := [] }

theorem u3526 : Upper (D 8) (R 8) [66,160,9,36,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3527 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 13 44 400 33 112 240 368), lower := (rows 67 162 13 44 400 33 64 128 256), losses := [] }

theorem u3527 : Upper (D 8) (R 8) [66,160,9,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3528 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 162 13 44 400 48 97 225 353), lower := (rows 67 162 13 44 400 48 64 128 256), losses := [] }

theorem u3528 : Upper (D 8) (R 8) [66,160,9,36,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3528 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3529 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 44, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 44 400 96 113 177 305), lower := (rows 67 162 13 44 400 96 64 128 256), losses := [] }

theorem u3529 : Upper (D 8) (R 8) [66,160,9,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3530 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 56 276 33 224 224 480), lower := (rows 67 162 13 56 276 33 64 128 256), losses := [] }

theorem u3530 : Upper (D 8) (R 8) [66,160,9,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3531 : Route 9 := (fun mask => (mask,id))

def c3531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3531 : Upper (D 8) (R 8) [66,160,9,48,260,64] 13 := by
  apply FastRouting.sound _ _ [66,160,9,48,260,64] 13 (by decide) (choices 1) [1,32,128] r3531 c3531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u464
  · exact u465
  · exact u466

def b3532 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 56 276 160 97 225 353), lower := (rows 67 162 13 56 276 160 64 128 256), losses := [] }

theorem u3532 : Upper (D 8) (R 8) [66,160,9,48,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3533 : Route 9 := (fun mask => (mask,id))

def c3533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3533 : Upper (D 8) (R 8) [66,160,9,48,384,1] 13 := by
  apply FastRouting.sound _ _ [66,160,9,48,384,1] 13 (by decide) (choices 1) [4,32] r3533 c3533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u467
  · exact u468

def b3534 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 162 13 56 400 36 97 225 353), lower := (rows 67 162 13 56 400 36 64 128 256), losses := [] }

theorem u3534 : Upper (D 8) (R 8) [66,160,9,48,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3534 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3535 : Route 9 := (fun mask => (mask,id))

def c3535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3535 : Upper (D 8) (R 8) [66,160,9,48,384,64] 13 := by
  apply FastRouting.sound _ _ [66,160,9,48,384,64] 13 (by decide) (choices 1) [1,4,32] r3535 c3535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u469
  · exact u470
  · exact u471

def b3536 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 268 112 33 240 176 432), lower := (rows 67 162 13 268 112 33 64 128 256), losses := [] }

theorem u3536 : Upper (D 8) (R 8) [66,160,9,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3537 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 13 268 112 48 225 161 417), lower := (rows 67 162 13 268 112 48 64 128 256), losses := [] }

theorem u3537 : Upper (D 8) (R 8) [66,160,9,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3537 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3538 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 268 112 160 113 177 305), lower := (rows 67 162 13 268 112 160 64 128 256), losses := [] }

theorem u3538 : Upper (D 8) (R 8) [66,160,9,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3539 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 268 208 33 112 176 304), lower := (rows 67 162 13 268 208 33 64 128 256), losses := [] }

theorem u3539 : Upper (D 8) (R 8) [66,160,9,260,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3539
end Delivery.IrregularNine14.P08
