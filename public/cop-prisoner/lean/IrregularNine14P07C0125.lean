import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0009

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7500 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 13 26 208 288 192 131 259), lower := (rows 37 98 13 26 208 288 192 128 256), losses := [] }

theorem u7500 : Upper (D 7) (R 7) [36,96,9,18,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7500 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7501 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 98 13 26 273 160 66 192 448), lower := (rows 37 98 13 26 273 160 66 128 256), losses := [{ target := 1, region := (rows 13 0 12 8 24 234 64 194 322), good := (rows 37 480 61 445 273 160 480 160 256) }] }

theorem u7501 : Upper (D 7) (R 7) [36,96,9,18,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7502 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 13 26 273 160 192 194 322), lower := (rows 37 98 13 26 273 160 192 128 256), losses := [] }

theorem u7502 : Upper (D 7) (R 7) [36,96,9,18,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7503 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 13 26 336 160 65 130 386), lower := (rows 37 98 13 26 336 160 65 128 256), losses := [] }

theorem u7503 : Upper (D 7) (R 7) [36,96,9,18,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7504 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 26 336 160 66 129 385), lower := (rows 37 98 13 26 336 160 66 128 256), losses := [] }

theorem u7504 : Upper (D 7) (R 7) [36,96,9,18,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7505 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 13 26 336 160 192 131 259), lower := (rows 37 98 13 26 336 160 192 128 256), losses := [] }

theorem u7505 : Upper (D 7) (R 7) [36,96,9,18,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7506 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 13 88 145 288 66 130 386), lower := (rows 37 98 13 88 145 288 66 128 256), losses := [] }

theorem u7506 : Upper (D 7) (R 7) [36,96,9,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7506 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7507 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 37 98 13 88 145 288 192 130 258), lower := (rows 37 98 13 88 145 288 192 128 256), losses := [] }

theorem u7507 : Upper (D 7) (R 7) [36,96,9,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7507 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7508 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 88 146 288 65 130 386), lower := (rows 37 98 13 88 146 288 65 128 256), losses := [] }

theorem u7508 : Upper (D 7) (R 7) [36,96,9,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7508 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7509 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 13 88 146 288 66 129 385), lower := (rows 37 98 13 88 146 288 66 128 256), losses := [] }

theorem u7509 : Upper (D 7) (R 7) [36,96,9,80,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7509 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7510 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 13 88 146 288 192 131 259), lower := (rows 37 98 13 88 146 288 192 128 256), losses := [] }

theorem u7510 : Upper (D 7) (R 7) [36,96,9,80,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7510 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7511 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,0),(1,7),(3,0)], upper := (rows 37 98 13 88 273 160 66 130 386), lower := (rows 37 98 13 88 273 160 66 128 256), losses := [{ target := 6, region := (rows 13 2 12 8 24 234 0 194 322), good := (rows 37 418 61 445 273 160 418 160 256) }] }

theorem u7511 : Upper (D 7) (R 7) [36,96,9,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7512 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 13 88 273 160 192 130 258), lower := (rows 37 98 13 88 273 160 192 128 256), losses := [] }

theorem u7512 : Upper (D 7) (R 7) [36,96,9,80,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7513 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 13 88 274 160 65 130 386), lower := (rows 37 98 13 88 274 160 65 128 256), losses := [] }

theorem u7513 : Upper (D 7) (R 7) [36,96,9,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7514 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 88 274 160 66 129 385), lower := (rows 37 98 13 88 274 160 66 128 256), losses := [] }

theorem u7514 : Upper (D 7) (R 7) [36,96,9,80,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7515 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 13 88 274 160 192 131 259), lower := (rows 37 98 13 88 274 160 192 128 256), losses := [] }

theorem u7515 : Upper (D 7) (R 7) [36,96,9,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7516 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 13 138 81 288 66 144 400), lower := (rows 37 98 13 138 81 288 66 128 256), losses := [] }

theorem u7516 : Upper (D 7) (R 7) [36,96,9,130,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7516 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7517 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 13 138 81 288 80 130 386), lower := (rows 37 98 13 138 81 288 80 128 256), losses := [] }

theorem u7517 : Upper (D 7) (R 7) [36,96,9,130,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7517 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7518 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 13 138 81 288 192 146 274), lower := (rows 37 98 13 138 81 288 192 128 256), losses := [] }

theorem u7518 : Upper (D 7) (R 7) [36,96,9,130,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7518 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7519 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 138 208 288 65 146 274), lower := (rows 37 98 13 138 208 288 65 128 256), losses := [] }

theorem u7519 : Upper (D 7) (R 7) [36,96,9,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7519 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7520 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 98 13 138 208 288 66 145 273), lower := (rows 37 98 13 138 208 288 66 128 256), losses := [] }

theorem u7520 : Upper (D 7) (R 7) [36,96,9,130,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7520 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7521 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 13 138 208 288 80 131 259), lower := (rows 37 98 13 138 208 288 80 128 256), losses := [] }

theorem u7521 : Upper (D 7) (R 7) [36,96,9,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7521 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7522 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 138 274 48 65 192 448), lower := (rows 37 98 13 138 274 48 65 128 256), losses := [] }

theorem u7522 : Upper (D 7) (R 7) [36,96,9,130,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7522 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7523 : Route 9 := (fun mask => (mask,id))

def c7523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7523 : Upper (D 7) (R 7) [36,96,9,130,258,16,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,258,16,128] 13 (by decide) (choices 1) [1,64] r7523 c7523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u564
  · exact u565

def b7524 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 138 400 48 65 194 322), lower := (rows 37 98 13 138 400 48 65 128 256), losses := [] }

theorem u7524 : Upper (D 7) (R 7) [36,96,9,130,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7524 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7525 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 13 138 400 48 66 193 321), lower := (rows 37 98 13 138 400 48 66 128 256), losses := [] }

theorem u7525 : Upper (D 7) (R 7) [36,96,9,130,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7525 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7526 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 13 152 81 288 66 130 386), lower := (rows 37 98 13 152 81 288 66 128 256), losses := [] }

theorem u7526 : Upper (D 7) (R 7) [36,96,9,144,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7526 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7527 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 13 152 81 288 192 130 258), lower := (rows 37 98 13 152 81 288 192 128 256), losses := [] }

theorem u7527 : Upper (D 7) (R 7) [36,96,9,144,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7527 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7528 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 200 146 288 65 146 274), lower := (rows 37 98 13 200 146 288 65 128 256), losses := [] }

theorem u7528 : Upper (D 7) (R 7) [36,96,9,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7528 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7529 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 72, targets := 33 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 13 200 146 288 66 145 273), lower := (rows 37 98 13 200 146 288 66 128 256), losses := [] }

theorem u7529 : Upper (D 7) (R 7) [36,96,9,192,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7529 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7530 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 13 200 146 288 80 131 259), lower := (rows 37 98 13 200 146 288 80 128 256), losses := [] }

theorem u7530 : Upper (D 7) (R 7) [36,96,9,192,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7530 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7531 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 200 274 48 65 130 386), lower := (rows 37 98 13 200 274 48 65 128 256), losses := [] }

theorem u7531 : Upper (D 7) (R 7) [36,96,9,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7531 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7532 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 13 200 274 48 66 129 385), lower := (rows 37 98 13 200 274 48 66 128 256), losses := [] }

theorem u7532 : Upper (D 7) (R 7) [36,96,9,192,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7532 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7533 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 13 200 274 48 192 131 259), lower := (rows 37 98 13 200 274 48 192 128 256), losses := [] }

theorem u7533 : Upper (D 7) (R 7) [36,96,9,192,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7533 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7534 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 13 200 400 48 65 130 258), lower := (rows 37 98 13 200 400 48 65 128 256), losses := [] }

theorem u7534 : Upper (D 7) (R 7) [36,96,9,192,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7534 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7535 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 13 200 400 48 66 131 259), lower := (rows 37 98 13 200 400 48 66 128 256), losses := [] }

theorem u7535 : Upper (D 7) (R 7) [36,96,9,192,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7535 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7536 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 37 98 13 266 81 160 66 144 400), lower := (rows 37 98 13 266 81 160 66 128 256), losses := [] }

theorem u7536 : Upper (D 7) (R 7) [36,96,9,258,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7537 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 266 81 160 80 130 386), lower := (rows 37 98 13 266 81 160 80 128 256), losses := [] }

theorem u7537 : Upper (D 7) (R 7) [36,96,9,258,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7537 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7538 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 13 266 81 160 192 146 274), lower := (rows 37 98 13 266 81 160 192 128 256), losses := [] }

theorem u7538 : Upper (D 7) (R 7) [36,96,9,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7539 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,5)], upper := (rows 37 98 13 266 145 160 66 208 336), lower := (rows 37 98 13 266 145 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 21 0 74 132 260), good := (rows 405 66 477 330 145 128 66 128 256) }] }

theorem u7539 : Upper (D 7) (R 7) [36,96,9,258,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7540 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 13 266 145 160 80 194 322), lower := (rows 37 98 13 266 145 160 80 128 256), losses := [] }

theorem u7540 : Upper (D 7) (R 7) [36,96,9,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7540 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7541 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 266 146 48 65 192 448), lower := (rows 37 98 13 266 146 48 65 128 256), losses := [] }

theorem u7541 : Upper (D 7) (R 7) [36,96,9,258,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7541 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7542 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 13 266 146 48 192 193 321), lower := (rows 37 98 13 266 146 48 192 128 256), losses := [] }

theorem u7542 : Upper (D 7) (R 7) [36,96,9,258,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7542 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7543 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 13 266 146 160 65 208 336), lower := (rows 37 98 13 266 146 160 65 128 256), losses := [] }

theorem u7543 : Upper (D 7) (R 7) [36,96,9,258,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7544 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 13 266 146 160 80 193 321), lower := (rows 37 98 13 266 146 160 80 128 256), losses := [] }

theorem u7544 : Upper (D 7) (R 7) [36,96,9,258,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7544 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7545 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 13 266 208 160 65 146 274), lower := (rows 37 98 13 266 208 160 65 128 256), losses := [] }

theorem u7545 : Upper (D 7) (R 7) [36,96,9,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7546 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 98 13 266 208 160 66 145 273), lower := (rows 37 98 13 266 208 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 74 133 261), good := (rows 405 66 477 330 208 128 66 128 256) }] }

theorem u7546 : Upper (D 7) (R 7) [36,96,9,258,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7547 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 266 208 160 80 131 259), lower := (rows 37 98 13 266 208 160 80 128 256), losses := [] }

theorem u7547 : Upper (D 7) (R 7) [36,96,9,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7547 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7548 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 37 98 13 280 81 160 66 130 386), lower := (rows 37 98 13 280 81 160 66 128 256), losses := [] }

theorem u7548 : Upper (D 7) (R 7) [36,96,9,272,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7549 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 13 280 81 160 192 130 258), lower := (rows 37 98 13 280 81 160 192 128 256), losses := [] }

theorem u7549 : Upper (D 7) (R 7) [36,96,9,272,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7550 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 37 98 13 328 145 160 66 146 274), lower := (rows 37 98 13 328 145 160 66 128 256), losses := [{ target := 7, region := (rows 1 35 20 24 16 32 119 0 272), good := (rows 103 98 79 328 351 98 66 0 256) }] }

theorem u7550 : Upper (D 7) (R 7) [36,96,9,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7551 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 13 328 145 160 80 130 258), lower := (rows 37 98 13 328 145 160 80 128 256), losses := [] }

theorem u7551 : Upper (D 7) (R 7) [36,96,9,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7551 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7552 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 328 146 48 65 130 386), lower := (rows 37 98 13 328 146 48 65 128 256), losses := [] }

theorem u7552 : Upper (D 7) (R 7) [36,96,9,320,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7552 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7553 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 13 328 146 48 66 129 385), lower := (rows 37 98 13 328 146 48 66 128 256), losses := [] }

theorem u7553 : Upper (D 7) (R 7) [36,96,9,320,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7553 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7554 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 13 328 146 48 192 131 259), lower := (rows 37 98 13 328 146 48 192 128 256), losses := [] }

theorem u7554 : Upper (D 7) (R 7) [36,96,9,320,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7554 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7555 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 13 328 146 160 65 146 274), lower := (rows 37 98 13 328 146 160 65 128 256), losses := [] }

theorem u7555 : Upper (D 7) (R 7) [36,96,9,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7556 : Route 9 := (fun mask => (mask,id))

def c7556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7556 : Upper (D 7) (R 7) [36,96,9,320,130,128,2] 13 := by
  apply FastRouting.sound _ _ [36,96,9,320,130,128,2] 13 (by decide) (choices 1) [1,16] r7556 c7556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u566
  · exact u567

def b7557 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 13 328 146 160 80 131 259), lower := (rows 37 98 13 328 146 160 80 128 256), losses := [] }

theorem u7557 : Upper (D 7) (R 7) [36,96,9,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7557 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7558 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 396, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 98 13 392 81 34 66 144 400), lower := (rows 37 98 13 392 81 34 66 128 256), losses := [] }

theorem u7558 : Upper (D 7) (R 7) [36,96,9,384,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7559 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 119, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 13 392 81 34 80 130 386), lower := (rows 37 98 13 392 81 34 80 128 256), losses := [] }

theorem u7559 : Upper (D 7) (R 7) [36,96,9,384,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7559 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7559
end Delivery.IrregularNine14.P07
