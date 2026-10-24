import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8400 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 134 292 11 81 96 66 148 276), lower := (rows 41 134 292 11 81 96 66 128 256), losses := [] }

theorem u8400 : Upper (D 6) (R 6) [40,132,288,3,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8401 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 8, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 41 134 292 11 81 96 68 146 274), lower := (rows 41 134 292 11 81 96 68 128 256), losses := [] }

theorem u8401 : Upper (D 6) (R 6) [40,132,288,3,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8402 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 292 11 81 96 80 134 262), lower := (rows 41 134 292 11 81 96 80 128 256), losses := [] }

theorem u8402 : Upper (D 6) (R 6) [40,132,288,3,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8402 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8403 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 134 292 11 82 96 65 148 276), lower := (rows 41 134 292 11 82 96 65 128 256), losses := [] }

theorem u8403 : Upper (D 6) (R 6) [40,132,288,3,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8404 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 41 134 292 11 82 96 68 145 273), lower := (rows 41 134 292 11 82 96 68 128 256), losses := [] }

theorem u8404 : Upper (D 6) (R 6) [40,132,288,3,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8405 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 134 292 11 82 96 80 133 261), lower := (rows 41 134 292 11 82 96 80 128 256), losses := [] }

theorem u8405 : Upper (D 6) (R 6) [40,132,288,3,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8405 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8406 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 292 11 84 48 65 194 322), lower := (rows 41 134 292 11 84 48 65 128 256), losses := [] }

theorem u8406 : Upper (D 6) (R 6) [40,132,288,3,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8406 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8407 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 41 134 292 11 84 48 66 193 321), lower := (rows 41 134 292 11 84 48 66 128 256), losses := [] }

theorem u8407 : Upper (D 6) (R 6) [40,132,288,3,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8407 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8408 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 292 11 84 96 65 146 274), lower := (rows 41 134 292 11 84 96 65 128 256), losses := [] }

theorem u8408 : Upper (D 6) (R 6) [40,132,288,3,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8409 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 292 11 84 96 66 145 273), lower := (rows 41 134 292 11 84 96 66 128 256), losses := [] }

theorem u8409 : Upper (D 6) (R 6) [40,132,288,3,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8410 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 134 292 11 84 96 80 131 259), lower := (rows 41 134 292 11 84 96 80 128 256), losses := [] }

theorem u8410 : Upper (D 6) (R 6) [40,132,288,3,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8410 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8411 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 134 292 25 84 34 65 194 322), lower := (rows 41 134 292 25 84 34 65 128 256), losses := [] }

theorem u8411 : Upper (D 6) (R 6) [40,132,288,17,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8412 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 32 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 41 134 292 25 84 34 66 193 321), lower := (rows 41 134 292 25 84 34 66 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 98 98 145 273), good := (rows 489 226 352 409 505 98 98 128 256) }] }

theorem u8412 : Upper (D 6) (R 6) [40,132,288,17,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8413 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 134 292 28 81 34 65 194 322), lower := (rows 41 134 292 28 81 34 65 128 256), losses := [] }

theorem u8413 : Upper (D 6) (R 6) [40,132,288,20,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8414 : PairBound 9 := { available := 65, camps := [], pairs := [(1,5),(4,2),(4,5)], upper := (rows 41 134 292 28 81 34 66 193 321), lower := (rows 41 134 292 28 81 34 66 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 98 98 145 273), good := (rows 505 226 352 408 497 98 98 128 256) },{ target := 5, region := (rows 1 10 4 8 17 0 107 145 273), good := (rows 475 198 324 478 465 66 66 128 256) }] }

theorem u8414 : Upper (D 6) (R 6) [40,132,288,20,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8415 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 2 },{ cop := 4, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 41 134 292 73 19 34 68 208 336), lower := (rows 41 134 292 73 19 34 68 128 256), losses := [] }

theorem u8415 : Upper (D 6) (R 6) [40,132,288,65,3,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8416 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 134 292 73 19 34 80 196 324), lower := (rows 41 134 292 73 19 34 80 128 256), losses := [] }

theorem u8416 : Upper (D 6) (R 6) [40,132,288,65,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8416 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8417 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 134 292 73 82 34 65 148 276), lower := (rows 41 134 292 73 82 34 65 128 256), losses := [] }

theorem u8417 : Upper (D 6) (R 6) [40,132,288,65,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8418 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 2 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 292 73 82 34 68 145 273), lower := (rows 41 134 292 73 82 34 68 128 256), losses := [] }

theorem u8418 : Upper (D 6) (R 6) [40,132,288,65,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8419 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 134 292 73 82 34 80 133 261), lower := (rows 41 134 292 73 82 34 80 128 256), losses := [] }

theorem u8419 : Upper (D 6) (R 6) [40,132,288,65,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8419 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8420 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 134 292 73 84 34 65 146 274), lower := (rows 41 134 292 73 84 34 65 128 256), losses := [] }

theorem u8420 : Upper (D 6) (R 6) [40,132,288,65,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8421 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 292 73 84 34 66 145 273), lower := (rows 41 134 292 73 84 34 66 128 256), losses := [] }

theorem u8421 : Upper (D 6) (R 6) [40,132,288,65,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8422 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 41 134 292 73 84 34 80 131 259), lower := (rows 41 134 292 73 84 34 80 128 256), losses := [] }

theorem u8422 : Upper (D 6) (R 6) [40,132,288,65,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8422 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8423 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(1,5),(3,1)], upper := (rows 41 134 292 76 19 34 65 208 336), lower := (rows 41 134 292 76 19 34 65 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 17 0 81 209 337), good := (rows 475 134 260 462 467 2 465 128 256) }] }

theorem u8423 : Upper (D 6) (R 6) [40,132,288,68,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8424 : Route 9 := (fun mask => (mask,id))

def c8424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8424 : Upper (D 6) (R 6) [40,132,288,68,3,2,16] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68,3,2,16] 13 (by decide) (choices 1) [1,64] r8424 c8424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u651
  · exact u652

def b8425 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 41 134 292 76 19 48 65 194 322), lower := (rows 41 134 292 76 19 48 65 128 256), losses := [] }

theorem u8425 : Upper (D 6) (R 6) [40,132,288,68,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8425 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8426 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 72, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 41 134 292 76 19 48 66 193 321), lower := (rows 41 134 292 76 19 48 66 128 256), losses := [] }

theorem u8426 : Upper (D 6) (R 6) [40,132,288,68,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8426 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8427 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 134 292 76 81 34 65 146 274), lower := (rows 41 134 292 76 81 34 65 128 256), losses := [] }

theorem u8427 : Upper (D 6) (R 6) [40,132,288,68,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8428 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 1, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 41 134 292 76 81 34 66 145 273), lower := (rows 41 134 292 76 81 34 66 128 256), losses := [] }

theorem u8428 : Upper (D 6) (R 6) [40,132,288,68,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8429 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 41 134 292 76 81 34 80 131 259), lower := (rows 41 134 292 76 81 34 80 128 256), losses := [] }

theorem u8429 : Upper (D 6) (R 6) [40,132,288,68,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8429 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8430 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(1,5),(3,1)], upper := (rows 41 134 292 76 82 34 65 145 273), lower := (rows 41 134 292 76 82 34 65 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 65 193 321), good := (rows 475 134 260 478 466 2 465 128 256) }] }

theorem u8430 : Upper (D 6) (R 6) [40,132,288,68,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8431 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 134 292 76 82 34 80 129 257), lower := (rows 41 134 292 76 82 34 80 128 256), losses := [] }

theorem u8431 : Upper (D 6) (R 6) [40,132,288,68,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8431 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8432 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 134 292 88 21 34 65 194 322), lower := (rows 41 134 292 88 21 34 65 128 256), losses := [] }

theorem u8432 : Upper (D 6) (R 6) [40,132,288,80,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8433 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 41 134 292 88 21 34 66 193 321), lower := (rows 41 134 292 88 21 34 66 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 98 98 137 265), good := (rows 489 226 352 505 401 98 98 128 256) }] }

theorem u8433 : Upper (D 6) (R 6) [40,132,288,80,5,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8434 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 324 13 82 34 65 176 304), lower := (rows 41 134 324 13 82 34 65 128 256), losses := [] }

theorem u8434 : Upper (D 6) (R 6) [40,132,320,5,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8435 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 134 324 13 82 34 80 161 289), lower := (rows 41 134 324 13 82 34 80 128 256), losses := [] }

theorem u8435 : Upper (D 6) (R 6) [40,132,320,5,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8435 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8436 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 41 134 324 13 82 34 96 145 273), lower := (rows 41 134 324 13 82 34 96 128 256), losses := [] }

theorem u8436 : Upper (D 6) (R 6) [40,132,320,5,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8437 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 324 13 82 48 65 162 290), lower := (rows 41 134 324 13 82 48 65 128 256), losses := [] }

theorem u8437 : Upper (D 6) (R 6) [40,132,320,5,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8437 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8438 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 301, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 134 324 13 82 48 66 161 289), lower := (rows 41 134 324 13 82 48 66 128 256), losses := [] }

theorem u8438 : Upper (D 6) (R 6) [40,132,320,5,66,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8438 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8439 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 112, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 41 134 324 13 82 48 96 131 259), lower := (rows 41 134 324 13 82 48 96 128 256), losses := [] }

theorem u8439 : Upper (D 6) (R 6) [40,132,320,5,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8439 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8440 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 324 13 112 34 65 146 274), lower := (rows 41 134 324 13 112 34 65 128 256), losses := [] }

theorem u8440 : Upper (D 6) (R 6) [40,132,320,5,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8441 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 269, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 134 324 13 112 34 66 145 273), lower := (rows 41 134 324 13 112 34 66 128 256), losses := [] }

theorem u8441 : Upper (D 6) (R 6) [40,132,320,5,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8442 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 134 324 13 112 34 80 131 259), lower := (rows 41 134 324 13 112 34 80 128 256), losses := [] }

theorem u8442 : Upper (D 6) (R 6) [40,132,320,5,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8442 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8443 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 1 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 134 324 26 21 96 65 162 290), lower := (rows 41 134 324 26 21 96 65 128 256), losses := [] }

theorem u8443 : Upper (D 6) (R 6) [40,132,320,18,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8444 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,6),(3,6)], upper := (rows 41 134 324 26 21 96 66 161 289), lower := (rows 41 134 324 26 21 96 66 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 32 0 129 257), good := (rows 425 134 260 26 415 32 2 128 256) }] }

theorem u8444 : Upper (D 6) (R 6) [40,132,320,18,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8445 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 138, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 41 134 324 26 21 96 96 131 259), lower := (rows 41 134 324 26 21 96 96 128 256), losses := [] }

theorem u8445 : Upper (D 6) (R 6) [40,132,320,18,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8446 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 134 324 26 81 36 65 162 290), lower := (rows 41 134 324 26 81 36 65 128 256), losses := [] }

theorem u8446 : Upper (D 6) (R 6) [40,132,320,18,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8447 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 292, targets := 2 }], pairs := [(0,1),(2,1),(4,2)], upper := (rows 41 134 324 26 81 36 66 161 289), lower := (rows 41 134 324 26 81 36 66 128 256), losses := [{ target := 1, region := (rows 9 0 20 8 16 62 64 153 281), good := (rows 425 164 356 445 501 36 96 128 256) },{ target := 2, region := (rows 1 2 0 8 17 32 74 129 257), good := (rows 505 194 320 90 465 32 66 128 256) }] }

theorem u8447 : Upper (D 6) (R 6) [40,132,320,18,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8448 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 134 324 26 81 36 96 131 259), lower := (rows 41 134 324 26 81 36 96 128 256), losses := [] }

theorem u8448 : Upper (D 6) (R 6) [40,132,320,18,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8449 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 5, region := 390, targets := 1 }], pairs := [(0,1),(0,2),(1,0)], upper := (rows 41 134 324 28 19 96 65 162 290), lower := (rows 41 134 324 28 19 96 65 128 256), losses := [] }

theorem u8449 : Upper (D 6) (R 6) [40,132,320,20,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8450 : Route 9 := (fun mask => (mask,id))

def c8450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8450 : Upper (D 6) (R 6) [40,132,320,20,3,64,2] 13 := by
  apply FastRouting.sound _ _ [40,132,320,20,3,64,2] 13 (by decide) (choices 1) [1,32] r8450 c8450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u653
  · exact u654

def b8451 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,1),(0,2),(2,0)], upper := (rows 41 134 324 28 19 96 96 131 259), lower := (rows 41 134 324 28 19 96 96 128 256), losses := [] }

theorem u8451 : Upper (D 6) (R 6) [40,132,320,20,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8452 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 134 324 28 81 34 65 162 290), lower := (rows 41 134 324 28 81 34 65 128 256), losses := [] }

theorem u8452 : Upper (D 6) (R 6) [40,132,320,20,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8453 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 41 134 324 28 81 34 66 161 289), lower := (rows 41 134 324 28 81 34 66 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 64 129 257), good := (rows 425 132 324 28 477 32 64 128 256) }] }

theorem u8453 : Upper (D 6) (R 6) [40,132,320,20,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8454 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 134 324 28 81 34 96 131 259), lower := (rows 41 134 324 28 81 34 96 128 256), losses := [] }

theorem u8454 : Upper (D 6) (R 6) [40,132,320,20,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8455 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 134 324 73 19 34 68 176 304), lower := (rows 41 134 324 73 19 34 68 128 256), losses := [] }

theorem u8455 : Upper (D 6) (R 6) [40,132,320,65,3,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8456 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 134 324 73 19 34 80 164 292), lower := (rows 41 134 324 73 19 34 80 128 256), losses := [] }

theorem u8456 : Upper (D 6) (R 6) [40,132,320,65,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8456 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8457 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 324 73 19 34 96 148 276), lower := (rows 41 134 324 73 19 34 96 128 256), losses := [] }

theorem u8457 : Upper (D 6) (R 6) [40,132,320,65,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8458 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 178, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 134 324 73 52 34 65 146 274), lower := (rows 41 134 324 73 52 34 65 128 256), losses := [] }

theorem u8458 : Upper (D 6) (R 6) [40,132,320,65,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8459 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 324 73 52 34 66 145 273), lower := (rows 41 134 324 73 52 34 66 128 256), losses := [] }

theorem u8459 : Upper (D 6) (R 6) [40,132,320,65,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8459
end Delivery.IrregularNine14.P06
