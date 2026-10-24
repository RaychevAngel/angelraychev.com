import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0125

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24420 : Route 9 := (fun mask => (mask,id))

def c24420 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24420 : Upper (D 6) (R 6) [34,136,288,68,65,16] 13 := by
  apply FastRouting.sound _ _ [34,136,288,68,65,16] 13 (by decide) (choices 1) [1,2,4] r24420 c24420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7531
  · exact u7532
  · exact u7533

def b24421 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 293, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 138 292 76 82 33 85 149 277), lower := (rows 35 138 292 76 82 33 64 128 256), losses := [] }

theorem u24421 : Upper (D 6) (R 6) [34,136,288,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24422 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 76 82 36 81 145 273), lower := (rows 35 138 292 76 82 36 64 128 256), losses := [] }

theorem u24422 : Upper (D 6) (R 6) [34,136,288,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24423 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 292 76 82 48 69 133 261), lower := (rows 35 138 292 76 82 48 64 128 256), losses := [] }

theorem u24423 : Upper (D 6) (R 6) [34,136,288,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24423 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24424 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 292 88 21 33 70 198 326), lower := (rows 35 138 292 88 21 33 64 128 256), losses := [] }

theorem u24424 : Upper (D 6) (R 6) [34,136,288,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24425 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 88 21 34 69 197 325), lower := (rows 35 138 292 88 21 34 64 128 256), losses := [] }

theorem u24425 : Upper (D 6) (R 6) [34,136,288,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24426 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 292 88 21 36 67 195 323), lower := (rows 35 138 292 88 21 36 64 128 256), losses := [] }

theorem u24426 : Upper (D 6) (R 6) [34,136,288,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24427 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(2,6),(4,6)], upper := (rows 35 138 292 88 21 96 71 135 263), lower := (rows 35 138 292 88 21 96 64 128 256), losses := [] }

theorem u24427 : Upper (D 6) (R 6) [34,136,288,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24428 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 292 88 22 33 69 197 325), lower := (rows 35 138 292 88 22 33 64 128 256), losses := [] }

theorem u24428 : Upper (D 6) (R 6) [34,136,288,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24429 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 88 22 36 65 193 321), lower := (rows 35 138 292 88 22 36 64 128 256), losses := [] }

theorem u24429 : Upper (D 6) (R 6) [34,136,288,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24430 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 0, region := 260, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 35 138 292 88 22 96 69 133 261), lower := (rows 35 138 292 88 22 96 64 128 256), losses := [] }

theorem u24430 : Upper (D 6) (R 6) [34,136,288,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24431 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 324 13 22 33 112 240 368), lower := (rows 35 138 324 13 22 33 64 128 256), losses := [] }

theorem u24431 : Upper (D 6) (R 6) [34,136,320,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24432 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 324 13 22 48 97 225 353), lower := (rows 35 138 324 13 22 48 64 128 256), losses := [] }

theorem u24432 : Upper (D 6) (R 6) [34,136,320,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24432 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24433 : Route 9 := (fun mask => (mask,id))

def c24433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24433 : Upper (D 6) (R 6) [34,136,320,5,6,64] 13 := by
  apply FastRouting.sound _ _ [34,136,320,5,6,64] 13 (by decide) (choices 1) [1,16,32] r24433 c24433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7534
  · exact u7535
  · exact u7536

def b24434 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 324 13 52 33 82 210 338), lower := (rows 35 138 324 13 52 33 64 128 256), losses := [] }

theorem u24434 : Upper (D 6) (R 6) [34,136,320,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24435 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 13 52 34 81 209 337), lower := (rows 35 138 324 13 52 34 64 128 256), losses := [] }

theorem u24435 : Upper (D 6) (R 6) [34,136,320,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24436 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 324 13 52 48 67 195 323), lower := (rows 35 138 324 13 52 48 64 128 256), losses := [] }

theorem u24436 : Upper (D 6) (R 6) [34,136,320,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24436 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24437 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 324 13 52 96 83 147 275), lower := (rows 35 138 324 13 52 96 64 128 256), losses := [] }

theorem u24437 : Upper (D 6) (R 6) [34,136,320,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24438 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 13 81 34 116 180 308), lower := (rows 35 138 324 13 81 34 64 128 256), losses := [] }

theorem u24438 : Upper (D 6) (R 6) [34,136,320,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24439 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 35 138 324 13 81 36 114 178 306), lower := (rows 35 138 324 13 81 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 154 320 475 465 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 171 292 45 17 36 0 128 256) }] }

theorem u24439 : Upper (D 6) (R 6) [34,136,320,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24440 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 324, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 138 324 13 81 48 102 166 294), lower := (rows 35 138 324 13 81 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 29 8 16 48 65 129 257), good := (rows 486 142 324 462 500 52 64 128 256) }] }

theorem u24440 : Upper (D 6) (R 6) [34,136,320,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24440 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24441 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 324 13 82 33 116 180 308), lower := (rows 35 138 324 13 82 33 64 128 256), losses := [] }

theorem u24441 : Upper (D 6) (R 6) [34,136,320,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24442 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 35 138 324 13 82 36 113 177 305), lower := (rows 35 138 324 13 82 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 154 320 475 82 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 171 292 45 19 36 0 128 256) }] }

theorem u24442 : Upper (D 6) (R 6) [34,136,320,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24443 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 324 13 82 48 101 165 293), lower := (rows 35 138 324 13 82 48 64 128 256), losses := [] }

theorem u24443 : Upper (D 6) (R 6) [34,136,320,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24443 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24444 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 324 13 112 33 86 150 278), lower := (rows 35 138 324 13 112 33 64 128 256), losses := [] }

theorem u24444 : Upper (D 6) (R 6) [34,136,320,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24445 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 13 112 34 85 149 277), lower := (rows 35 138 324 13 112 34 64 128 256), losses := [] }

theorem u24445 : Upper (D 6) (R 6) [34,136,320,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24446 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 80, targets := 4 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 138 324 13 112 36 83 147 275), lower := (rows 35 138 324 13 112 36 64 128 256), losses := [] }

theorem u24446 : Upper (D 6) (R 6) [34,136,320,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24447 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 324 13 112 48 71 135 263), lower := (rows 35 138 324 13 112 48 64 128 256), losses := [] }

theorem u24447 : Upper (D 6) (R 6) [34,136,320,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24447 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24448 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 14 21 33 112 240 368), lower := (rows 35 138 324 14 21 33 64 128 256), losses := [] }

theorem u24448 : Upper (D 6) (R 6) [34,136,320,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24449 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 324 14 21 48 97 225 353), lower := (rows 35 138 324 14 21 48 64 128 256), losses := [] }

theorem u24449 : Upper (D 6) (R 6) [34,136,320,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24449 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24450 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 14 21 96 113 177 305), lower := (rows 35 138 324 14 21 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 116 80 144 272), good := (rows 35 139 352 43 497 96 96 128 256) }] }

theorem u24450 : Upper (D 6) (R 6) [34,136,320,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24451 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 14 52 33 81 209 337), lower := (rows 35 138 324 14 52 33 64 128 256), losses := [] }

theorem u24451 : Upper (D 6) (R 6) [34,136,320,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24452 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 324 14 52 48 65 193 321), lower := (rows 35 138 324 14 52 48 64 128 256), losses := [] }

theorem u24452 : Upper (D 6) (R 6) [34,136,320,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24452 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24453 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 324 14 52 96 81 145 273), lower := (rows 35 138 324 14 52 96 64 128 256), losses := [] }

theorem u24453 : Upper (D 6) (R 6) [34,136,320,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24454 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 14 81 33 116 180 308), lower := (rows 35 138 324 14 81 33 64 128 256), losses := [] }

theorem u24454 : Upper (D 6) (R 6) [34,136,320,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24455 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 324 14 81 36 113 177 305), lower := (rows 35 138 324 14 81 36 64 128 256), losses := [] }

theorem u24455 : Upper (D 6) (R 6) [34,136,320,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24456 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 324 14 81 48 101 165 293), lower := (rows 35 138 324 14 81 48 64 128 256), losses := [] }

theorem u24456 : Upper (D 6) (R 6) [34,136,320,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24456 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24457 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 14 112 33 85 149 277), lower := (rows 35 138 324 14 112 33 64 128 256), losses := [] }

theorem u24457 : Upper (D 6) (R 6) [34,136,320,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24458 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 324 14 112 36 81 145 273), lower := (rows 35 138 324 14 112 36 64 128 256), losses := [] }

theorem u24458 : Upper (D 6) (R 6) [34,136,320,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24459 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 324 14 112 48 69 133 261), lower := (rows 35 138 324 14 112 48 64 128 256), losses := [] }

theorem u24459 : Upper (D 6) (R 6) [34,136,320,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24459 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24460 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 138 324 25 22 33 100 228 356), lower := (rows 35 138 324 25 22 33 64 128 256), losses := [] }

theorem u24460 : Upper (D 6) (R 6) [34,136,320,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24461 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 138 324 25 22 36 97 225 353), lower := (rows 35 138 324 25 22 36 64 128 256), losses := [] }

theorem u24461 : Upper (D 6) (R 6) [34,136,320,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24462 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 138 324 25 22 96 101 165 293), lower := (rows 35 138 324 25 22 96 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 100 64 128 256), good := (rows 35 138 352 25 59 96 96 128 256) }] }

theorem u24462 : Upper (D 6) (R 6) [34,136,320,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24463 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 138 324 25 52 33 70 198 326), lower := (rows 35 138 324 25 52 33 64 128 256), losses := [] }

theorem u24463 : Upper (D 6) (R 6) [34,136,320,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24464 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 25 52 34 69 197 325), lower := (rows 35 138 324 25 52 34 64 128 256), losses := [] }

theorem u24464 : Upper (D 6) (R 6) [34,136,320,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24465 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 138 324 25 52 36 67 195 323), lower := (rows 35 138 324 25 52 36 64 128 256), losses := [] }

theorem u24465 : Upper (D 6) (R 6) [34,136,320,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24466 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 324 25 52 96 71 135 263), lower := (rows 35 138 324 25 52 96 64 128 256), losses := [] }

theorem u24466 : Upper (D 6) (R 6) [34,136,320,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24467 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 138 324 25 82 33 100 164 292), lower := (rows 35 138 324 25 82 33 64 128 256), losses := [] }

theorem u24467 : Upper (D 6) (R 6) [34,136,320,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24468 : Route 9 := (fun mask => (mask,id))

def c24468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24468 : Upper (D 6) (R 6) [34,136,320,17,66,4] 13 := by
  apply FastRouting.sound _ _ [34,136,320,17,66,4] 13 (by decide) (choices 1) [1,4,32] r24468 c24468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7537
  · exact u7538
  · exact u7539

def b24469 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 138 324 25 112 33 70 134 262), lower := (rows 35 138 324 25 112 33 64 128 256), losses := [] }

theorem u24469 : Upper (D 6) (R 6) [34,136,320,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24470 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 25 112 34 69 133 261), lower := (rows 35 138 324 25 112 34 64 128 256), losses := [] }

theorem u24470 : Upper (D 6) (R 6) [34,136,320,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24471 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 138 324 25 112 36 71 135 263), lower := (rows 35 138 324 25 112 36 64 128 256), losses := [] }

theorem u24471 : Upper (D 6) (R 6) [34,136,320,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24472 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 26 21 33 100 228 356), lower := (rows 35 138 324 26 21 33 64 128 256), losses := [] }

theorem u24472 : Upper (D 6) (R 6) [34,136,320,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24473 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 35 138 324 26 21 36 97 225 353), lower := (rows 35 138 324 26 21 36 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 32 65 129 257), good := (rows 483 138 320 26 475 32 64 128 256) }] }

theorem u24473 : Upper (D 6) (R 6) [34,136,320,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24474 : Route 9 := (fun mask => (mask,id))

def c24474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24474 : Upper (D 6) (R 6) [34,136,320,18,5,64] 13 := by
  apply FastRouting.sound _ _ [34,136,320,18,5,64] 13 (by decide) (choices 1) [1,4,32] r24474 c24474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7540
  · exact u7541
  · exact u7542

def b24475 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 26 81 33 100 164 292), lower := (rows 35 138 324 26 81 33 64 128 256), losses := [] }

theorem u24475 : Upper (D 6) (R 6) [34,136,320,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24476 : Route 9 := (fun mask => (mask,id))

def c24476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24476 : Upper (D 6) (R 6) [34,136,320,18,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,320,18,65,4] 13 (by decide) (choices 1) [1,4,32] r24476 c24476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7543
  · exact u7544
  · exact u7545

def b24477 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 138 324 28 81 33 102 166 294), lower := (rows 35 138 324 28 81 33 64 128 256), losses := [] }

theorem u24477 : Upper (D 6) (R 6) [34,136,320,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24478 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 28 81 34 101 165 293), lower := (rows 35 138 324 28 81 34 64 128 256), losses := [] }

theorem u24478 : Upper (D 6) (R 6) [34,136,320,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24479 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 35 138 324 28 81 36 99 163 291), lower := (rows 35 138 324 28 81 36 64 128 256), losses := [] }

theorem u24479 : Upper (D 6) (R 6) [34,136,320,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24479
end Delivery.IrregularNine14.P06
