import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0125

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23520 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 138 208 34 337 401 273), lower := (rows 37 98 13 138 208 34 64 128 256), losses := [] }

theorem u23520 : Upper (D 7) (R 7) [36,96,9,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23521 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 138 208 48 323 387 259), lower := (rows 37 98 13 138 208 48 64 128 256), losses := [] }

theorem u23521 : Upper (D 7) (R 7) [36,96,9,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23521 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23522 : Route 9 := (fun mask => (mask,id))

def c23522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23522 : Upper (D 7) (R 7) [36,96,9,130,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,192,256] 13 (by decide) (choices 1) [1,2,16] r23522 c23522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7519
  · exact u7520
  · exact u7521

def b23523 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 138 273 34 208 208 464), lower := (rows 37 98 13 138 273 34 64 128 256), losses := [] }

theorem u23523 : Upper (D 7) (R 7) [36,96,9,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23524 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 13 138 273 48 194 194 450), lower := (rows 37 98 13 138 273 48 64 128 256), losses := [] }

theorem u23524 : Upper (D 7) (R 7) [36,96,9,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23524 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23525 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 138 273 96 210 146 402), lower := (rows 37 98 13 138 273 96 64 128 256), losses := [] }

theorem u23525 : Upper (D 7) (R 7) [36,96,9,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23526 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 138 273 160 82 210 338), lower := (rows 37 98 13 138 273 160 64 128 256), losses := [] }

theorem u23526 : Upper (D 7) (R 7) [36,96,9,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23527 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 138 274 33 208 208 464), lower := (rows 37 98 13 138 274 33 64 128 256), losses := [] }

theorem u23527 : Upper (D 7) (R 7) [36,96,9,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23528 : Route 9 := (fun mask => (mask,id))

def c23528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23528 : Upper (D 7) (R 7) [36,96,9,130,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,258,16] 13 (by decide) (choices 1) [1,128] r23528 c23528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7522
  · exact u7523

def b23529 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 138 274 96 209 145 401), lower := (rows 37 98 13 138 274 96 64 128 256), losses := [] }

theorem u23529 : Upper (D 7) (R 7) [36,96,9,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23530 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 138 274 160 81 209 337), lower := (rows 37 98 13 138 274 160 64 128 256), losses := [] }

theorem u23530 : Upper (D 7) (R 7) [36,96,9,130,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23531 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 138 336 33 210 146 402), lower := (rows 37 98 13 138 336 33 64 128 256), losses := [] }

theorem u23531 : Upper (D 7) (R 7) [36,96,9,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23532 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 138 336 34 209 145 401), lower := (rows 37 98 13 138 336 34 64 128 256), losses := [] }

theorem u23532 : Upper (D 7) (R 7) [36,96,9,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23533 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 138 336 48 195 131 387), lower := (rows 37 98 13 138 336 48 64 128 256), losses := [] }

theorem u23533 : Upper (D 7) (R 7) [36,96,9,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23533 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23534 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 138 336 160 83 147 275), lower := (rows 37 98 13 138 336 160 64 128 256), losses := [] }

theorem u23534 : Upper (D 7) (R 7) [36,96,9,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23535 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 138 400 33 82 210 338), lower := (rows 37 98 13 138 400 33 64 128 256), losses := [] }

theorem u23535 : Upper (D 7) (R 7) [36,96,9,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23536 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 138 400 34 81 209 337), lower := (rows 37 98 13 138 400 34 64 128 256), losses := [] }

theorem u23536 : Upper (D 7) (R 7) [36,96,9,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23537 : Route 9 := (fun mask => (mask,id))

def c23537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23537 : Upper (D 7) (R 7) [36,96,9,130,384,16] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,384,16] 13 (by decide) (choices 1) [1,2] r23537 c23537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7524
  · exact u7525

def b23538 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 138 400 96 83 147 275), lower := (rows 37 98 13 138 400 96 64 128 256), losses := [] }

theorem u23538 : Upper (D 7) (R 7) [36,96,9,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23539 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(3,0)], upper := (rows 37 98 13 152 81 34 450 386 386), lower := (rows 37 98 13 152 81 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 9 17 0 98 162 290), good := (rows 477 450 29 156 93 450 64 128 256) }] }

theorem u23539 : Upper (D 7) (R 7) [36,96,9,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23540 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 152 81 160 322 386 258), lower := (rows 37 98 13 152 81 160 64 128 256), losses := [] }

theorem u23540 : Upper (D 7) (R 7) [36,96,9,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23541 : Route 9 := (fun mask => (mask,id))

def c23541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23541 : Upper (D 7) (R 7) [36,96,9,144,65,256] 13 := by
  apply FastRouting.sound _ _ [36,96,9,144,65,256] 13 (by decide) (choices 1) [2,128] r23541 c23541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7526
  · exact u7527

def b23542 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(3,0)], upper := (rows 37 98 13 152 273 34 194 194 450), lower := (rows 37 98 13 152 273 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 9 17 0 98 162 290), good := (rows 477 450 29 156 285 450 64 128 256) }] }

theorem u23542 : Upper (D 7) (R 7) [36,96,9,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23543 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 152 273 96 194 130 386), lower := (rows 37 98 13 152 273 96 64 128 256), losses := [] }

theorem u23543 : Upper (D 7) (R 7) [36,96,9,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23544 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 152 273 160 66 194 322), lower := (rows 37 98 13 152 273 160 64 128 256), losses := [] }

theorem u23544 : Upper (D 7) (R 7) [36,96,9,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23545 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 152 274 33 194 194 450), lower := (rows 37 98 13 152 274 33 64 128 256), losses := [] }

theorem u23545 : Upper (D 7) (R 7) [36,96,9,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23546 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 13 152 274 34 193 193 449), lower := (rows 37 98 13 152 274 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 128 256), good := (rows 37 34 13 189 306 34 0 128 256) }] }

theorem u23546 : Upper (D 7) (R 7) [36,96,9,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23547 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 152 274 96 195 131 387), lower := (rows 37 98 13 152 274 96 64 128 256), losses := [] }

theorem u23547 : Upper (D 7) (R 7) [36,96,9,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23548 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 152 274 160 67 195 323), lower := (rows 37 98 13 152 274 160 64 128 256), losses := [] }

theorem u23548 : Upper (D 7) (R 7) [36,96,9,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23549 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 152 336 33 194 130 386), lower := (rows 37 98 13 152 336 33 64 128 256), losses := [] }

theorem u23549 : Upper (D 7) (R 7) [36,96,9,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23550 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 34, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 152 336 34 195 131 387), lower := (rows 37 98 13 152 336 34 64 128 256), losses := [{ target := 7, region := (rows 13 82 12 8 16 122 64 0 256), good := (rows 37 98 45 63 370 34 98 0 256) }] }

theorem u23550 : Upper (D 7) (R 7) [36,96,9,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23551 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 152 336 160 67 131 259), lower := (rows 37 98 13 152 336 160 64 128 256), losses := [] }

theorem u23551 : Upper (D 7) (R 7) [36,96,9,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23552 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 200 145 34 338 402 274), lower := (rows 37 98 13 200 145 34 64 128 256), losses := [] }

theorem u23552 : Upper (D 7) (R 7) [36,96,9,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23553 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 13 200 145 48 322 386 258), lower := (rows 37 98 13 200 145 48 64 128 256), losses := [] }

theorem u23553 : Upper (D 7) (R 7) [36,96,9,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23553 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23554 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 13 200 145 288 82 146 274), lower := (rows 37 98 13 200 145 288 64 128 256), losses := [] }

theorem u23554 : Upper (D 7) (R 7) [36,96,9,192,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23554 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23555 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 200 146 33 338 402 274), lower := (rows 37 98 13 200 146 33 64 128 256), losses := [] }

theorem u23555 : Upper (D 7) (R 7) [36,96,9,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23556 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 200 146 34 337 401 273), lower := (rows 37 98 13 200 146 34 64 128 256), losses := [] }

theorem u23556 : Upper (D 7) (R 7) [36,96,9,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23557 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 13 200 146 48 323 387 259), lower := (rows 37 98 13 200 146 48 64 128 256), losses := [] }

theorem u23557 : Upper (D 7) (R 7) [36,96,9,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23557 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23558 : Route 9 := (fun mask => (mask,id))

def c23558 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23558 : Upper (D 7) (R 7) [36,96,9,192,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192,130,256] 13 (by decide) (choices 1) [1,2,16] r23558 c23558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7528
  · exact u7529
  · exact u7530

def b23559 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 200 273 34 210 146 402), lower := (rows 37 98 13 200 273 34 64 128 256), losses := [] }

theorem u23559 : Upper (D 7) (R 7) [36,96,9,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23560 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 13 200 273 48 194 130 386), lower := (rows 37 98 13 200 273 48 64 128 256), losses := [] }

theorem u23560 : Upper (D 7) (R 7) [36,96,9,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23560 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23561 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 200 273 160 82 146 274), lower := (rows 37 98 13 200 273 160 64 128 256), losses := [] }

theorem u23561 : Upper (D 7) (R 7) [36,96,9,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23562 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 200 274 33 210 146 402), lower := (rows 37 98 13 200 274 33 64 128 256), losses := [] }

theorem u23562 : Upper (D 7) (R 7) [36,96,9,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23563 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 200 274 34 209 145 401), lower := (rows 37 98 13 200 274 34 64 128 256), losses := [] }

theorem u23563 : Upper (D 7) (R 7) [36,96,9,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23564 : Route 9 := (fun mask => (mask,id))

def c23564 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23564 : Upper (D 7) (R 7) [36,96,9,192,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192,258,16] 13 (by decide) (choices 1) [1,2,128] r23564 c23564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7531
  · exact u7532
  · exact u7533

def b23565 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 200 274 160 83 147 275), lower := (rows 37 98 13 200 274 160 64 128 256), losses := [] }

theorem u23565 : Upper (D 7) (R 7) [36,96,9,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23566 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 200 400 33 82 146 274), lower := (rows 37 98 13 200 400 33 64 128 256), losses := [] }

theorem u23566 : Upper (D 7) (R 7) [36,96,9,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23567 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 200 400 34 83 147 275), lower := (rows 37 98 13 200 400 34 64 128 256), losses := [] }

theorem u23567 : Upper (D 7) (R 7) [36,96,9,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23568 : Route 9 := (fun mask => (mask,id))

def c23568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23568 : Upper (D 7) (R 7) [36,96,9,192,384,16] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192,384,16] 13 (by decide) (choices 1) [1,2] r23568 c23568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7534
  · exact u7535

def b23569 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 266 81 34 208 144 400), lower := (rows 37 98 13 266 81 34 64 128 256), losses := [] }

theorem u23569 : Upper (D 7) (R 7) [36,96,9,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23570 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 266 81 48 194 130 386), lower := (rows 37 98 13 266 81 48 64 128 256), losses := [] }

theorem u23570 : Upper (D 7) (R 7) [36,96,9,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23570 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23571 : Route 9 := (fun mask => (mask,id))

def c23571 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23571 : Upper (D 7) (R 7) [36,96,9,258,65,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,65,128] 13 (by decide) (choices 1) [2,16,128] r23571 c23571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7536
  · exact u7537
  · exact u7538

def b23572 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 266 145 34 208 208 464), lower := (rows 37 98 13 266 145 34 64 128 256), losses := [] }

theorem u23572 : Upper (D 7) (R 7) [36,96,9,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23573 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 13 266 145 48 194 194 450), lower := (rows 37 98 13 266 145 48 64 128 256), losses := [] }

theorem u23573 : Upper (D 7) (R 7) [36,96,9,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23573 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23574 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 266 145 96 210 146 402), lower := (rows 37 98 13 266 145 96 64 128 256), losses := [] }

theorem u23574 : Upper (D 7) (R 7) [36,96,9,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23575 : Route 9 := (fun mask => (mask,id))

def c23575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23575 : Upper (D 7) (R 7) [36,96,9,258,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,129,128] 13 (by decide) (choices 1) [2,16] r23575 c23575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7539
  · exact u7540

def b23576 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 266 146 33 208 208 464), lower := (rows 37 98 13 266 146 33 64 128 256), losses := [] }

theorem u23576 : Upper (D 7) (R 7) [36,96,9,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23577 : Route 9 := (fun mask => (mask,id))

def c23577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23577 : Upper (D 7) (R 7) [36,96,9,258,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,130,16] 13 (by decide) (choices 1) [1,128] r23577 c23577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7541
  · exact u7542

def b23578 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 266 146 96 209 145 401), lower := (rows 37 98 13 266 146 96 64 128 256), losses := [] }

theorem u23578 : Upper (D 7) (R 7) [36,96,9,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23579 : Route 9 := (fun mask => (mask,id))

def c23579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23579 : Upper (D 7) (R 7) [36,96,9,258,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,130,128] 13 (by decide) (choices 1) [1,16] r23579 c23579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7543
  · exact u7544

#print axioms u23579
end Delivery.IrregularNine14.P07
