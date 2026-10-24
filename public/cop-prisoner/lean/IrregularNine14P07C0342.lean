import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0095

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20520 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 73 274 33 212 148 404), lower := (rows 35 194 44 73 274 33 64 128 256), losses := [] }

theorem u20520 : Upper (D 7) (R 7) [34,192,40,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20521 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 73 274 36 209 145 401), lower := (rows 35 194 44 73 274 36 64 128 256), losses := [] }

theorem u20521 : Upper (D 7) (R 7) [34,192,40,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20521 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20522 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 194 44 73 274 48 197 133 389), lower := (rows 35 194 44 73 274 48 64 128 256), losses := [] }

theorem u20522 : Upper (D 7) (R 7) [34,192,40,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20522 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20523 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 73 274 160 85 149 277), lower := (rows 35 194 44 73 274 160 64 128 256), losses := [] }

theorem u20523 : Upper (D 7) (R 7) [34,192,40,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20524 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 73 276 33 210 146 402), lower := (rows 35 194 44 73 276 33 64 128 256), losses := [] }

theorem u20524 : Upper (D 7) (R 7) [34,192,40,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20525 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 73 276 34 209 145 401), lower := (rows 35 194 44 73 276 34 64 128 256), losses := [] }

theorem u20525 : Upper (D 7) (R 7) [34,192,40,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20526 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 194 44 73 276 48 195 131 387), lower := (rows 35 194 44 73 276 48 64 128 256), losses := [{ target := 5, region := (rows 1 15 4 9 20 0 73 137 265), good := (rows 459 194 478 459 278 16 64 128 256) }] }

theorem u20526 : Upper (D 7) (R 7) [34,192,40,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20526 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20527 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 73 276 160 83 147 275), lower := (rows 35 194 44 73 276 160 64 128 256), losses := [] }

theorem u20527 : Upper (D 7) (R 7) [34,192,40,65,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20528 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 73 400 33 86 150 278), lower := (rows 35 194 44 73 400 33 64 128 256), losses := [] }

theorem u20528 : Upper (D 7) (R 7) [34,192,40,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20529 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 73 400 34 85 149 277), lower := (rows 35 194 44 73 400 34 64 128 256), losses := [] }

theorem u20529 : Upper (D 7) (R 7) [34,192,40,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20530 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 73 400 36 83 147 275), lower := (rows 35 194 44 73 400 36 64 128 256), losses := [] }

theorem u20530 : Upper (D 7) (R 7) [34,192,40,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20530 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20531 : Route 9 := (fun mask => (mask,id))

def c20531 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20531 : Upper (D 7) (R 7) [34,192,40,65,384,16] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,384,16] 13 (by decide) (choices 1) [1,2,4] r20531 c20531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5727
  · exact u5728
  · exact u5729

def b20532 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,6),(1,0),(1,5),(4,6)], upper := (rows 35 194 44 88 145 33 326 390 262), lower := (rows 35 194 44 88 145 33 64 128 256), losses := [] }

theorem u20532 : Upper (D 7) (R 7) [34,192,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20533 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 88 145 34 325 389 261), lower := (rows 35 194 44 88 145 34 64 128 256), losses := [] }

theorem u20533 : Upper (D 7) (R 7) [34,192,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20534 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 88 145 36 323 387 259), lower := (rows 35 194 44 88 145 36 64 128 256), losses := [] }

theorem u20534 : Upper (D 7) (R 7) [34,192,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20534 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20535 : Route 9 := (fun mask => (mask,id))

def c20535 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20535 : Upper (D 7) (R 7) [34,192,40,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,129,256] 13 (by decide) (choices 1) [1,2,4] r20535 c20535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5730
  · exact u5731
  · exact u5732

def b20536 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(3,5)], upper := (rows 35 194 44 88 148 33 323 387 259), lower := (rows 35 194 44 88 148 33 64 128 256), losses := [{ target := 5, region := (rows 1 39 4 12 20 0 97 161 289), good := (rows 451 194 478 88 158 451 64 128 256) }] }

theorem u20536 : Upper (D 7) (R 7) [34,192,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20537 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 88 148 34 321 385 257), lower := (rows 35 194 44 88 148 34 64 128 256), losses := [] }

theorem u20537 : Upper (D 7) (R 7) [34,192,40,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20538 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(1,5)], upper := (rows 35 194 44 88 148 288 67 131 259), lower := (rows 35 194 44 88 148 288 64 128 256), losses := [] }

theorem u20538 : Upper (D 7) (R 7) [34,192,40,80,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20538 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20539 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 194, targets := 33 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 194 44 88 273 33 198 134 390), lower := (rows 35 194 44 88 273 33 64 128 256), losses := [] }

theorem u20539 : Upper (D 7) (R 7) [34,192,40,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20540 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 88 273 34 197 133 389), lower := (rows 35 194 44 88 273 34 64 128 256), losses := [] }

theorem u20540 : Upper (D 7) (R 7) [34,192,40,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20541 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 88 273 36 195 131 387), lower := (rows 35 194 44 88 273 36 64 128 256), losses := [] }

theorem u20541 : Upper (D 7) (R 7) [34,192,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20541 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20542 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 88 273 160 71 135 263), lower := (rows 35 194 44 88 273 160 64 128 256), losses := [] }

theorem u20542 : Upper (D 7) (R 7) [34,192,40,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20543 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 44 88 274 33 197 133 389), lower := (rows 35 194 44 88 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 136 264), good := (rows 35 163 428 445 307 33 0 128 256) },{ target := 7, region := (rows 19 2 12 8 16 59 64 0 256), good := (rows 35 99 44 125 307 33 64 0 256) }] }

theorem u20543 : Upper (D 7) (R 7) [34,192,40,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20544 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 88 274 36 193 129 385), lower := (rows 35 194 44 88 274 36 64 128 256), losses := [] }

theorem u20544 : Upper (D 7) (R 7) [34,192,40,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20544 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20545 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 88 274 160 69 133 261), lower := (rows 35 194 44 88 274 160 64 128 256), losses := [] }

theorem u20545 : Upper (D 7) (R 7) [34,192,40,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20546 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(3,5)], upper := (rows 35 194 44 88 276 33 195 131 387), lower := (rows 35 194 44 88 276 33 64 128 256), losses := [{ target := 5, region := (rows 1 39 4 12 20 0 97 161 289), good := (rows 451 194 478 88 286 451 64 128 256) }] }

theorem u20546 : Upper (D 7) (R 7) [34,192,40,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20547 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 88 276 34 193 129 385), lower := (rows 35 194 44 88 276 34 64 128 256), losses := [] }

theorem u20547 : Upper (D 7) (R 7) [34,192,40,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20548 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 88 276 160 67 131 259), lower := (rows 35 194 44 88 276 160 64 128 256), losses := [] }

theorem u20548 : Upper (D 7) (R 7) [34,192,40,80,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20549 : Route 9 := (fun mask => (mask,id))

def c20549 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20549 : Upper (D 7) (R 7) [34,192,40,80,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,384,1] 13 (by decide) (choices 1) [1,2,4] r20549 c20549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5733
  · exact u5734
  · exact u5735

def b20550 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 88 400 34 69 133 261), lower := (rows 35 194 44 88 400 34 64 128 256), losses := [] }

theorem u20550 : Upper (D 7) (R 7) [34,192,40,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20551 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 88 400 36 67 131 259), lower := (rows 35 194 44 88 400 36 64 128 256), losses := [] }

theorem u20551 : Upper (D 7) (R 7) [34,192,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20551 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20552 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 265 81 34 212 148 404), lower := (rows 35 194 44 265 81 34 64 128 256), losses := [] }

theorem u20552 : Upper (D 7) (R 7) [34,192,40,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20553 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 265 81 36 210 146 402), lower := (rows 35 194 44 265 81 36 64 128 256), losses := [] }

theorem u20553 : Upper (D 7) (R 7) [34,192,40,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20553 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20554 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 194 44 265 81 48 198 134 390), lower := (rows 35 194 44 265 81 48 64 128 256), losses := [] }

theorem u20554 : Upper (D 7) (R 7) [34,192,40,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20554 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20555 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 265 81 160 86 150 278), lower := (rows 35 194 44 265 81 160 64 128 256), losses := [] }

theorem u20555 : Upper (D 7) (R 7) [34,192,40,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20556 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 265 84 33 210 146 402), lower := (rows 35 194 44 265 84 33 64 128 256), losses := [] }

theorem u20556 : Upper (D 7) (R 7) [34,192,40,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20557 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 265 84 34 209 145 401), lower := (rows 35 194 44 265 84 34 64 128 256), losses := [] }

theorem u20557 : Upper (D 7) (R 7) [34,192,40,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20558 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(1,5),(2,6),(3,5)], upper := (rows 35 194 44 265 84 48 195 131 387), lower := (rows 35 194 44 265 84 48 64 128 256), losses := [] }

theorem u20558 : Upper (D 7) (R 7) [34,192,40,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20558 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20559 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 265 84 160 83 147 275), lower := (rows 35 194 44 265 84 160 64 128 256), losses := [] }

theorem u20559 : Upper (D 7) (R 7) [34,192,40,257,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20560 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 44 266 81 33 212 148 404), lower := (rows 35 194 44 266 81 33 64 128 256), losses := [] }

theorem u20560 : Upper (D 7) (R 7) [34,192,40,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20561 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 194 44 266 81 36 209 145 401), lower := (rows 35 194 44 266 81 36 64 128 256), losses := [] }

theorem u20561 : Upper (D 7) (R 7) [34,192,40,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20561 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20562 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 194 44 266 81 48 197 133 389), lower := (rows 35 194 44 266 81 48 64 128 256), losses := [] }

theorem u20562 : Upper (D 7) (R 7) [34,192,40,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20562 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20563 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 266 81 160 85 149 277), lower := (rows 35 194 44 266 81 160 64 128 256), losses := [] }

theorem u20563 : Upper (D 7) (R 7) [34,192,40,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20564 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 44 266 84 33 209 145 401), lower := (rows 35 194 44 266 84 33 64 128 256), losses := [] }

theorem u20564 : Upper (D 7) (R 7) [34,192,40,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20565 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(1,5),(2,6),(3,5)], upper := (rows 35 194 44 266 84 48 193 129 385), lower := (rows 35 194 44 266 84 48 64 128 256), losses := [] }

theorem u20565 : Upper (D 7) (R 7) [34,192,40,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20565 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20566 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 266 84 160 81 145 273), lower := (rows 35 194 44 266 84 160 64 128 256), losses := [] }

theorem u20566 : Upper (D 7) (R 7) [34,192,40,258,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20567 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(1,5),(4,5),(4,7)], upper := (rows 35 194 44 268 81 33 210 146 402), lower := (rows 35 194 44 268 81 33 64 128 256), losses := [] }

theorem u20567 : Upper (D 7) (R 7) [34,192,40,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20568 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 268 81 34 209 145 401), lower := (rows 35 194 44 268 81 34 64 128 256), losses := [] }

theorem u20568 : Upper (D 7) (R 7) [34,192,40,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20569 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 35 194 44 268 81 48 195 131 387), lower := (rows 35 194 44 268 81 48 64 128 256), losses := [] }

theorem u20569 : Upper (D 7) (R 7) [34,192,40,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20569 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20570 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 268 81 160 83 147 275), lower := (rows 35 194 44 268 81 160 64 128 256), losses := [] }

theorem u20570 : Upper (D 7) (R 7) [34,192,40,260,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20571 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 2, region := 194, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(4,7)], upper := (rows 35 194 44 280 81 33 198 134 390), lower := (rows 35 194 44 280 81 33 64 128 256), losses := [] }

theorem u20571 : Upper (D 7) (R 7) [34,192,40,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20572 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 280 81 34 197 133 389), lower := (rows 35 194 44 280 81 34 64 128 256), losses := [] }

theorem u20572 : Upper (D 7) (R 7) [34,192,40,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20573 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 280 81 36 195 131 387), lower := (rows 35 194 44 280 81 36 64 128 256), losses := [] }

theorem u20573 : Upper (D 7) (R 7) [34,192,40,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20573 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20574 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 280 81 160 71 135 263), lower := (rows 35 194 44 280 81 160 64 128 256), losses := [] }

theorem u20574 : Upper (D 7) (R 7) [34,192,40,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20575 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(3,5)], upper := (rows 35 194 44 280 84 33 195 131 387), lower := (rows 35 194 44 280 84 33 64 128 256), losses := [{ target := 5, region := (rows 1 39 4 12 20 0 97 161 289), good := (rows 451 194 478 280 94 451 64 128 256) }] }

theorem u20575 : Upper (D 7) (R 7) [34,192,40,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20576 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 280 84 34 193 129 385), lower := (rows 35 194 44 280 84 34 64 128 256), losses := [] }

theorem u20576 : Upper (D 7) (R 7) [34,192,40,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20577 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 280 84 160 67 131 259), lower := (rows 35 194 44 280 84 160 64 128 256), losses := [] }

theorem u20577 : Upper (D 7) (R 7) [34,192,40,272,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20578 : Route 9 := (fun mask => (mask,id))

def c20578 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20578 : Upper (D 7) (R 7) [34,192,40,320,129,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,129,1] 13 (by decide) (choices 1) [2,4,16] r20578 c20578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5736
  · exact u5737
  · exact u5738

def b20579 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 328 145 34 85 149 277), lower := (rows 35 194 44 328 145 34 64 128 256), losses := [] }

theorem u20579 : Upper (D 7) (R 7) [34,192,40,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20579
end Delivery.IrregularNine14.P07
