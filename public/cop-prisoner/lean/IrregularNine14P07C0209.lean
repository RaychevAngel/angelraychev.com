import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0021
import IrregularNine14P07C0022

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12540 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 88 274 33 232 168 424), lower := (rows 7 35 196 88 274 33 64 128 256), losses := [] }

theorem u12540 : Upper (D 7) (R 7) [6,33,192,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12541 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 196, targets := 2 },{ cop := 1, region := 400, targets := 64 }], pairs := [(2,1),(3,1),(4,6)], upper := (rows 7 35 196 88 274 40 225 161 417), lower := (rows 7 35 196 88 274 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 56 66 130 258), good := (rows 453 485 196 124 508 40 64 128 256) }] }

theorem u12541 : Upper (D 7) (R 7) [6,33,192,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12541 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12542 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 88 274 160 105 169 297), lower := (rows 7 35 196 88 274 160 64 128 256), losses := [] }

theorem u12542 : Upper (D 7) (R 7) [6,33,192,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12543 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 88 280 33 226 162 418), lower := (rows 7 35 196 88 280 33 64 128 256), losses := [] }

theorem u12543 : Upper (D 7) (R 7) [6,33,192,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12544 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 88 280 34 225 161 417), lower := (rows 7 35 196 88 280 34 64 128 256), losses := [] }

theorem u12544 : Upper (D 7) (R 7) [6,33,192,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12545 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 88 280 160 99 163 291), lower := (rows 7 35 196 88 280 160 64 128 256), losses := [] }

theorem u12545 : Upper (D 7) (R 7) [6,33,192,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12546 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 88 304 33 202 138 394), lower := (rows 7 35 196 88 304 33 64 128 256), losses := [] }

theorem u12546 : Upper (D 7) (R 7) [6,33,192,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12547 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 88 304 34 201 137 393), lower := (rows 7 35 196 88 304 34 64 128 256), losses := [] }

theorem u12547 : Upper (D 7) (R 7) [6,33,192,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12548 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 1, region := 400, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 35 196 88 304 40 195 131 387), lower := (rows 7 35 196 88 304 40 64 128 256), losses := [] }

theorem u12548 : Upper (D 7) (R 7) [6,33,192,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12548 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12549 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 88 304 160 75 139 267), lower := (rows 7 35 196 88 304 160 64 128 256), losses := [] }

theorem u12549 : Upper (D 7) (R 7) [6,33,192,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12550 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 88 400 33 106 170 298), lower := (rows 7 35 196 88 400 33 64 128 256), losses := [] }

theorem u12550 : Upper (D 7) (R 7) [6,33,192,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12551 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 88 400 34 105 169 297), lower := (rows 7 35 196 88 400 34 64 128 256), losses := [] }

theorem u12551 : Upper (D 7) (R 7) [6,33,192,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12552 : Route 9 := (fun mask => (mask,id))

def c12552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12552 : Upper (D 7) (R 7) [6,33,192,80,384,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384,8] 13 (by decide) (choices 1) [1,2,32] r12552 c12552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1313
  · exact u1314
  · exact u1315

def b12553 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 104 273 34 216 152 408), lower := (rows 7 35 196 104 273 34 64 128 256), losses := [] }

theorem u12553 : Upper (D 7) (R 7) [6,33,192,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12554 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 196 104 273 40 210 146 402), lower := (rows 7 35 196 104 273 40 64 128 256), losses := [] }

theorem u12554 : Upper (D 7) (R 7) [6,33,192,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12554 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12555 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 196 104 273 48 202 138 394), lower := (rows 7 35 196 104 273 48 64 128 256), losses := [] }

theorem u12555 : Upper (D 7) (R 7) [6,33,192,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12555 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12556 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1),(3,7),(4,7)], upper := (rows 7 35 196 104 273 160 90 154 282), lower := (rows 7 35 196 104 273 160 64 128 256), losses := [] }

theorem u12556 : Upper (D 7) (R 7) [6,33,192,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12557 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 104 274 33 216 152 408), lower := (rows 7 35 196 104 274 33 64 128 256), losses := [] }

theorem u12557 : Upper (D 7) (R 7) [6,33,192,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12558 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 196 104 274 40 209 145 401), lower := (rows 7 35 196 104 274 40 64 128 256), losses := [] }

theorem u12558 : Upper (D 7) (R 7) [6,33,192,96,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12558 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12559 : Route 9 := (fun mask => (mask,id))

def c12559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12559 : Upper (D 7) (R 7) [6,33,192,96,258,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,258,16] 13 (by decide) (choices 1) [1,8,128] r12559 c12559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1316
  · exact u1317
  · exact u1318

def b12560 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1),(3,7),(4,7)], upper := (rows 7 35 196 104 274 160 89 153 281), lower := (rows 7 35 196 104 274 160 64 128 256), losses := [] }

theorem u12560 : Upper (D 7) (R 7) [6,33,192,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12561 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 104 280 33 210 146 402), lower := (rows 7 35 196 104 280 33 64 128 256), losses := [] }

theorem u12561 : Upper (D 7) (R 7) [6,33,192,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12562 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 104 280 34 209 145 401), lower := (rows 7 35 196 104 280 34 64 128 256), losses := [] }

theorem u12562 : Upper (D 7) (R 7) [6,33,192,96,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12563 : Route 9 := (fun mask => (mask,id))

def c12563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12563 : Upper (D 7) (R 7) [6,33,192,96,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264,16] 13 (by decide) (choices 1) [1,2,128] r12563 c12563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1319
  · exact u1320
  · exact u1321

def b12564 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1),(3,7),(4,7)], upper := (rows 7 35 196 104 280 160 83 147 275), lower := (rows 7 35 196 104 280 160 64 128 256), losses := [] }

theorem u12564 : Upper (D 7) (R 7) [6,33,192,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12565 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 104 400 33 90 154 282), lower := (rows 7 35 196 104 400 33 64 128 256), losses := [] }

theorem u12565 : Upper (D 7) (R 7) [6,33,192,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12566 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 104 400 34 89 153 281), lower := (rows 7 35 196 104 400 34 64 128 256), losses := [] }

theorem u12566 : Upper (D 7) (R 7) [6,33,192,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12567 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 196 104 400 40 83 147 275), lower := (rows 7 35 196 104 400 40 64 128 256), losses := [] }

theorem u12567 : Upper (D 7) (R 7) [6,33,192,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12567 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12568 : Route 9 := (fun mask => (mask,id))

def c12568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12568 : Upper (D 7) (R 7) [6,33,192,96,384,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,384,16] 13 (by decide) (choices 1) [1,2,8] r12568 c12568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1322
  · exact u1323
  · exact u1324

def b12569 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 1, region := 452, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 261 26 208 40 224 224 480), lower := (rows 7 35 261 26 208 40 64 128 256), losses := [] }

theorem u12569 : Upper (D 7) (R 7) [6,33,257,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12569 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12570 : Route 9 := (fun mask => (mask,id))

def c12570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12570 : Upper (D 7) (R 7) [6,33,257,18,192,64] 13 := by
  apply FastRouting.sound _ _ [6,33,257,18,192,64] 13 (by decide) (choices 1) [8,32,128] r12570 c12570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1325
  · exact u1326
  · exact u1327

def b12571 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 261 56 82 40 192 192 448), lower := (rows 7 35 261 56 82 40 64 128 256), losses := [] }

theorem u12571 : Upper (D 7) (R 7) [6,33,257,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12571 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12572 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 261 56 82 96 200 136 392), lower := (rows 7 35 261 56 82 96 64 128 256), losses := [] }

theorem u12572 : Upper (D 7) (R 7) [6,33,257,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12573 : Route 9 := (fun mask => (mask,id))

def c12573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12573 : Upper (D 7) (R 7) [6,33,257,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,257,48,66,128] 13 (by decide) (choices 1) [8,128] r12573 c12573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1328
  · exact u1329

def b12574 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 261 56 208 34 200 200 456), lower := (rows 7 35 261 56 208 34 64 128 256), losses := [] }

theorem u12574 : Upper (D 7) (R 7) [6,33,257,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12575 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 35 261 56 208 40 194 194 450), lower := (rows 7 35 261 56 208 40 64 128 256), losses := [] }

theorem u12575 : Upper (D 7) (R 7) [6,33,257,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12575 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12576 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 261 56 208 96 202 138 394), lower := (rows 7 35 261 56 208 96 64 128 256), losses := [] }

theorem u12576 : Upper (D 7) (R 7) [6,33,257,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12577 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 74 112 40 208 144 400), lower := (rows 7 35 261 74 112 40 64 128 256), losses := [] }

theorem u12577 : Upper (D 7) (R 7) [6,33,257,66,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12577 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12578 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 261 74 112 48 200 136 392), lower := (rows 7 35 261 74 112 48 64 128 256), losses := [] }

theorem u12578 : Upper (D 7) (R 7) [6,33,257,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12578 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12579 : Route 9 := (fun mask => (mask,id))

def c12579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12579 : Upper (D 7) (R 7) [6,33,257,66,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,96,128] 13 (by decide) (choices 1) [8,16,128] r12579 c12579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1330
  · exact u1331
  · exact u1332

def b12580 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 1, region := 452, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 261 74 152 48 224 224 480), lower := (rows 7 35 261 74 152 48 64 128 256), losses := [] }

theorem u12580 : Upper (D 7) (R 7) [6,33,257,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12580 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12581 : Route 9 := (fun mask => (mask,id))

def c12581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12581 : Upper (D 7) (R 7) [6,33,257,66,136,64] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,136,64] 13 (by decide) (choices 1) [16,32,128] r12581 c12581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1333
  · exact u1334
  · exact u1335

def r12582 : Route 9 := (fun mask => (mask,id))

def c12582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12582 : Upper (D 7) (R 7) [6,33,257,66,136,128] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,136,128] 13 (by decide) (choices 1) [16,32] r12582 c12582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1336
  · exact u1337

def b12583 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 261 74 176 40 208 208 464), lower := (rows 7 35 261 74 176 40 64 128 256), losses := [] }

theorem u12583 : Upper (D 7) (R 7) [6,33,257,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12583 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12584 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 261 74 176 48 200 200 456), lower := (rows 7 35 261 74 176 48 64 128 256), losses := [] }

theorem u12584 : Upper (D 7) (R 7) [6,33,257,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12584 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12585 : Route 9 := (fun mask => (mask,id))

def c12585 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12585 : Upper (D 7) (R 7) [6,33,257,66,160,64] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,160,64] 13 (by decide) (choices 1) [8,16,128] r12585 c12585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1338
  · exact u1339
  · exact u1340

def b12586 : PairBound 9 := { available := 88, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 261 74 176 160 88 216 344), lower := (rows 7 35 261 74 176 160 64 128 256), losses := [] }

theorem u12586 : Upper (D 7) (R 7) [6,33,257,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12587 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 261 74 208 40 240 176 432), lower := (rows 7 35 261 74 208 40 64 128 256), losses := [] }

theorem u12587 : Upper (D 7) (R 7) [6,33,257,66,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12587 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12588 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 176, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 261 74 208 48 232 168 424), lower := (rows 7 35 261 74 208 48 64 128 256), losses := [] }

theorem u12588 : Upper (D 7) (R 7) [6,33,257,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12588 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12589 : Route 9 := (fun mask => (mask,id))

def c12589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12589 : Upper (D 7) (R 7) [6,33,257,66,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,192,128] 13 (by decide) (choices 1) [8,16,32] r12589 c12589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1341
  · exact u1342
  · exact u1343

def b12590 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 261 88 152 34 224 224 480), lower := (rows 7 35 261 88 152 34 64 128 256), losses := [] }

theorem u12590 : Upper (D 7) (R 7) [6,33,257,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12591 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 391, targets := 64 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 261 88 152 96 226 162 418), lower := (rows 7 35 261 88 152 96 64 128 256), losses := [] }

theorem u12591 : Upper (D 7) (R 7) [6,33,257,80,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12592 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 261 88 176 34 200 200 456), lower := (rows 7 35 261 88 176 34 64 128 256), losses := [] }

theorem u12592 : Upper (D 7) (R 7) [6,33,257,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12593 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 261 88 176 40 194 194 450), lower := (rows 7 35 261 88 176 40 64 128 256), losses := [] }

theorem u12593 : Upper (D 7) (R 7) [6,33,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12593 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12594 : Route 9 := (fun mask => (mask,id))

def c12594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12594 : Upper (D 7) (R 7) [6,33,257,80,160,64] 13 := by
  apply FastRouting.sound _ _ [6,33,257,80,160,64] 13 (by decide) (choices 1) [2,8,128] r12594 c12594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1344
  · exact u1345
  · exact u1346

def b12595 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 261 88 176 160 74 202 330), lower := (rows 7 35 261 88 176 160 64 128 256), losses := [] }

theorem u12595 : Upper (D 7) (R 7) [6,33,257,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12596 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 261 104 208 34 216 152 408), lower := (rows 7 35 261 104 208 34 64 128 256), losses := [] }

theorem u12596 : Upper (D 7) (R 7) [6,33,257,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12597 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 261 104 208 40 210 146 402), lower := (rows 7 35 261 104 208 40 64 128 256), losses := [] }

theorem u12597 : Upper (D 7) (R 7) [6,33,257,96,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12597 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12598 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 104 208 48 202 138 394), lower := (rows 7 35 261 104 208 48 64 128 256), losses := [] }

theorem u12598 : Upper (D 7) (R 7) [6,33,257,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12598 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12599 : Route 9 := (fun mask => (mask,id))

def c12599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12599 : Upper (D 7) (R 7) [6,33,257,96,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,257,96,192,128] 13 (by decide) (choices 1) [2,8,16] r12599 c12599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1347
  · exact u1348
  · exact u1349

#print axioms u12599
end Delivery.IrregularNine14.P07
