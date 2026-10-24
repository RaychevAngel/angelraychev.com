import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0105
import IrregularNine14P07C0106

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21540 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 41, targets := 64 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 196 56 82 33 201 137 393), lower := (rows 35 262 196 56 82 33 64 128 256), losses := [] }

theorem u21540 : Upper (D 7) (R 7) [34,260,192,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21541 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 196 56 82 40 193 129 385), lower := (rows 35 262 196 56 82 40 64 128 256), losses := [] }

theorem u21541 : Upper (D 7) (R 7) [34,260,192,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21541 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21542 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(3,6),(3,7),(4,7)], upper := (rows 35 262 196 56 82 160 73 137 265), lower := (rows 35 262 196 56 82 160 64 128 256), losses := [] }

theorem u21542 : Upper (D 7) (R 7) [34,260,192,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21543 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 196 73 145 34 120 184 312), lower := (rows 35 262 196 73 145 34 64 128 256), losses := [] }

theorem u21543 : Upper (D 7) (R 7) [34,260,192,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21544 : Route 9 := (fun mask => (mask,id))

def c21544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21544 : Upper (D 7) (R 7) [34,260,192,65,129,8] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,129,8] 13 (by decide) (choices 1) [2,16,32] r21544 c21544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6332
  · exact u6333
  · exact u6334

def r21545 : Route 9 := (fun mask => (mask,id))

def c21545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21545 : Upper (D 7) (R 7) [34,260,192,65,130,1] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,130,1] 13 (by decide) (choices 1) [8,16,32] r21545 c21545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6335
  · exact u6336
  · exact u6337

def b21546 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,7),(3,7),(4,6)], upper := (rows 35 262 196 73 146 40 113 177 305), lower := (rows 35 262 196 73 146 40 64 128 256), losses := [] }

theorem u21546 : Upper (D 7) (R 7) [34,260,192,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21546 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21547 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 262 196 73 146 48 105 169 297), lower := (rows 35 262 196 73 146 48 64 128 256), losses := [] }

theorem u21547 : Upper (D 7) (R 7) [34,260,192,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21547 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21548 : Route 9 := (fun mask => (mask,id))

def c21548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21548 : Upper (D 7) (R 7) [34,260,192,65,136,1] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,136,1] 13 (by decide) (choices 1) [2,16,32] r21548 c21548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6338
  · exact u6339
  · exact u6340

def b21549 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 196 73 152 34 113 177 305), lower := (rows 35 262 196 73 152 34 64 128 256), losses := [] }

theorem u21549 : Upper (D 7) (R 7) [34,260,192,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21550 : Route 9 := (fun mask => (mask,id))

def c21550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21550 : Upper (D 7) (R 7) [34,260,192,65,136,16] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,136,16] 13 (by decide) (choices 1) [1,2,32] r21550 c21550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6341
  · exact u6342
  · exact u6343

def r21551 : Route 9 := (fun mask => (mask,id))

def c21551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21551 : Upper (D 7) (R 7) [34,260,192,65,160,1] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,160,1] 13 (by decide) (choices 1) [2,8,16] r21551 c21551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6344
  · exact u6345
  · exact u6346

def b21552 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 196 73 176 34 89 153 281), lower := (rows 35 262 196 73 176 34 64 128 256), losses := [] }

theorem u21552 : Upper (D 7) (R 7) [34,260,192,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21553 : Route 9 := (fun mask => (mask,id))

def c21553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21553 : Upper (D 7) (R 7) [34,260,192,65,160,8] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,160,8] 13 (by decide) (choices 1) [1,2,16] r21553 c21553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6347
  · exact u6348
  · exact u6349

def b21554 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 196 73 176 48 75 139 267), lower := (rows 35 262 196 73 176 48 64 128 256), losses := [] }

theorem u21554 : Upper (D 7) (R 7) [34,260,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21554 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21555 : Route 9 := (fun mask => (mask,id))

def c21555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21555 : Upper (D 7) (R 7) [34,260,192,66,136,1] 13 := by
  apply FastRouting.sound _ _ [34,260,192,66,136,1] 13 (by decide) (choices 1) [1,16,32] r21555 c21555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6350
  · exact u6351
  · exact u6352

def b21556 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 177, targets := 64 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 262 196 74 152 48 97 161 289), lower := (rows 35 262 196 74 152 48 64 128 256), losses := [] }

theorem u21556 : Upper (D 7) (R 7) [34,260,192,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21556 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21557 : Route 9 := (fun mask => (mask,id))

def c21557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21557 : Upper (D 7) (R 7) [34,260,192,66,160,1] 13 := by
  apply FastRouting.sound _ _ [34,260,192,66,160,1] 13 (by decide) (choices 1) [1,8,16] r21557 c21557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6353
  · exact u6354
  · exact u6355

def b21558 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 262 196 74 176 40 81 145 273), lower := (rows 35 262 196 74 176 40 64 128 256), losses := [] }

theorem u21558 : Upper (D 7) (R 7) [34,260,192,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21558 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21559 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 196 74 176 48 73 137 265), lower := (rows 35 262 196 74 176 48 64 128 256), losses := [] }

theorem u21559 : Upper (D 7) (R 7) [34,260,192,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21559 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21560 : Route 9 := (fun mask => (mask,id))

def c21560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21560 : Upper (D 7) (R 7) [34,260,192,80,160,1] 13 := by
  apply FastRouting.sound _ _ [34,260,192,80,160,1] 13 (by decide) (choices 1) [1,2,8] r21560 c21560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6356
  · exact u6357
  · exact u6358

def b21561 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 196 88 176 34 73 137 265), lower := (rows 35 262 196 88 176 34 64 128 256), losses := [] }

theorem u21561 : Upper (D 7) (R 7) [34,260,192,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21562 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 262 196 88 176 40 67 131 259), lower := (rows 35 262 196 88 176 40 64 128 256), losses := [] }

theorem u21562 : Upper (D 7) (R 7) [34,260,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21562 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21563 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 26 84 33 224 160 416), lower := (rows 35 322 13 26 84 33 64 128 256), losses := [] }

theorem u21563 : Upper (D 7) (R 7) [34,320,9,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21564 : Route 9 := (fun mask => (mask,id))

def c21564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21564 : Upper (D 7) (R 7) [34,320,9,18,68,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,18,68,128] 13 (by decide) (choices 1) [1,32,128] r21564 c21564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6359
  · exact u6360
  · exact u6361

def b21565 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 26 145 36 224 224 480), lower := (rows 35 322 13 26 145 36 64 128 256), losses := [] }

theorem u21565 : Upper (D 7) (R 7) [34,320,9,18,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21565 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21566 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 26 145 96 228 164 420), lower := (rows 35 322 13 26 145 96 64 128 256), losses := [] }

theorem u21566 : Upper (D 7) (R 7) [34,320,9,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21567 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 482, targets := 1 },{ cop := 2, region := 240, targets := 2 }], pairs := [(0,6),(1,0),(2,6),(4,1)], upper := (rows 35 322 13 26 145 160 100 228 356), lower := (rows 35 322 13 26 145 160 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 35 258 13 63 177 160 0 160 256) }] }

theorem u21567 : Upper (D 7) (R 7) [34,320,9,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21568 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 26 148 33 224 224 480), lower := (rows 35 322 13 26 148 33 64 128 256), losses := [] }

theorem u21568 : Upper (D 7) (R 7) [34,320,9,18,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21569 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 26 148 96 225 161 417), lower := (rows 35 322 13 26 148 96 64 128 256), losses := [] }

theorem u21569 : Upper (D 7) (R 7) [34,320,9,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21570 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 2, region := 240, targets := 2 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 13 26 148 160 97 225 353), lower := (rows 35 322 13 26 148 160 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 35 258 13 63 180 160 0 160 256) }] }

theorem u21570 : Upper (D 7) (R 7) [34,320,9,18,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21571 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 26 176 33 196 196 452), lower := (rows 35 322 13 26 176 33 64 128 256), losses := [] }

theorem u21571 : Upper (D 7) (R 7) [34,320,9,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21572 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 26 176 36 193 193 449), lower := (rows 35 322 13 26 176 36 64 128 256), losses := [] }

theorem u21572 : Upper (D 7) (R 7) [34,320,9,18,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21572 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21573 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 26 176 96 197 133 389), lower := (rows 35 322 13 26 176 96 64 128 256), losses := [] }

theorem u21573 : Upper (D 7) (R 7) [34,320,9,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21574 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 13 26 176 160 69 197 325), lower := (rows 35 322 13 26 176 160 64 128 256), losses := [] }

theorem u21574 : Upper (D 7) (R 7) [34,320,9,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21575 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 240, targets := 2 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(0,7),(2,6),(4,1)], upper := (rows 35 322 13 26 208 33 228 164 420), lower := (rows 35 322 13 26 208 33 64 128 256), losses := [] }

theorem u21575 : Upper (D 7) (R 7) [34,320,9,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21576 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 26 208 36 225 161 417), lower := (rows 35 322 13 26 208 36 64 128 256), losses := [] }

theorem u21576 : Upper (D 7) (R 7) [34,320,9,18,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21576 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21577 : Route 9 := (fun mask => (mask,id))

def c21577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21577 : Upper (D 7) (R 7) [34,320,9,18,192,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,18,192,128] 13 (by decide) (choices 1) [1,4,32] r21577 c21577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6362
  · exact u6363
  · exact u6364

def b21578 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 28 112 33 194 130 386), lower := (rows 35 322 13 28 112 33 64 128 256), losses := [] }

theorem u21578 : Upper (D 7) (R 7) [34,320,9,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21579 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 28 112 34 193 129 385), lower := (rows 35 322 13 28 112 34 64 128 256), losses := [] }

theorem u21579 : Upper (D 7) (R 7) [34,320,9,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21580 : Route 9 := (fun mask => (mask,id))

def c21580 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21580 : Upper (D 7) (R 7) [34,320,9,20,96,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20,96,128] 13 (by decide) (choices 1) [1,2,128] r21580 c21580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6365
  · exact u6366
  · exact u6367

def b21581 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 28 146 33 224 224 480), lower := (rows 35 322 13 28 146 33 64 128 256), losses := [] }

theorem u21581 : Upper (D 7) (R 7) [34,320,9,20,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21582 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 28 146 96 225 161 417), lower := (rows 35 322 13 28 146 96 64 128 256), losses := [] }

theorem u21582 : Upper (D 7) (R 7) [34,320,9,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21583 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 322 13 28 146 160 97 225 353), lower := (rows 35 322 13 28 146 160 64 128 256), losses := [] }

theorem u21583 : Upper (D 7) (R 7) [34,320,9,20,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21584 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 322 13 28 176 33 194 194 450), lower := (rows 35 322 13 28 176 33 64 128 256), losses := [] }

theorem u21584 : Upper (D 7) (R 7) [34,320,9,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21585 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 28 176 34 193 193 449), lower := (rows 35 322 13 28 176 34 64 128 256), losses := [] }

theorem u21585 : Upper (D 7) (R 7) [34,320,9,20,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21586 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 28 176 96 195 131 387), lower := (rows 35 322 13 28 176 96 64 128 256), losses := [] }

theorem u21586 : Upper (D 7) (R 7) [34,320,9,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21587 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 13 28 176 160 67 195 323), lower := (rows 35 322 13 28 176 160 64 128 256), losses := [] }

theorem u21587 : Upper (D 7) (R 7) [34,320,9,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21588 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 322 13 28 208 33 226 162 418), lower := (rows 35 322 13 28 208 33 64 128 256), losses := [] }

theorem u21588 : Upper (D 7) (R 7) [34,320,9,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21589 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 28 208 34 225 161 417), lower := (rows 35 322 13 28 208 34 64 128 256), losses := [] }

theorem u21589 : Upper (D 7) (R 7) [34,320,9,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21590 : Route 9 := (fun mask => (mask,id))

def c21590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21590 : Upper (D 7) (R 7) [34,320,9,20,192,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20,192,128] 13 (by decide) (choices 1) [1,2,32] r21590 c21590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6368
  · exact u6369
  · exact u6370

def b21591 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 56 81 34 196 132 388), lower := (rows 35 322 13 56 81 34 64 128 256), losses := [] }

theorem u21591 : Upper (D 7) (R 7) [34,320,9,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21592 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 44, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 35 322 13 56 81 36 194 130 386), lower := (rows 35 322 13 56 81 36 64 128 256), losses := [] }

theorem u21592 : Upper (D 7) (R 7) [34,320,9,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21592 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21593 : Route 9 := (fun mask => (mask,id))

def c21593 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21593 : Upper (D 7) (R 7) [34,320,9,48,65,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,65,128] 13 (by decide) (choices 1) [2,4,128] r21593 c21593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6371
  · exact u6372
  · exact u6373

def b21594 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 56 84 33 194 130 386), lower := (rows 35 322 13 56 84 33 64 128 256), losses := [] }

theorem u21594 : Upper (D 7) (R 7) [34,320,9,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21595 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 56 84 34 193 129 385), lower := (rows 35 322 13 56 84 34 64 128 256), losses := [] }

theorem u21595 : Upper (D 7) (R 7) [34,320,9,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21596 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(3,6),(4,5)], upper := (rows 35 322 13 56 84 160 195 131 387), lower := (rows 35 322 13 56 84 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 24 16 167 0 131 259), good := (rows 419 419 429 56 60 160 0 160 256) }] }

theorem u21596 : Upper (D 7) (R 7) [34,320,9,48,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21597 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 56 145 34 196 196 452), lower := (rows 35 322 13 56 145 34 64 128 256), losses := [] }

theorem u21597 : Upper (D 7) (R 7) [34,320,9,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21598 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 44, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 35 322 13 56 145 36 194 194 450), lower := (rows 35 322 13 56 145 36 64 128 256), losses := [] }

theorem u21598 : Upper (D 7) (R 7) [34,320,9,48,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21598 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21599 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 56 145 96 198 134 390), lower := (rows 35 322 13 56 145 96 64 128 256), losses := [] }

theorem u21599 : Upper (D 7) (R 7) [34,320,9,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21599
end Delivery.IrregularNine14.P07
