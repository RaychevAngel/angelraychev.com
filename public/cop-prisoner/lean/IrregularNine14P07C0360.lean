import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0106

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21600 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 35 322 13 56 145 160 70 198 326), lower := (rows 35 322 13 56 145 160 64 128 256), losses := [] }

theorem u21600 : Upper (D 7) (R 7) [34,320,9,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21601 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 56 146 33 196 196 452), lower := (rows 35 322 13 56 146 33 64 128 256), losses := [] }

theorem u21601 : Upper (D 7) (R 7) [34,320,9,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21602 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 56 146 36 193 193 449), lower := (rows 35 322 13 56 146 36 64 128 256), losses := [] }

theorem u21602 : Upper (D 7) (R 7) [34,320,9,48,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21602 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21603 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 56 146 96 197 133 389), lower := (rows 35 322 13 56 146 96 64 128 256), losses := [] }

theorem u21603 : Upper (D 7) (R 7) [34,320,9,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21604 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 322 13 56 146 160 69 197 325), lower := (rows 35 322 13 56 146 160 64 128 256), losses := [] }

theorem u21604 : Upper (D 7) (R 7) [34,320,9,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21605 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 13 56 148 33 194 194 450), lower := (rows 35 322 13 56 148 33 64 128 256), losses := [] }

theorem u21605 : Upper (D 7) (R 7) [34,320,9,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21606 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 56 148 34 193 193 449), lower := (rows 35 322 13 56 148 34 64 128 256), losses := [] }

theorem u21606 : Upper (D 7) (R 7) [34,320,9,48,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21607 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 56 148 96 195 131 387), lower := (rows 35 322 13 56 148 96 64 128 256), losses := [] }

theorem u21607 : Upper (D 7) (R 7) [34,320,9,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21608 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 322 13 56 148 160 67 195 323), lower := (rows 35 322 13 56 148 160 64 128 256), losses := [] }

theorem u21608 : Upper (D 7) (R 7) [34,320,9,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21609 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 13 56 208 33 198 134 390), lower := (rows 35 322 13 56 208 33 64 128 256), losses := [] }

theorem u21609 : Upper (D 7) (R 7) [34,320,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21610 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 56 208 34 197 133 389), lower := (rows 35 322 13 56 208 34 64 128 256), losses := [] }

theorem u21610 : Upper (D 7) (R 7) [34,320,9,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21611 : Route 9 := (fun mask => (mask,id))

def c21611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21611 : Upper (D 7) (R 7) [34,320,9,48,192,4] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,192,4] 13 (by decide) (choices 1) [1,2,128] r21611 c21611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6374
  · exact u6375
  · exact u6376

def b21612 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 322 13 56 208 160 71 135 263), lower := (rows 35 322 13 56 208 160 64 128 256), losses := [] }

theorem u21612 : Upper (D 7) (R 7) [34,320,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21613 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 76 145 34 240 176 432), lower := (rows 35 322 13 76 145 34 64 128 256), losses := [] }

theorem u21613 : Upper (D 7) (R 7) [34,320,9,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21614 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 322 13 76 145 48 226 162 418), lower := (rows 35 322 13 76 145 48 64 128 256), losses := [] }

theorem u21614 : Upper (D 7) (R 7) [34,320,9,68,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21614 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21615 : Route 9 := (fun mask => (mask,id))

def c21615 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21615 : Upper (D 7) (R 7) [34,320,9,68,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,68,129,128] 13 (by decide) (choices 1) [2,16,32] r21615 c21615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6377
  · exact u6378
  · exact u6379

def b21616 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 322 13 76 146 33 240 176 432), lower := (rows 35 322 13 76 146 33 64 128 256), losses := [] }

theorem u21616 : Upper (D 7) (R 7) [34,320,9,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21617 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 322 13 76 146 48 225 161 417), lower := (rows 35 322 13 76 146 48 64 128 256), losses := [] }

theorem u21617 : Upper (D 7) (R 7) [34,320,9,68,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21617 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21618 : Route 9 := (fun mask => (mask,id))

def c21618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21618 : Upper (D 7) (R 7) [34,320,9,68,130,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,68,130,128] 13 (by decide) (choices 1) [1,16,32] r21618 c21618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6380
  · exact u6381
  · exact u6382

def b21619 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 322 13 76 176 33 210 146 402), lower := (rows 35 322 13 76 176 33 64 128 256), losses := [] }

theorem u21619 : Upper (D 7) (R 7) [34,320,9,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21620 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 76 176 34 209 145 401), lower := (rows 35 322 13 76 176 34 64 128 256), losses := [] }

theorem u21620 : Upper (D 7) (R 7) [34,320,9,68,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21621 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 13 76 176 48 195 131 387), lower := (rows 35 322 13 76 176 48 64 128 256), losses := [] }

theorem u21621 : Upper (D 7) (R 7) [34,320,9,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21621 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21622 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 13 76 176 160 83 147 275), lower := (rows 35 322 13 76 176 160 64 128 256), losses := [] }

theorem u21622 : Upper (D 7) (R 7) [34,320,9,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21623 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 88 22 33 224 160 416), lower := (rows 35 322 13 88 22 33 64 128 256), losses := [] }

theorem u21623 : Upper (D 7) (R 7) [34,320,9,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21624 : Route 9 := (fun mask => (mask,id))

def c21624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21624 : Upper (D 7) (R 7) [34,320,9,80,6,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,6,128] 13 (by decide) (choices 1) [1,32,128] r21624 c21624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6383
  · exact u6384
  · exact u6385

def b21625 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 88 145 34 228 164 420), lower := (rows 35 322 13 88 145 34 64 128 256), losses := [] }

theorem u21625 : Upper (D 7) (R 7) [34,320,9,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21626 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 35 322 13 88 145 36 226 162 418), lower := (rows 35 322 13 88 145 36 64 128 256), losses := [{ target := 0, region := (rows 0 55 4 24 16 36 101 165 293), good := (rows 482 322 494 90 474 486 64 128 256) }] }

theorem u21626 : Upper (D 7) (R 7) [34,320,9,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21626 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21627 : Route 9 := (fun mask => (mask,id))

def c21627 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21627 : Upper (D 7) (R 7) [34,320,9,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,129,128] 13 (by decide) (choices 1) [2,4,32] r21627 c21627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6386
  · exact u6387
  · exact u6388

def b21628 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 88 146 33 228 164 420), lower := (rows 35 322 13 88 146 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 63 0 140 268), good := (rows 35 291 429 445 179 33 0 128 256) },{ target := 7, region := (rows 19 2 12 8 16 63 64 0 256), good := (rows 35 355 45 125 51 33 64 0 256) }] }

theorem u21628 : Upper (D 7) (R 7) [34,320,9,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21629 : Route 9 := (fun mask => (mask,id))

def c21629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21629 : Upper (D 7) (R 7) [34,320,9,80,130,4] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,130,4] 13 (by decide) (choices 1) [1,32,128] r21629 c21629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6389
  · exact u6390
  · exact u6391

def r21630 : Route 9 := (fun mask => (mask,id))

def c21630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21630 : Upper (D 7) (R 7) [34,320,9,80,130,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,130,128] 13 (by decide) (choices 1) [1,4,32] r21630 c21630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6392
  · exact u6393
  · exact u6394

def b21631 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 322 13 88 148 33 226 162 418), lower := (rows 35 322 13 88 148 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 322 478 88 158 482 64 128 256) }] }

theorem u21631 : Upper (D 7) (R 7) [34,320,9,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21632 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 88 148 34 225 161 417), lower := (rows 35 322 13 88 148 34 64 128 256), losses := [] }

theorem u21632 : Upper (D 7) (R 7) [34,320,9,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21633 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 13 88 148 160 99 163 291), lower := (rows 35 322 13 88 148 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 20 183 0 131 259), good := (rows 419 419 445 56 180 160 0 160 256) }] }

theorem u21633 : Upper (D 7) (R 7) [34,320,9,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21634 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 322 13 88 176 33 198 134 390), lower := (rows 35 322 13 88 176 33 64 128 256), losses := [] }

theorem u21634 : Upper (D 7) (R 7) [34,320,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21635 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 88 176 34 197 133 389), lower := (rows 35 322 13 88 176 34 64 128 256), losses := [] }

theorem u21635 : Upper (D 7) (R 7) [34,320,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21636 : Route 9 := (fun mask => (mask,id))

def c21636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21636 : Upper (D 7) (R 7) [34,320,9,80,160,4] 13 := by
  apply FastRouting.sound _ _ [34,320,9,80,160,4] 13 (by decide) (choices 1) [1,2,128] r21636 c21636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6395
  · exact u6396
  · exact u6397

def b21637 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 13 88 176 160 71 135 263), lower := (rows 35 322 13 88 176 160 64 128 256), losses := [] }

theorem u21637 : Upper (D 7) (R 7) [34,320,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21638 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 13 104 22 33 208 144 400), lower := (rows 35 322 13 104 22 33 64 128 256), losses := [] }

theorem u21638 : Upper (D 7) (R 7) [34,320,9,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21639 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 13 104 22 48 193 129 385), lower := (rows 35 322 13 104 22 48 64 128 256), losses := [] }

theorem u21639 : Upper (D 7) (R 7) [34,320,9,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21639 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21640 : Route 9 := (fun mask => (mask,id))

def c21640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21640 : Upper (D 7) (R 7) [34,320,9,96,6,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,96,6,128] 13 (by decide) (choices 1) [1,16,128] r21640 c21640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6398
  · exact u6399
  · exact u6400

def b21641 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 104 145 34 212 148 404), lower := (rows 35 322 13 104 145 34 64 128 256), losses := [] }

theorem u21641 : Upper (D 7) (R 7) [34,320,9,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21642 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 13 104 145 36 210 146 402), lower := (rows 35 322 13 104 145 36 64 128 256), losses := [] }

theorem u21642 : Upper (D 7) (R 7) [34,320,9,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21642 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21643 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 322 13 104 145 48 198 134 390), lower := (rows 35 322 13 104 145 48 64 128 256), losses := [] }

theorem u21643 : Upper (D 7) (R 7) [34,320,9,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21643 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21644 : Route 9 := (fun mask => (mask,id))

def c21644 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21644 : Upper (D 7) (R 7) [34,320,9,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,96,129,128] 13 (by decide) (choices 1) [2,4,16] r21644 c21644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6401
  · exact u6402
  · exact u6403

def b21645 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 13 104 146 33 212 148 404), lower := (rows 35 322 13 104 146 33 64 128 256), losses := [] }

theorem u21645 : Upper (D 7) (R 7) [34,320,9,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21646 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 13 104 146 36 209 145 401), lower := (rows 35 322 13 104 146 36 64 128 256), losses := [] }

theorem u21646 : Upper (D 7) (R 7) [34,320,9,96,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21646 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21647 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 322 13 104 146 48 197 133 389), lower := (rows 35 322 13 104 146 48 64 128 256), losses := [] }

theorem u21647 : Upper (D 7) (R 7) [34,320,9,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21647 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21648 : Route 9 := (fun mask => (mask,id))

def c21648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21648 : Upper (D 7) (R 7) [34,320,9,96,130,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,96,130,128] 13 (by decide) (choices 1) [1,4,16] r21648 c21648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6404
  · exact u6405
  · exact u6406

def b21649 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 13 104 148 33 210 146 402), lower := (rows 35 322 13 104 148 33 64 128 256), losses := [] }

theorem u21649 : Upper (D 7) (R 7) [34,320,9,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21650 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 104 148 34 209 145 401), lower := (rows 35 322 13 104 148 34 64 128 256), losses := [] }

theorem u21650 : Upper (D 7) (R 7) [34,320,9,96,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21651 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,5),(4,6)], upper := (rows 35 322 13 104 148 48 195 131 387), lower := (rows 35 322 13 104 148 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 52 0 129 257), good := (rows 419 258 445 40 180 48 0 128 256) }] }

theorem u21651 : Upper (D 7) (R 7) [34,320,9,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21651 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21652 : Route 9 := (fun mask => (mask,id))

def c21652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21652 : Upper (D 7) (R 7) [34,320,9,96,132,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,96,132,128] 13 (by decide) (choices 1) [1,2,16] r21652 c21652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6407
  · exact u6408
  · exact u6409

def b21653 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 138 52 33 208 208 464), lower := (rows 35 322 13 138 52 33 64 128 256), losses := [] }

theorem u21653 : Upper (D 7) (R 7) [34,320,9,130,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21654 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 138 52 48 193 193 449), lower := (rows 35 322 13 138 52 48 64 128 256), losses := [] }

theorem u21654 : Upper (D 7) (R 7) [34,320,9,130,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21654 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21655 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 138 52 96 209 145 401), lower := (rows 35 322 13 138 52 96 64 128 256), losses := [] }

theorem u21655 : Upper (D 7) (R 7) [34,320,9,130,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21656 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 35 322 13 138 52 160 81 209 337), lower := (rows 35 322 13 138 52 160 64 128 256), losses := [] }

theorem u21656 : Upper (D 7) (R 7) [34,320,9,130,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21657 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 138 81 36 240 176 432), lower := (rows 35 322 13 138 81 36 64 128 256), losses := [] }

theorem u21657 : Upper (D 7) (R 7) [34,320,9,130,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21657 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21658 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 13 138 81 48 228 164 420), lower := (rows 35 322 13 138 81 48 64 128 256), losses := [] }

theorem u21658 : Upper (D 7) (R 7) [34,320,9,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21658 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21659 : Route 9 := (fun mask => (mask,id))

def c21659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21659 : Upper (D 7) (R 7) [34,320,9,130,65,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,65,128] 13 (by decide) (choices 1) [4,16,32] r21659 c21659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6410
  · exact u6411
  · exact u6412

#print axioms u21659
end Delivery.IrregularNine14.P07
