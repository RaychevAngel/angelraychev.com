import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0190
import IrregularNine14P07C0191

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29640 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 290 14 137 84 33 210 146 402), lower := (rows 97 290 14 137 84 33 64 128 256), losses := [] }

theorem u29640 : Upper (D 7) (R 7) [96,288,10,129,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29641 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 14 137 84 34 209 145 401), lower := (rows 97 290 14 137 84 34 64 128 256), losses := [{ target := 7, region := (rows 17 258 4 8 16 294 64 0 256), good := (rows 97 290 46 9 117 34 64 0 290) }] }

theorem u29641 : Upper (D 7) (R 7) [96,288,10,129,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29642 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 137 84 48 195 131 387), lower := (rows 97 290 14 137 84 48 64 128 256), losses := [] }

theorem u29642 : Upper (D 7) (R 7) [96,288,10,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29642 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29643 : Route 9 := (fun mask => (mask,id))

def c29643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29643 : Upper (D 7) (R 7) [96,288,10,129,68,128] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,68,128] 13 (by decide) (choices 1) [1,2,16] r29643 c29643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11435
  · exact u11436
  · exact u11437

def b29644 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 290 14 137 146 33 84 212 340), lower := (rows 97 290 14 137 146 33 64 128 256), losses := [] }

theorem u29644 : Upper (D 7) (R 7) [96,288,10,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29645 : Route 9 := (fun mask => (mask,id))

def c29645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29645 : Upper (D 7) (R 7) [96,288,10,129,130,4] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,130,4] 13 (by decide) (choices 1) [1,16] r29645 c29645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11438
  · exact u11439

def r29646 : Route 9 := (fun mask => (mask,id))

def c29646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29646 : Upper (D 7) (R 7) [96,288,10,129,130,16] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,130,16] 13 (by decide) (choices 1) [1,4] r29646 c29646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11440
  · exact u11441

def b29647 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 14 137 146 96 85 149 277), lower := (rows 97 290 14 137 146 96 64 128 256), losses := [] }

theorem u29647 : Upper (D 7) (R 7) [96,288,10,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29648 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 97 290 14 137 148 33 82 210 338), lower := (rows 97 290 14 137 148 33 64 128 256), losses := [] }

theorem u29648 : Upper (D 7) (R 7) [96,288,10,129,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29649 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 14 137 148 34 81 209 337), lower := (rows 97 290 14 137 148 34 64 128 256), losses := [] }

theorem u29649 : Upper (D 7) (R 7) [96,288,10,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29650 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 14 137 148 48 67 195 323), lower := (rows 97 290 14 137 148 48 64 128 256), losses := [{ target := 7, region := (rows 51 51 12 8 16 48 127 0 319), good := (rows 355 355 335 335 375 371 64 0 256) }] }

theorem u29650 : Upper (D 7) (R 7) [96,288,10,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29650 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29651 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 14 137 148 96 83 147 275), lower := (rows 97 290 14 137 148 96 64 128 256), losses := [] }

theorem u29651 : Upper (D 7) (R 7) [96,288,10,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29652 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 41, targets := 2 }], pairs := [(0,1),(3,1),(4,0),(4,5)], upper := (rows 97 290 14 137 208 33 86 150 278), lower := (rows 97 290 14 137 208 33 64 128 256), losses := [] }

theorem u29652 : Upper (D 7) (R 7) [96,288,10,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29653 : Route 9 := (fun mask => (mask,id))

def c29653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29653 : Upper (D 7) (R 7) [96,288,10,129,192,2] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,192,2] 13 (by decide) (choices 1) [1,4,16] r29653 c29653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11442
  · exact u11443
  · exact u11444

def r29654 : Route 9 := (fun mask => (mask,id))

def c29654 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29654 : Upper (D 7) (R 7) [96,288,10,129,192,4] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,192,4] 13 (by decide) (choices 1) [1,2,16] r29654 c29654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11445
  · exact u11446
  · exact u11447

def b29655 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 137 208 48 71 135 263), lower := (rows 97 290 14 137 208 48 64 128 256), losses := [] }

theorem u29655 : Upper (D 7) (R 7) [96,288,10,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29655 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29656 : Route 9 := (fun mask => (mask,id))

def c29656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29656 : Upper (D 7) (R 7) [96,288,10,132,66,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,132,66,1] 13 (by decide) (choices 1) [1,16,128] r29656 c29656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11448
  · exact u11449
  · exact u11450

def b29657 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 140 82 48 193 129 385), lower := (rows 97 290 14 140 82 48 64 128 256), losses := [] }

theorem u29657 : Upper (D 7) (R 7) [96,288,10,132,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29657 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29658 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 4, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 97 290 14 140 82 160 81 145 273), lower := (rows 97 290 14 140 82 160 64 128 256), losses := [] }

theorem u29658 : Upper (D 7) (R 7) [96,288,10,132,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29659 : Route 9 := (fun mask => (mask,id))

def c29659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29659 : Upper (D 7) (R 7) [96,288,10,132,129,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,132,129,1] 13 (by decide) (choices 1) [2,16] r29659 c29659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11451
  · exact u11452

def b29660 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 14 140 145 34 81 209 337), lower := (rows 97 290 14 140 145 34 64 128 256), losses := [] }

theorem u29660 : Upper (D 7) (R 7) [96,288,10,132,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29661 : Route 9 := (fun mask => (mask,id))

def c29661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29661 : Upper (D 7) (R 7) [96,288,10,132,129,16] 13 := by
  apply FastRouting.sound _ _ [96,288,10,132,129,16] 13 (by decide) (choices 1) [1,2] r29661 c29661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11453
  · exact u11454

def b29662 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 14 140 145 96 83 147 275), lower := (rows 97 290 14 140 145 96 64 128 256), losses := [] }

theorem u29662 : Upper (D 7) (R 7) [96,288,10,132,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29663 : Route 9 := (fun mask => (mask,id))

def c29663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29663 : Upper (D 7) (R 7) [96,288,10,132,192,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,132,192,1] 13 (by decide) (choices 1) [1,2,16] r29663 c29663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11455
  · exact u11456
  · exact u11457

def b29664 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 14 140 208 34 81 145 273), lower := (rows 97 290 14 140 208 34 64 128 256), losses := [] }

theorem u29664 : Upper (D 7) (R 7) [96,288,10,132,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29665 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 140 208 48 67 131 259), lower := (rows 97 290 14 140 208 48 64 128 256), losses := [] }

theorem u29665 : Upper (D 7) (R 7) [96,288,10,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29665 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29666 : Route 9 := (fun mask => (mask,id))

def c29666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29666 : Upper (D 7) (R 7) [96,288,10,144,66,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,144,66,1] 13 (by decide) (choices 1) [1,4,128] r29666 c29666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11458
  · exact u11459
  · exact u11460

def b29667 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 386, targets := 64 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,6),(3,1)], upper := (rows 97 290 14 152 82 36 193 129 385), lower := (rows 97 290 14 152 82 36 64 128 256), losses := [{ target := 1, region := (rows 39 0 4 24 16 36 119 183 311), good := (rows 481 481 493 472 473 485 64 128 256) }] }

theorem u29667 : Upper (D 7) (R 7) [96,288,10,144,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29667 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29668 : Route 9 := (fun mask => (mask,id))

def c29668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29668 : Upper (D 7) (R 7) [96,288,10,144,66,128] 13 := by
  apply FastRouting.sound _ _ [96,288,10,144,66,128] 13 (by decide) (choices 1) [1,4] r29668 c29668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11461
  · exact u11462

def r29669 : Route 9 := (fun mask => (mask,id))

def c29669 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29669 : Upper (D 7) (R 7) [96,288,10,144,68,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,144,68,1] 13 (by decide) (choices 1) [1,2,128] r29669 c29669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11463
  · exact u11464
  · exact u11465

def b29670 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(1,7)], upper := (rows 97 290 14 152 84 34 193 129 385), lower := (rows 97 290 14 152 84 34 64 128 256), losses := [] }

theorem u29670 : Upper (D 7) (R 7) [96,288,10,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29671 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(4,7)], upper := (rows 97 290 14 152 84 160 67 131 259), lower := (rows 97 290 14 152 84 160 64 128 256), losses := [{ target := 7, region := (rows 35 35 4 8 20 32 103 0 295), good := (rows 355 355 351 24 340 355 64 0 256) }] }

theorem u29671 : Upper (D 7) (R 7) [96,288,10,144,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29672 : Route 9 := (fun mask => (mask,id))

def c29672 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29672 : Upper (D 7) (R 7) [96,288,10,192,129,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,129,1] 13 (by decide) (choices 1) [2,4,16] r29672 c29672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11466
  · exact u11467
  · exact u11468

def r29673 : Route 9 := (fun mask => (mask,id))

def c29673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29673 : Upper (D 7) (R 7) [96,288,10,192,129,2] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,129,2] 13 (by decide) (choices 1) [1,4,16] r29673 c29673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11469
  · exact u11470
  · exact u11471

def r29674 : Route 9 := (fun mask => (mask,id))

def c29674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29674 : Upper (D 7) (R 7) [96,288,10,192,129,4] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,129,4] 13 (by decide) (choices 1) [1,2,16] r29674 c29674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11472
  · exact u11473
  · exact u11474

def r29675 : Route 9 := (fun mask => (mask,id))

def c29675 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29675 : Upper (D 7) (R 7) [96,288,10,192,129,16] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,129,16] 13 (by decide) (choices 1) [1,2,4] r29675 c29675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11475
  · exact u11476
  · exact u11477

def r29676 : Route 9 := (fun mask => (mask,id))

def c29676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29676 : Upper (D 7) (R 7) [96,288,10,192,130,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,130,1] 13 (by decide) (choices 1) [1,4,16] r29676 c29676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11478
  · exact u11479
  · exact u11480

def r29677 : Route 9 := (fun mask => (mask,id))

def c29677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29677 : Upper (D 7) (R 7) [96,288,10,192,130,4] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,130,4] 13 (by decide) (choices 1) [1,16] r29677 c29677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11481
  · exact u11482

def r29678 : Route 9 := (fun mask => (mask,id))

def c29678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29678 : Upper (D 7) (R 7) [96,288,10,192,130,16] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,130,16] 13 (by decide) (choices 1) [1,4] r29678 c29678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11483
  · exact u11484

def r29679 : Route 9 := (fun mask => (mask,id))

def c29679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29679 : Upper (D 7) (R 7) [96,288,10,192,132,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192,132,1] 13 (by decide) (choices 1) [1,2,16] r29679 c29679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11485
  · exact u11486
  · exact u11487

def b29680 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 14 200 148 34 81 145 273), lower := (rows 97 290 14 200 148 34 64 128 256), losses := [] }

theorem u29680 : Upper (D 7) (R 7) [96,288,10,192,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29681 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,7),(1,6),(1,7)], upper := (rows 97 290 14 200 148 48 67 131 259), lower := (rows 97 290 14 200 148 48 64 128 256), losses := [] }

theorem u29681 : Upper (D 7) (R 7) [96,288,10,192,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29681 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29682 : Route 9 := (fun mask => (mask,id))

def c29682 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29682 : Upper (D 7) (R 7) [96,288,24,66,129,1] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,129,1] 13 (by decide) (choices 1) [2,4,128] r29682 c29682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11488
  · exact u11489
  · exact u11490

def b29683 : PairBound 9 := { available := 133, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 28 74 145 34 197 133 389), lower := (rows 97 290 28 74 145 34 64 128 256), losses := [] }

theorem u29683 : Upper (D 7) (R 7) [96,288,24,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29684 : Route 9 := (fun mask => (mask,id))

def c29684 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29684 : Upper (D 7) (R 7) [96,288,24,66,129,4] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,129,4] 13 (by decide) (choices 1) [1,2,128] r29684 c29684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11491
  · exact u11492
  · exact u11493

def r29685 : Route 9 := (fun mask => (mask,id))

def c29685 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29685 : Upper (D 7) (R 7) [96,288,24,66,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,129,128] 13 (by decide) (choices 1) [1,2,4] r29685 c29685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11494
  · exact u11495
  · exact u11496

def r29686 : Route 9 := (fun mask => (mask,id))

def c29686 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29686 : Upper (D 7) (R 7) [96,288,24,66,130,1] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,130,1] 13 (by decide) (choices 1) [1,4,128] r29686 c29686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11497
  · exact u11498
  · exact u11499

def b29687 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 97 290 28 74 146 36 193 129 385), lower := (rows 97 290 28 74 146 36 64 128 256), losses := [] }

theorem u29687 : Upper (D 7) (R 7) [96,288,24,66,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29687 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29688 : Route 9 := (fun mask => (mask,id))

def c29688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29688 : Upper (D 7) (R 7) [96,288,24,66,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,130,128] 13 (by decide) (choices 1) [1,4] r29688 c29688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11500
  · exact u11501

def r29689 : Route 9 := (fun mask => (mask,id))

def c29689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29689 : Upper (D 7) (R 7) [96,288,24,66,132,1] 13 := by
  apply FastRouting.sound _ _ [96,288,24,66,132,1] 13 (by decide) (choices 1) [1,2,128] r29689 c29689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11502
  · exact u11503
  · exact u11504

def b29690 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(1,7)], upper := (rows 97 290 28 74 148 34 193 129 385), lower := (rows 97 290 28 74 148 34 64 128 256), losses := [] }

theorem u29690 : Upper (D 7) (R 7) [96,288,24,66,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29691 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 331, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 97 290 28 74 148 160 67 131 259), lower := (rows 97 290 28 74 148 160 64 128 256), losses := [] }

theorem u29691 : Upper (D 7) (R 7) [96,288,24,66,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29692 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 97 290 28 76 145 33 194 130 386), lower := (rows 97 290 28 76 145 33 64 128 256), losses := [] }

theorem u29692 : Upper (D 7) (R 7) [96,288,24,68,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29693 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 97 290 28 76 145 34 195 131 387), lower := (rows 97 290 28 76 145 34 64 128 256), losses := [] }

theorem u29693 : Upper (D 7) (R 7) [96,288,24,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29694 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,6),(1,7),(4,6)], upper := (rows 97 290 28 76 145 160 67 131 259), lower := (rows 97 290 28 76 145 160 64 128 256), losses := [] }

theorem u29694 : Upper (D 7) (R 7) [96,288,24,68,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29695 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 97 290 28 76 146 33 195 131 387), lower := (rows 97 290 28 76 146 33 64 128 256), losses := [] }

theorem u29695 : Upper (D 7) (R 7) [96,288,24,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29696 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 97 290 28 76 146 34 193 129 385), lower := (rows 97 290 28 76 146 34 64 128 256), losses := [] }

theorem u29696 : Upper (D 7) (R 7) [96,288,24,68,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29697 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,6),(1,7),(4,6)], upper := (rows 97 290 28 76 146 160 67 131 259), lower := (rows 97 290 28 76 146 160 64 128 256), losses := [] }

theorem u29697 : Upper (D 7) (R 7) [96,288,24,68,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29698 : Route 9 := (fun mask => (mask,id))

def c29698 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29698 : Upper (D 7) (R 7) [96,288,24,129,130,1] 13 := by
  apply FastRouting.sound _ _ [96,288,24,129,130,1] 13 (by decide) (choices 1) [2,4] r29698 c29698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11505
  · exact u11506

def b29699 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 28 137 146 34 69 197 325), lower := (rows 97 290 28 137 146 34 64 128 256), losses := [] }

theorem u29699 : Upper (D 7) (R 7) [96,288,24,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29699
end Delivery.IrregularNine14.P07
