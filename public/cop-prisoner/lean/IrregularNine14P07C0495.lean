import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0191
import IrregularNine14P07C0192

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r29700 : Route 9 := (fun mask => (mask,id))

def c29700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29700 : Upper (D 7) (R 7) [96,288,24,129,130,4] 13 := by
  apply FastRouting.sound _ _ [96,288,24,129,130,4] 13 (by decide) (choices 1) [1,2] r29700 c29700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11507
  · exact u11508

def b29701 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 28 137 146 96 71 135 263), lower := (rows 97 290 28 137 146 96 64 128 256), losses := [] }

theorem u29701 : Upper (D 7) (R 7) [96,288,24,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29702 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 290 28 137 208 33 70 134 262), lower := (rows 97 290 28 137 208 33 64 128 256), losses := [] }

theorem u29702 : Upper (D 7) (R 7) [96,288,24,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29703 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 28 137 208 34 71 135 263), lower := (rows 97 290 28 137 208 34 64 128 256), losses := [] }

theorem u29703 : Upper (D 7) (R 7) [96,288,24,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29704 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 290 28 137 208 36 67 131 259), lower := (rows 97 290 28 137 208 36 64 128 256), losses := [] }

theorem u29704 : Upper (D 7) (R 7) [96,288,24,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29704 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29705 : Route 9 := (fun mask => (mask,id))

def c29705 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29705 : Upper (D 7) (R 7) [96,288,24,130,192,1] 13 := by
  apply FastRouting.sound _ _ [96,288,24,130,192,1] 13 (by decide) (choices 1) [1,2,4] r29705 c29705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11509
  · exact u11510
  · exact u11511

def b29706 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 28 138 208 34 69 133 261), lower := (rows 97 290 28 138 208 34 64 128 256), losses := [] }

theorem u29706 : Upper (D 7) (R 7) [96,288,24,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29707 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 97 290 28 138 208 36 67 131 259), lower := (rows 97 290 28 138 208 36 64 128 256), losses := [] }

theorem u29707 : Upper (D 7) (R 7) [96,288,24,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29707 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29708 : Route 9 := (fun mask => (mask,id))

def c29708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29708 : Upper (D 7) (R 7) [96,288,66,129,130,1] 13 := by
  apply FastRouting.sound _ _ [96,288,66,129,130,1] 13 (by decide) (choices 1) [4,8,16] r29708 c29708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11512
  · exact u11513
  · exact u11514

def b29709 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 290 70 137 146 36 89 153 281), lower := (rows 97 290 70 137 146 36 64 128 256), losses := [] }

theorem u29709 : Upper (D 7) (R 7) [96,288,66,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29709 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29710 : Route 9 := (fun mask => (mask,id))

def c29710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29710 : Upper (D 7) (R 7) [96,288,66,129,130,8] 13 := by
  apply FastRouting.sound _ _ [96,288,66,129,130,8] 13 (by decide) (choices 1) [1,4,16] r29710 c29710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11515
  · exact u11516
  · exact u11517

def r29711 : Route 9 := (fun mask => (mask,id))

def c29711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29711 : Upper (D 7) (R 7) [96,288,66,129,130,16] 13 := by
  apply FastRouting.sound _ _ [96,288,66,129,130,16] 13 (by decide) (choices 1) [1,4,8] r29711 c29711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11518
  · exact u11519
  · exact u11520

def r29712 : Route 9 := (fun mask => (mask,id))

def c29712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29712 : Upper (D 7) (R 7) [96,288,66,129,132,1] 13 := by
  apply FastRouting.sound _ _ [96,288,66,129,132,1] 13 (by decide) (choices 1) [2,8,16] r29712 c29712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11521
  · exact u11522
  · exact u11523

def b29713 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 70 137 148 34 89 153 281), lower := (rows 97 290 70 137 148 34 64 128 256), losses := [] }

theorem u29713 : Upper (D 7) (R 7) [96,288,66,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29714 : Route 9 := (fun mask => (mask,id))

def c29714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29714 : Upper (D 7) (R 7) [96,288,66,129,132,8] 13 := by
  apply FastRouting.sound _ _ [96,288,66,129,132,8] 13 (by decide) (choices 1) [1,2,16] r29714 c29714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11524
  · exact u11525
  · exact u11526

def r29715 : Route 9 := (fun mask => (mask,id))

def c29715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29715 : Upper (D 7) (R 7) [96,288,66,129,132,16] 13 := by
  apply FastRouting.sound _ _ [96,288,66,129,132,16] 13 (by decide) (choices 1) [1,2,8] r29715 c29715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11527
  · exact u11528
  · exact u11529

def r29716 : Route 9 := (fun mask => (mask,id))

def c29716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29716 : Upper (D 7) (R 7) [96,288,66,130,132,1] 13 := by
  apply FastRouting.sound _ _ [96,288,66,130,132,1] 13 (by decide) (choices 1) [1,8,16] r29716 c29716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11530
  · exact u11531
  · exact u11532

def r29717 : Route 9 := (fun mask => (mask,id))

def c29717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29717 : Upper (D 7) (R 7) [96,288,66,130,132,8] 13 := by
  apply FastRouting.sound _ _ [96,288,66,130,132,8] 13 (by decide) (choices 1) [1,16] r29717 c29717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11533
  · exact u11534

def r29718 : Route 9 := (fun mask => (mask,id))

def c29718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29718 : Upper (D 7) (R 7) [96,288,66,130,132,16] 13 := by
  apply FastRouting.sound _ _ [96,288,66,130,132,16] 13 (by decide) (choices 1) [1,8] r29718 c29718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11535
  · exact u11536

def b29719 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 97 290 76 137 146 33 86 150 278), lower := (rows 97 290 76 137 146 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 20 41 0 132 260), good := (rows 33 290 446 169 146 33 0 128 256) }] }

theorem u29719 : Upper (D 7) (R 7) [96,288,72,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29720 : Route 9 := (fun mask => (mask,id))

def c29720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29720 : Upper (D 7) (R 7) [96,288,72,129,130,2] 13 := by
  apply FastRouting.sound _ _ [96,288,72,129,130,2] 13 (by decide) (choices 1) [1,4,16] r29720 c29720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11537
  · exact u11538
  · exact u11539

def b29721 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 290 76 137 146 36 83 147 275), lower := (rows 97 290 76 137 146 36 64 128 256), losses := [] }

theorem u29721 : Upper (D 7) (R 7) [96,288,72,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29721 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29722 : Route 9 := (fun mask => (mask,id))

def c29722 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29722 : Upper (D 7) (R 7) [96,288,72,129,130,16] 13 := by
  apply FastRouting.sound _ _ [96,288,72,129,130,16] 13 (by decide) (choices 1) [1,2,4] r29722 c29722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11540
  · exact u11541
  · exact u11542

def b29723 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(3,1)], upper := (rows 97 290 76 137 148 33 82 146 274), lower := (rows 97 290 76 137 148 33 64 128 256), losses := [{ target := 1, region := (rows 69 0 4 24 16 125 64 128 256), good := (rows 97 288 109 169 189 33 97 128 256) }] }

theorem u29723 : Upper (D 7) (R 7) [96,288,72,129,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29724 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 76 137 148 34 83 147 275), lower := (rows 97 290 76 137 148 34 64 128 256), losses := [] }

theorem u29724 : Upper (D 7) (R 7) [96,288,72,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29725 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 97 290 76 137 148 48 67 131 259), lower := (rows 97 290 76 137 148 48 64 128 256), losses := [] }

theorem u29725 : Upper (D 7) (R 7) [96,288,72,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29725 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29726 : Route 9 := (fun mask => (mask,id))

def c29726 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29726 : Upper (D 7) (R 7) [96,288,72,130,129,1] 13 := by
  apply FastRouting.sound _ _ [96,288,72,130,129,1] 13 (by decide) (choices 1) [2,4,16] r29726 c29726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11543
  · exact u11544
  · exact u11545

def b29727 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 76 138 145 34 85 149 277), lower := (rows 97 290 76 138 145 34 64 128 256), losses := [{ target := 7, region := (rows 5 258 4 8 16 298 64 0 256), good := (rows 97 290 109 42 17 34 64 0 290) }] }

theorem u29727 : Upper (D 7) (R 7) [96,288,72,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29728 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 290 76 138 145 36 83 147 275), lower := (rows 97 290 76 138 145 36 64 128 256), losses := [] }

theorem u29728 : Upper (D 7) (R 7) [96,288,72,130,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29728 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29729 : Route 9 := (fun mask => (mask,id))

def c29729 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29729 : Upper (D 7) (R 7) [96,288,72,130,129,16] 13 := by
  apply FastRouting.sound _ _ [96,288,72,130,129,16] 13 (by decide) (choices 1) [1,2,4] r29729 c29729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11546
  · exact u11547
  · exact u11548

def r29730 : Route 9 := (fun mask => (mask,id))

def c29730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29730 : Upper (D 7) (R 7) [96,288,72,130,132,1] 13 := by
  apply FastRouting.sound _ _ [96,288,72,130,132,1] 13 (by decide) (choices 1) [1,2,16] r29730 c29730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11549
  · exact u11550
  · exact u11551

def b29731 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 76 138 148 34 81 145 273), lower := (rows 97 290 76 138 148 34 64 128 256), losses := [] }

theorem u29731 : Upper (D 7) (R 7) [96,288,72,130,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29732 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 97 290 76 138 148 48 67 131 259), lower := (rows 97 290 76 138 148 48 64 128 256), losses := [] }

theorem u29732 : Upper (D 7) (R 7) [96,288,72,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29732 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29733 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6)], upper := (rows 97 386 7 25 50 36 200 200 456), lower := (rows 97 386 7 25 50 36 64 128 256), losses := [] }

theorem u29733 : Upper (D 7) (R 7) [96,384,3,17,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29733 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29734 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6)], upper := (rows 97 386 7 25 50 40 196 196 452), lower := (rows 97 386 7 25 50 40 64 128 256), losses := [] }

theorem u29734 : Upper (D 7) (R 7) [96,384,3,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29734 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29735 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 25 50 96 204 140 396), lower := (rows 97 386 7 25 50 96 64 128 256), losses := [] }

theorem u29735 : Upper (D 7) (R 7) [96,384,3,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29736 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 97 386 7 25 50 160 76 204 332), lower := (rows 97 386 7 25 50 160 64 128 256), losses := [] }

theorem u29736 : Upper (D 7) (R 7) [96,384,3,17,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29737 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 386 7 25 52 34 200 200 456), lower := (rows 97 386 7 25 52 34 64 128 256), losses := [] }

theorem u29737 : Upper (D 7) (R 7) [96,384,3,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29738 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 56, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 97 386 7 25 52 40 194 194 450), lower := (rows 97 386 7 25 52 40 64 128 256), losses := [] }

theorem u29738 : Upper (D 7) (R 7) [96,384,3,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29738 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29739 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 25 52 96 202 138 394), lower := (rows 97 386 7 25 52 96 64 128 256), losses := [] }

theorem u29739 : Upper (D 7) (R 7) [96,384,3,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29740 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 97 386 7 25 52 160 74 202 330), lower := (rows 97 386 7 25 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 20 170 72 136 264), good := (rows 96 418 54 506 52 160 64 160 256) }] }

theorem u29740 : Upper (D 7) (R 7) [96,384,3,17,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29741 : Route 9 := (fun mask => (mask,id))

def c29741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29741 : Upper (D 7) (R 7) [96,384,3,17,132,2] 13 := by
  apply FastRouting.sound _ _ [96,384,3,17,132,2] 13 (by decide) (choices 1) [8,32] r29741 c29741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11552
  · exact u11553

theorem m29742_2 : Upper (D 7) (R 7) [96,384,3,17,132,8,2] 13 :=
  permutation_upper _ _ _ [96,384,3,17,132,2,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11552

def r29742 : Route 9 := (fun mask => (mask,id))

def c29742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29742 : Upper (D 7) (R 7) [96,384,3,17,132,8] 13 := by
  apply FastRouting.sound _ _ [96,384,3,17,132,8] 13 (by decide) (choices 1) [2,32] r29742 c29742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29742_2
  · exact u11554

def b29743 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 25 148 96 106 170 298), lower := (rows 97 386 7 25 148 96 64 128 256), losses := [] }

theorem u29743 : Upper (D 7) (R 7) [96,384,3,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29744 : Route 9 := (fun mask => (mask,id))

def c29744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29744 : Upper (D 7) (R 7) [96,384,3,17,136,2] 13 := by
  apply FastRouting.sound _ _ [96,384,3,17,136,2] 13 (by decide) (choices 1) [4,32] r29744 c29744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11555
  · exact u11556

def b29745 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 97 386 7 25 152 36 98 226 354), lower := (rows 97 386 7 25 152 36 64 128 256), losses := [] }

theorem u29745 : Upper (D 7) (R 7) [96,384,3,17,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29745 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29746 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 25 152 96 102 166 294), lower := (rows 97 386 7 25 152 96 64 128 256), losses := [] }

theorem u29746 : Upper (D 7) (R 7) [96,384,3,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29747 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,0),(4,6)], upper := (rows 97 386 7 25 176 34 76 204 332), lower := (rows 97 386 7 25 176 34 64 128 256), losses := [] }

theorem u29747 : Upper (D 7) (R 7) [96,384,3,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29748 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 97 386 7 25 176 36 74 202 330), lower := (rows 97 386 7 25 176 36 64 128 256), losses := [] }

theorem u29748 : Upper (D 7) (R 7) [96,384,3,17,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29748 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29749 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 97 386 7 25 176 40 70 198 326), lower := (rows 97 386 7 25 176 40 64 128 256), losses := [] }

theorem u29749 : Upper (D 7) (R 7) [96,384,3,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29749 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29750 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 25 176 96 78 142 270), lower := (rows 97 386 7 25 176 96 64 128 256), losses := [] }

theorem u29750 : Upper (D 7) (R 7) [96,384,3,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29751 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 386 7 26 52 33 200 200 456), lower := (rows 97 386 7 26 52 33 64 128 256), losses := [] }

theorem u29751 : Upper (D 7) (R 7) [96,384,3,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29752 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 386 7 26 52 40 193 193 449), lower := (rows 97 386 7 26 52 40 64 128 256), losses := [] }

theorem u29752 : Upper (D 7) (R 7) [96,384,3,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29752 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29753 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 26 52 96 201 137 393), lower := (rows 97 386 7 26 52 96 64 128 256), losses := [] }

theorem u29753 : Upper (D 7) (R 7) [96,384,3,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29754 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1),(3,0),(4,0),(4,1)], upper := (rows 97 386 7 26 52 160 73 201 329), lower := (rows 97 386 7 26 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 162 64 128 256), good := (rows 96 418 62 58 60 160 64 160 256) },{ target := 1, region := (rows 9 0 4 8 20 170 72 136 264), good := (rows 97 416 53 505 52 160 64 160 256) }] }

theorem u29754 : Upper (D 7) (R 7) [96,384,3,18,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29755 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 386 7 26 56 33 196 196 452), lower := (rows 97 386 7 26 56 33 64 128 256), losses := [] }

theorem u29755 : Upper (D 7) (R 7) [96,384,3,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29756 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 386 7 26 56 36 193 193 449), lower := (rows 97 386 7 26 56 36 64 128 256), losses := [] }

theorem u29756 : Upper (D 7) (R 7) [96,384,3,18,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29756 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29757 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 26 56 96 197 133 389), lower := (rows 97 386 7 26 56 96 64 128 256), losses := [] }

theorem u29757 : Upper (D 7) (R 7) [96,384,3,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29758 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 97 386 7 26 56 160 69 197 325), lower := (rows 97 386 7 26 56 160 64 128 256), losses := [] }

theorem u29758 : Upper (D 7) (R 7) [96,384,3,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29759 : Route 9 := (fun mask => (mask,id))

def c29759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29759 : Upper (D 7) (R 7) [96,384,3,18,129,4] 13 := by
  apply FastRouting.sound _ _ [96,384,3,18,129,4] 13 (by decide) (choices 1) [8,32] r29759 c29759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11557
  · exact u11558

#print axioms u29759
end Delivery.IrregularNine14.P07
