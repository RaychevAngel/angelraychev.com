import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0096
import IrregularNine14P07C0097

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20640 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(3,6),(4,6),(4,7)], upper := (rows 35 194 76 152 273 36 99 163 291), lower := (rows 35 194 76 152 273 36 64 128 256), losses := [] }

theorem u20640 : Upper (D 7) (R 7) [34,192,72,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20640 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20641 : Route 9 := (fun mask => (mask,id))

def c20641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20641 : Upper (D 7) (R 7) [34,192,72,144,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,258,1] 13 (by decide) (choices 1) [1,4,32] r20641 c20641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5781
  · exact u5782
  · exact u5783

def b20642 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(3,6),(4,6),(4,7)], upper := (rows 35 194 76 152 274 36 97 161 289), lower := (rows 35 194 76 152 274 36 64 128 256), losses := [] }

theorem u20642 : Upper (D 7) (R 7) [34,192,72,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20642 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20643 : Route 9 := (fun mask => (mask,id))

def c20643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20643 : Upper (D 7) (R 7) [34,192,72,144,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,260,1] 13 (by decide) (choices 1) [1,2,32] r20643 c20643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5784
  · exact u5785
  · exact u5786

def b20644 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 76 152 276 34 97 161 289), lower := (rows 35 194 76 152 276 34 64 128 256), losses := [] }

theorem u20644 : Upper (D 7) (R 7) [34,192,72,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20645 : Route 9 := (fun mask => (mask,id))

def c20645 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20645 : Upper (D 7) (R 7) [34,192,72,144,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,288,1] 13 (by decide) (choices 1) [1,2,4] r20645 c20645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5787
  · exact u5788
  · exact u5789

def b20646 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 76 152 304 34 69 133 261), lower := (rows 35 194 76 152 304 34 64 128 256), losses := [] }

theorem u20646 : Upper (D 7) (R 7) [34,192,72,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20647 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,6),(4,6)], upper := (rows 35 194 76 152 304 36 67 131 259), lower := (rows 35 194 76 152 304 36 64 128 256), losses := [] }

theorem u20647 : Upper (D 7) (R 7) [34,192,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20647 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20648 : Route 9 := (fun mask => (mask,id))

def c20648 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20648 : Upper (D 7) (R 7) [34,192,72,160,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257,1] 13 (by decide) (choices 1) [2,4,16] r20648 c20648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5790
  · exact u5791
  · exact u5792

def b20649 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 44, targets := 1 }], pairs := [(2,0),(2,1),(3,1),(4,1)], upper := (rows 35 194 76 168 273 34 85 149 277), lower := (rows 35 194 76 168 273 34 64 128 256), losses := [] }

theorem u20649 : Upper (D 7) (R 7) [34,192,72,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20650 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 35 194 76 168 273 36 83 147 275), lower := (rows 35 194 76 168 273 36 64 128 256), losses := [] }

theorem u20650 : Upper (D 7) (R 7) [34,192,72,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20650 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20651 : Route 9 := (fun mask => (mask,id))

def c20651 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20651 : Upper (D 7) (R 7) [34,192,72,160,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257,16] 13 (by decide) (choices 1) [1,2,4] r20651 c20651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5793
  · exact u5794
  · exact u5795

def r20652 : Route 9 := (fun mask => (mask,id))

def c20652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20652 : Upper (D 7) (R 7) [34,192,72,160,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,258,1] 13 (by decide) (choices 1) [1,4,16] r20652 c20652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5796
  · exact u5797
  · exact u5798

def b20653 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 35 194 76 168 274 36 81 145 273), lower := (rows 35 194 76 168 274 36 64 128 256), losses := [] }

theorem u20653 : Upper (D 7) (R 7) [34,192,72,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20653 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20654 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 194 76 168 274 48 69 133 261), lower := (rows 35 194 76 168 274 48 64 128 256), losses := [] }

theorem u20654 : Upper (D 7) (R 7) [34,192,72,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20654 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20655 : Route 9 := (fun mask => (mask,id))

def c20655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20655 : Upper (D 7) (R 7) [34,192,72,160,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260,1] 13 (by decide) (choices 1) [1,2,16] r20655 c20655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5799
  · exact u5800
  · exact u5801

def b20656 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 44, targets := 1 }], pairs := [(2,0),(2,1),(3,1),(4,1)], upper := (rows 35 194 76 168 276 34 81 145 273), lower := (rows 35 194 76 168 276 34 64 128 256), losses := [] }

theorem u20656 : Upper (D 7) (R 7) [34,192,72,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20657 : Route 9 := (fun mask => (mask,id))

def c20657 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20657 : Upper (D 7) (R 7) [34,192,72,160,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260,16] 13 (by decide) (choices 1) [1,2] r20657 c20657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5802
  · exact u5803

def r20658 : Route 9 := (fun mask => (mask,id))

def c20658 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20658 : Upper (D 7) (R 7) [34,192,72,257,160,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160,1] 13 (by decide) (choices 1) [2,4,16] r20658 c20658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5804
  · exact u5805
  · exact u5806

def b20659 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 76 265 176 34 85 149 277), lower := (rows 35 194 76 265 176 34 64 128 256), losses := [] }

theorem u20659 : Upper (D 7) (R 7) [34,192,72,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20660 : Route 9 := (fun mask => (mask,id))

def c20660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20660 : Upper (D 7) (R 7) [34,192,72,257,160,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160,4] 13 (by decide) (choices 1) [1,2,16] r20660 c20660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5807
  · exact u5808
  · exact u5809

def b20661 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 76 265 176 48 71 135 263), lower := (rows 35 194 76 265 176 48 64 128 256), losses := [] }

theorem u20661 : Upper (D 7) (R 7) [34,192,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20661 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20662 : Route 9 := (fun mask => (mask,id))

def c20662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20662 : Upper (D 7) (R 7) [34,192,72,258,160,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258,160,1] 13 (by decide) (choices 1) [1,4,16] r20662 c20662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5810
  · exact u5811
  · exact u5812

def b20663 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(3,6),(4,1),(4,6)], upper := (rows 35 194 76 266 176 36 81 145 273), lower := (rows 35 194 76 266 176 36 64 128 256), losses := [] }

theorem u20663 : Upper (D 7) (R 7) [34,192,72,258,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20663 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20664 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 76 266 176 48 69 133 261), lower := (rows 35 194 76 266 176 48 64 128 256), losses := [] }

theorem u20664 : Upper (D 7) (R 7) [34,192,72,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20664 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20665 : Route 9 := (fun mask => (mask,id))

def c20665 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20665 : Upper (D 7) (R 7) [34,192,72,260,160,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260,160,1] 13 (by decide) (choices 1) [1,2,16] r20665 c20665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5813
  · exact u5814
  · exact u5815

def b20666 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 76 268 176 34 81 145 273), lower := (rows 35 194 76 268 176 34 64 128 256), losses := [] }

theorem u20666 : Upper (D 7) (R 7) [34,192,72,260,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20667 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 76 268 176 48 67 131 259), lower := (rows 35 194 76 268 176 48 64 128 256), losses := [] }

theorem u20667 : Upper (D 7) (R 7) [34,192,72,260,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20667 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20668 : Route 9 := (fun mask => (mask,id))

def c20668 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20668 : Upper (D 7) (R 7) [34,192,72,272,160,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160,1] 13 (by decide) (choices 1) [1,2,4] r20668 c20668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5816
  · exact u5817
  · exact u5818

def b20669 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 76 280 176 34 69 133 261), lower := (rows 35 194 76 280 176 34 64 128 256), losses := [] }

theorem u20669 : Upper (D 7) (R 7) [34,192,72,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20670 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,6),(4,6)], upper := (rows 35 194 76 280 176 36 67 131 259), lower := (rows 35 194 76 280 176 36 64 128 256), losses := [] }

theorem u20670 : Upper (D 7) (R 7) [34,192,72,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20670 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20671 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 259 13 26 84 96 224 160 416), lower := (rows 35 259 13 26 84 96 64 128 256), losses := [] }

theorem u20671 : Upper (D 7) (R 7) [34,257,9,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20672 : Route 9 := (fun mask => (mask,id))

def c20672 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20672 : Upper (D 7) (R 7) [34,257,9,18,68,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,18,68,128] 13 (by decide) (choices 1) [32,128] r20672 c20672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5819
  · exact u5820

def b20673 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 259 13 26 112 36 192 192 448), lower := (rows 35 259 13 26 112 36 64 128 256), losses := [] }

theorem u20673 : Upper (D 7) (R 7) [34,257,9,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20673 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20674 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 35 259 13 26 112 96 196 132 388), lower := (rows 35 259 13 26 112 96 64 128 256), losses := [] }

theorem u20674 : Upper (D 7) (R 7) [34,257,9,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20675 : Route 9 := (fun mask => (mask,id))

def c20675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20675 : Upper (D 7) (R 7) [34,257,9,18,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,18,96,128] 13 (by decide) (choices 1) [4,128] r20675 c20675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5821
  · exact u5822

def b20676 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 259 13 26 208 36 224 224 480), lower := (rows 35 259 13 26 208 36 64 128 256), losses := [] }

theorem u20676 : Upper (D 7) (R 7) [34,257,9,18,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20676 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20677 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 240, targets := 3 }], pairs := [(0,7),(2,7),(4,0),(4,1)], upper := (rows 35 259 13 26 208 96 228 164 420), lower := (rows 35 259 13 26 208 96 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 16 112 64 0 256), good := (rows 35 259 13 63 112 96 96 0 256) }] }

theorem u20677 : Upper (D 7) (R 7) [34,257,9,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20678 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 259 13 28 82 96 224 160 416), lower := (rows 35 259 13 28 82 96 64 128 256), losses := [] }

theorem u20678 : Upper (D 7) (R 7) [34,257,9,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20679 : Route 9 := (fun mask => (mask,id))

def c20679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20679 : Upper (D 7) (R 7) [34,257,9,20,66,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,20,66,128] 13 (by decide) (choices 1) [32,128] r20679 c20679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5823
  · exact u5824

def b20680 : PairBound 9 := { available := 192, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 28 112 34 192 192 448), lower := (rows 35 259 13 28 112 34 64 128 256), losses := [] }

theorem u20680 : Upper (D 7) (R 7) [34,257,9,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20681 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 35 259 13 28 112 96 194 130 386), lower := (rows 35 259 13 28 112 96 64 128 256), losses := [] }

theorem u20681 : Upper (D 7) (R 7) [34,257,9,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20682 : Route 9 := (fun mask => (mask,id))

def c20682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20682 : Upper (D 7) (R 7) [34,257,9,20,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,20,96,128] 13 (by decide) (choices 1) [2,128] r20682 c20682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5825
  · exact u5826

def b20683 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 28 208 34 224 224 480), lower := (rows 35 259 13 28 208 34 64 128 256), losses := [] }

theorem u20683 : Upper (D 7) (R 7) [34,257,9,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20684 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 387, targets := 64 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 35 259 13 28 208 96 226 162 418), lower := (rows 35 259 13 28 208 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 119 67 131 259), good := (rows 498 498 508 60 240 96 96 128 256) }] }

theorem u20684 : Upper (D 7) (R 7) [34,257,9,20,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20685 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 259 13 56 82 36 192 192 448), lower := (rows 35 259 13 56 82 36 64 128 256), losses := [] }

theorem u20685 : Upper (D 7) (R 7) [34,257,9,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20685 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20686 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 35 259 13 56 82 96 196 132 388), lower := (rows 35 259 13 56 82 96 64 128 256), losses := [] }

theorem u20686 : Upper (D 7) (R 7) [34,257,9,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20687 : Route 9 := (fun mask => (mask,id))

def c20687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20687 : Upper (D 7) (R 7) [34,257,9,48,66,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,48,66,128] 13 (by decide) (choices 1) [4,128] r20687 c20687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5827
  · exact u5828

def b20688 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 56 208 34 196 196 452), lower := (rows 35 259 13 56 208 34 64 128 256), losses := [] }

theorem u20688 : Upper (D 7) (R 7) [34,257,9,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20689 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 259 13 56 208 36 194 194 450), lower := (rows 35 259 13 56 208 36 64 128 256), losses := [] }

theorem u20689 : Upper (D 7) (R 7) [34,257,9,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20689 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20690 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 35 259 13 56 208 96 198 134 390), lower := (rows 35 259 13 56 208 96 64 128 256), losses := [] }

theorem u20690 : Upper (D 7) (R 7) [34,257,9,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20691 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 259 13 74 52 48 192 192 448), lower := (rows 35 259 13 74 52 48 64 128 256), losses := [] }

theorem u20691 : Upper (D 7) (R 7) [34,257,9,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20691 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20692 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 2, region := 240, targets := 1 }], pairs := [(0,7),(2,7),(4,0),(4,7)], upper := (rows 35 259 13 74 52 96 208 144 400), lower := (rows 35 259 13 74 52 96 64 128 256), losses := [] }

theorem u20692 : Upper (D 7) (R 7) [34,257,9,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20693 : Route 9 := (fun mask => (mask,id))

def c20693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20693 : Upper (D 7) (R 7) [34,257,9,66,36,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,36,128] 13 (by decide) (choices 1) [16,128] r20693 c20693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5829
  · exact u5830

def b20694 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 259 13 74 112 36 208 144 400), lower := (rows 35 259 13 74 112 36 64 128 256), losses := [] }

theorem u20694 : Upper (D 7) (R 7) [34,257,9,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20694 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20695 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 13 74 112 48 196 132 388), lower := (rows 35 259 13 74 112 48 64 128 256), losses := [] }

theorem u20695 : Upper (D 7) (R 7) [34,257,9,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20695 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20696 : Route 9 := (fun mask => (mask,id))

def c20696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20696 : Upper (D 7) (R 7) [34,257,9,66,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,96,128] 13 (by decide) (choices 1) [4,16,128] r20696 c20696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5831
  · exact u5832
  · exact u5833

def b20697 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 35 259 13 74 148 48 224 224 480), lower := (rows 35 259 13 74 148 48 64 128 256), losses := [] }

theorem u20697 : Upper (D 7) (R 7) [34,257,9,66,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20697 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20698 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,1)], upper := (rows 35 259 13 74 148 96 240 176 432), lower := (rows 35 259 13 74 148 96 64 128 256), losses := [] }

theorem u20698 : Upper (D 7) (R 7) [34,257,9,66,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20699 : Route 9 := (fun mask => (mask,id))

def c20699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20699 : Upper (D 7) (R 7) [34,257,9,66,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,132,128] 13 (by decide) (choices 1) [16,32] r20699 c20699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5834
  · exact u5835

#print axioms u20699
end Delivery.IrregularNine14.P07
