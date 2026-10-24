import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0161

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r26760 : Route 9 := (fun mask => (mask,id))

def c26760 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26760 : Upper (D 7) (R 7) [36,288,9,18,65,128] 13 := by
  apply FastRouting.sound _ _ [36,288,9,18,65,128] 13 (by decide) (choices 1) [2,128] r26760 c26760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9667
  · exact u9668

def b26761 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 290 13 26 208 33 194 194 450), lower := (rows 37 290 13 26 208 33 64 128 256), losses := [] }

theorem u26761 : Upper (D 7) (R 7) [36,288,9,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26762 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 13 26 208 34 193 193 449), lower := (rows 37 290 13 26 208 34 64 128 256), losses := [] }

theorem u26762 : Upper (D 7) (R 7) [36,288,9,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26763 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 37 290 13 26 208 96 195 131 387), lower := (rows 37 290 13 26 208 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 112 64 128 256), good := (rows 37 288 13 61 240 96 96 128 256) },{ target := 7, region := (rows 9 2 12 8 16 112 64 0 256), good := (rows 37 290 13 63 112 96 96 0 256) }] }

theorem u26763 : Upper (D 7) (R 7) [36,288,9,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26764 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 290 13 74 81 34 208 144 400), lower := (rows 37 290 13 74 81 34 64 128 256), losses := [] }

theorem u26764 : Upper (D 7) (R 7) [36,288,9,66,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26765 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 13 74 81 48 194 130 386), lower := (rows 37 290 13 74 81 48 64 128 256), losses := [] }

theorem u26765 : Upper (D 7) (R 7) [36,288,9,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26765 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26766 : Route 9 := (fun mask => (mask,id))

def c26766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26766 : Upper (D 7) (R 7) [36,288,9,66,65,128] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,65,128] 13 (by decide) (choices 1) [2,16,128] r26766 c26766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9669
  · exact u9670
  · exact u9671

def b26767 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 13 74 145 34 208 208 464), lower := (rows 37 290 13 74 145 34 64 128 256), losses := [] }

theorem u26767 : Upper (D 7) (R 7) [36,288,9,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26768 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 1, region := 200, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 290 13 74 145 48 194 194 450), lower := (rows 37 290 13 74 145 48 64 128 256), losses := [] }

theorem u26768 : Upper (D 7) (R 7) [36,288,9,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26768 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26769 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 13 74 145 96 210 146 402), lower := (rows 37 290 13 74 145 96 64 128 256), losses := [] }

theorem u26769 : Upper (D 7) (R 7) [36,288,9,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26770 : Route 9 := (fun mask => (mask,id))

def c26770 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26770 : Upper (D 7) (R 7) [36,288,9,66,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,129,128] 13 (by decide) (choices 1) [2,16] r26770 c26770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9672
  · exact u9673

def b26771 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 290 13 74 146 33 208 208 464), lower := (rows 37 290 13 74 146 33 64 128 256), losses := [] }

theorem u26771 : Upper (D 7) (R 7) [36,288,9,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26772 : Route 9 := (fun mask => (mask,id))

def c26772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26772 : Upper (D 7) (R 7) [36,288,9,66,130,16] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,130,16] 13 (by decide) (choices 1) [1,128] r26772 c26772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9674
  · exact u9675

def b26773 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 13 74 146 96 209 145 401), lower := (rows 37 290 13 74 146 96 64 128 256), losses := [] }

theorem u26773 : Upper (D 7) (R 7) [36,288,9,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26774 : Route 9 := (fun mask => (mask,id))

def c26774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26774 : Upper (D 7) (R 7) [36,288,9,66,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,130,128] 13 (by decide) (choices 1) [1,16] r26774 c26774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9676
  · exact u9677

def b26775 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 290 13 74 208 33 210 146 402), lower := (rows 37 290 13 74 208 33 64 128 256), losses := [] }

theorem u26775 : Upper (D 7) (R 7) [36,288,9,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26776 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 13 74 208 34 209 145 401), lower := (rows 37 290 13 74 208 34 64 128 256), losses := [] }

theorem u26776 : Upper (D 7) (R 7) [36,288,9,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26777 : Route 9 := (fun mask => (mask,id))

def c26777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26777 : Upper (D 7) (R 7) [36,288,9,66,192,16] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,192,16] 13 (by decide) (choices 1) [1,2,128] r26777 c26777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9678
  · exact u9679
  · exact u9680

def r26778 : Route 9 := (fun mask => (mask,id))

def c26778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26778 : Upper (D 7) (R 7) [36,288,9,66,192,128] 13 := by
  apply FastRouting.sound _ _ [36,288,9,66,192,128] 13 (by decide) (choices 1) [1,2,16] r26778 c26778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9681
  · exact u9682
  · exact u9683

def b26779 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 290 13 88 145 34 194 194 450), lower := (rows 37 290 13 88 145 34 64 128 256), losses := [] }

theorem u26779 : Upper (D 7) (R 7) [36,288,9,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26780 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 13 88 145 96 194 130 386), lower := (rows 37 290 13 88 145 96 64 128 256), losses := [] }

theorem u26780 : Upper (D 7) (R 7) [36,288,9,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26781 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 290 13 88 145 160 66 194 322), lower := (rows 37 290 13 88 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 288 13 125 177 160 64 160 256) }] }

theorem u26781 : Upper (D 7) (R 7) [36,288,9,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26782 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 290 13 88 146 33 194 194 450), lower := (rows 37 290 13 88 146 33 64 128 256), losses := [] }

theorem u26782 : Upper (D 7) (R 7) [36,288,9,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26783 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 37 290 13 88 146 34 193 193 449), lower := (rows 37 290 13 88 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 258 12 8 16 306 0 128 256), good := (rows 37 290 13 61 178 34 0 128 290) }] }

theorem u26783 : Upper (D 7) (R 7) [36,288,9,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26784 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 13 88 146 96 195 131 387), lower := (rows 37 290 13 88 146 96 64 128 256), losses := [] }

theorem u26784 : Upper (D 7) (R 7) [36,288,9,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26785 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(2,1)], upper := (rows 37 290 13 88 146 160 67 195 323), lower := (rows 37 290 13 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 288 13 125 176 160 64 160 256) },{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 37 290 13 61 178 160 0 160 256) }] }

theorem u26785 : Upper (D 7) (R 7) [36,288,9,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26786 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 290 13 200 81 34 210 146 402), lower := (rows 37 290 13 200 81 34 64 128 256), losses := [] }

theorem u26786 : Upper (D 7) (R 7) [36,288,9,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26787 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 13 200 81 48 194 130 386), lower := (rows 37 290 13 200 81 48 64 128 256), losses := [] }

theorem u26787 : Upper (D 7) (R 7) [36,288,9,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26787 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26788 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(4,1)], upper := (rows 37 290 13 200 81 160 82 146 274), lower := (rows 37 290 13 200 81 160 64 128 256), losses := [] }

theorem u26788 : Upper (D 7) (R 7) [36,288,9,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26789 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 290 13 200 82 33 210 146 402), lower := (rows 37 290 13 200 82 33 64 128 256), losses := [] }

theorem u26789 : Upper (D 7) (R 7) [36,288,9,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26790 : Route 9 := (fun mask => (mask,id))

def c26790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26790 : Upper (D 7) (R 7) [36,288,9,192,66,2] 13 := by
  apply FastRouting.sound _ _ [36,288,9,192,66,2] 13 (by decide) (choices 1) [1,16,128] r26790 c26790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9684
  · exact u9685
  · exact u9686

def r26791 : Route 9 := (fun mask => (mask,id))

def c26791 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26791 : Upper (D 7) (R 7) [36,288,9,192,66,16] 13 := by
  apply FastRouting.sound _ _ [36,288,9,192,66,16] 13 (by decide) (choices 1) [1,2,128] r26791 c26791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9687
  · exact u9688
  · exact u9689

def b26792 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 290 13 200 82 160 83 147 275), lower := (rows 37 290 13 200 82 160 64 128 256), losses := [] }

theorem u26792 : Upper (D 7) (R 7) [36,288,9,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26793 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 14 25 82 33 192 192 448), lower := (rows 37 290 14 25 82 33 64 128 256), losses := [] }

theorem u26793 : Upper (D 7) (R 7) [36,288,10,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26794 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 37 290 14 25 82 96 193 129 385), lower := (rows 37 290 14 25 82 96 64 128 256), losses := [] }

theorem u26794 : Upper (D 7) (R 7) [36,288,10,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26795 : Route 9 := (fun mask => (mask,id))

def c26795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26795 : Upper (D 7) (R 7) [36,288,10,17,66,128] 13 := by
  apply FastRouting.sound _ _ [36,288,10,17,66,128] 13 (by decide) (choices 1) [1,128] r26795 c26795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9690
  · exact u9691

def b26796 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 14 25 208 33 194 194 450), lower := (rows 37 290 14 25 208 33 64 128 256), losses := [] }

theorem u26796 : Upper (D 7) (R 7) [36,288,10,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26797 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 14 25 208 34 193 193 449), lower := (rows 37 290 14 25 208 34 64 128 256), losses := [] }

theorem u26797 : Upper (D 7) (R 7) [36,288,10,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26798 : Route 9 := (fun mask => (mask,id))

def c26798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26798 : Upper (D 7) (R 7) [36,288,10,17,192,64] 13 := by
  apply FastRouting.sound _ _ [36,288,10,17,192,64] 13 (by decide) (choices 1) [1,2,128] r26798 c26798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9692
  · exact u9693
  · exact u9694

def b26799 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 14 73 82 33 208 144 400), lower := (rows 37 290 14 73 82 33 64 128 256), losses := [] }

theorem u26799 : Upper (D 7) (R 7) [36,288,10,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26800 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 14 73 82 48 193 129 385), lower := (rows 37 290 14 73 82 48 64 128 256), losses := [] }

theorem u26800 : Upper (D 7) (R 7) [36,288,10,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26800 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26801 : Route 9 := (fun mask => (mask,id))

def c26801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26801 : Upper (D 7) (R 7) [36,288,10,65,66,128] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,66,128] 13 (by decide) (choices 1) [1,16,128] r26801 c26801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9695
  · exact u9696
  · exact u9697

def b26802 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 14 73 145 34 208 208 464), lower := (rows 37 290 14 73 145 34 64 128 256), losses := [] }

theorem u26802 : Upper (D 7) (R 7) [36,288,10,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26803 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(2,0),(3,5)], upper := (rows 37 290 14 73 145 48 194 194 450), lower := (rows 37 290 14 73 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 51 12 8 16 48 127 191 319), good := (rows 486 482 462 462 498 498 64 128 256) },{ target := 5, region := (rows 1 2 4 9 17 0 70 134 262), good := (rows 477 450 462 89 153 16 64 128 256) }] }

theorem u26803 : Upper (D 7) (R 7) [36,288,10,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26803 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26804 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(4,6)], upper := (rows 37 290 14 73 145 96 210 146 402), lower := (rows 37 290 14 73 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 288 45 105 145 96 96 128 256) }] }

theorem u26804 : Upper (D 7) (R 7) [36,288,10,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26805 : Route 9 := (fun mask => (mask,id))

def c26805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26805 : Upper (D 7) (R 7) [36,288,10,65,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,129,128] 13 (by decide) (choices 1) [2,16] r26805 c26805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9698
  · exact u9699

def b26806 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 14 73 146 33 208 208 464), lower := (rows 37 290 14 73 146 33 64 128 256), losses := [] }

theorem u26806 : Upper (D 7) (R 7) [36,288,10,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26807 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 37 290 14 73 146 48 193 193 449), lower := (rows 37 290 14 73 146 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 20 0 73 137 265), good := (rows 477 258 478 457 146 16 64 128 256) }] }

theorem u26807 : Upper (D 7) (R 7) [36,288,10,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26807 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26808 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 402, targets := 64 }], pairs := [(0,1),(1,6),(2,6),(4,6)], upper := (rows 37 290 14 73 146 96 209 145 401), lower := (rows 37 290 14 73 146 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 288 45 105 144 96 96 128 256) },{ target := 6, region := (rows 1 3 12 8 29 32 0 137 265), good := (rows 439 290 414 415 146 32 0 128 256) }] }

theorem u26808 : Upper (D 7) (R 7) [36,288,10,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26809 : Route 9 := (fun mask => (mask,id))

def c26809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26809 : Upper (D 7) (R 7) [36,288,10,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,130,128] 13 (by decide) (choices 1) [1,16] r26809 c26809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9700
  · exact u9701

def b26810 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 14 73 208 33 210 146 402), lower := (rows 37 290 14 73 208 33 64 128 256), losses := [] }

theorem u26810 : Upper (D 7) (R 7) [36,288,10,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26811 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 14 73 208 34 209 145 401), lower := (rows 37 290 14 73 208 34 64 128 256), losses := [] }

theorem u26811 : Upper (D 7) (R 7) [36,288,10,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26812 : Route 9 := (fun mask => (mask,id))

def c26812 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26812 : Upper (D 7) (R 7) [36,288,10,65,192,16] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,192,16] 13 (by decide) (choices 1) [1,2,128] r26812 c26812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9702
  · exact u9703
  · exact u9704

def r26813 : Route 9 := (fun mask => (mask,id))

def c26813 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26813 : Upper (D 7) (R 7) [36,288,10,65,192,128] 13 := by
  apply FastRouting.sound _ _ [36,288,10,65,192,128] 13 (by decide) (choices 1) [1,2,16] r26813 c26813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9705
  · exact u9706
  · exact u9707

def b26814 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 14 88 145 33 194 194 450), lower := (rows 37 290 14 88 145 33 64 128 256), losses := [] }

theorem u26814 : Upper (D 7) (R 7) [36,288,10,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26815 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 14 88 145 34 193 193 449), lower := (rows 37 290 14 88 145 34 64 128 256), losses := [] }

theorem u26815 : Upper (D 7) (R 7) [36,288,10,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26816 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 37 290 14 88 145 96 195 131 387), lower := (rows 37 290 14 88 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 288 45 120 145 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 16 104 64 0 256), good := (rows 37 290 47 120 17 96 96 0 256) }] }

theorem u26816 : Upper (D 7) (R 7) [36,288,10,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26817 : Route 9 := (fun mask => (mask,id))

def c26817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26817 : Upper (D 7) (R 7) [36,288,10,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,10,80,129,128] 13 (by decide) (choices 1) [1,2] r26817 c26817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9708
  · exact u9709

def b26818 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 290 14 88 146 33 193 193 449), lower := (rows 37 290 14 88 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 22 10 18 0 97 161 289), good := (rows 453 478 30 92 158 449 64 128 256) }] }

theorem u26818 : Upper (D 7) (R 7) [36,288,10,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26819 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 37 290 14 88 146 96 193 129 385), lower := (rows 37 290 14 88 146 96 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 104 64 0 256), good := (rows 37 290 47 120 18 96 96 0 256) }] }

theorem u26819 : Upper (D 7) (R 7) [36,288,10,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26819
end Delivery.IrregularNine14.P07
