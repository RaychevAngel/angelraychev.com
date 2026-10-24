import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0098

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r20760 : Route 9 := (fun mask => (mask,id))

def c20760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20760 : Upper (D 7) (R 7) [34,257,10,20,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,20,96,128] 13 (by decide) (choices 1) [1,128] r20760 c20760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5880
  · exact u5881

def b20761 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 28 208 33 224 224 480), lower := (rows 35 259 14 28 208 33 64 128 256), losses := [] }

theorem u20761 : Upper (D 7) (R 7) [34,257,10,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20762 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 35 259 14 28 208 96 225 161 417), lower := (rows 35 259 14 28 208 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 23 119 67 131 259), good := (rows 497 497 508 60 240 96 96 128 256) }] }

theorem u20762 : Upper (D 7) (R 7) [34,257,10,20,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20763 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 259 14 56 81 36 192 192 448), lower := (rows 35 259 14 56 81 36 64 128 256), losses := [] }

theorem u20763 : Upper (D 7) (R 7) [34,257,10,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20763 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20764 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 35 259 14 56 81 96 196 132 388), lower := (rows 35 259 14 56 81 96 64 128 256), losses := [] }

theorem u20764 : Upper (D 7) (R 7) [34,257,10,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20765 : Route 9 := (fun mask => (mask,id))

def c20765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20765 : Upper (D 7) (R 7) [34,257,10,48,65,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,48,65,128] 13 (by decide) (choices 1) [4,128] r20765 c20765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5882
  · exact u5883

def b20766 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 56 208 33 196 196 452), lower := (rows 35 259 14 56 208 33 64 128 256), losses := [] }

theorem u20766 : Upper (D 7) (R 7) [34,257,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20767 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 259 14 56 208 36 193 193 449), lower := (rows 35 259 14 56 208 36 64 128 256), losses := [] }

theorem u20767 : Upper (D 7) (R 7) [34,257,10,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20767 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20768 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 35 259 14 56 208 96 197 133 389), lower := (rows 35 259 14 56 208 96 64 128 256), losses := [] }

theorem u20768 : Upper (D 7) (R 7) [34,257,10,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20769 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 259 14 73 52 48 192 192 448), lower := (rows 35 259 14 73 52 48 64 128 256), losses := [] }

theorem u20769 : Upper (D 7) (R 7) [34,257,10,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20769 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20770 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 259 14 73 52 96 208 144 400), lower := (rows 35 259 14 73 52 96 64 128 256), losses := [] }

theorem u20770 : Upper (D 7) (R 7) [34,257,10,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20771 : Route 9 := (fun mask => (mask,id))

def c20771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20771 : Upper (D 7) (R 7) [34,257,10,65,36,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,36,128] 13 (by decide) (choices 1) [16,128] r20771 c20771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5884
  · exact u5885

def b20772 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 14 73 112 36 208 144 400), lower := (rows 35 259 14 73 112 36 64 128 256), losses := [] }

theorem u20772 : Upper (D 7) (R 7) [34,257,10,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20772 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20773 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 14 73 112 48 196 132 388), lower := (rows 35 259 14 73 112 48 64 128 256), losses := [] }

theorem u20773 : Upper (D 7) (R 7) [34,257,10,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20773 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20774 : Route 9 := (fun mask => (mask,id))

def c20774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20774 : Upper (D 7) (R 7) [34,257,10,65,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,96,128] 13 (by decide) (choices 1) [4,16,128] r20774 c20774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5886
  · exact u5887
  · exact u5888

def b20775 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 35 259 14 73 148 48 224 224 480), lower := (rows 35 259 14 73 148 48 64 128 256), losses := [] }

theorem u20775 : Upper (D 7) (R 7) [34,257,10,65,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20775 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20776 : Route 9 := (fun mask => (mask,id))

def c20776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u20776 : Upper (D 7) (R 7) [34,257,10,65,132,64] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,132,64] 13 (by decide) (choices 1) [16,32,128] r20776 c20776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5889
  · exact u5890
  · exact u5891

def r20777 : Route 9 := (fun mask => (mask,id))

def c20777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20777 : Upper (D 7) (R 7) [34,257,10,65,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,132,128] 13 (by decide) (choices 1) [16,32] r20777 c20777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5892
  · exact u5893

def b20778 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 14 73 176 36 208 208 464), lower := (rows 35 259 14 73 176 36 64 128 256), losses := [] }

theorem u20778 : Upper (D 7) (R 7) [34,257,10,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20778 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20779 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 14 73 176 48 196 196 452), lower := (rows 35 259 14 73 176 48 64 128 256), losses := [] }

theorem u20779 : Upper (D 7) (R 7) [34,257,10,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20779 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20780 : Route 9 := (fun mask => (mask,id))

def c20780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20780 : Upper (D 7) (R 7) [34,257,10,65,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,160,64] 13 (by decide) (choices 1) [4,16,128] r20780 c20780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5894
  · exact u5895
  · exact u5896

def b20781 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 14 73 176 160 84 212 340), lower := (rows 35 259 14 73 176 160 64 128 256), losses := [] }

theorem u20781 : Upper (D 7) (R 7) [34,257,10,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20782 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 14 73 208 36 240 176 432), lower := (rows 35 259 14 73 208 36 64 128 256), losses := [] }

theorem u20782 : Upper (D 7) (R 7) [34,257,10,65,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20782 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20783 : Route 9 := (fun mask => (mask,id))

def c20783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20783 : Upper (D 7) (R 7) [34,257,10,65,192,16] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,192,16] 13 (by decide) (choices 1) [4,32,128] r20783 c20783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5897
  · exact u5898
  · exact u5899

def r20784 : Route 9 := (fun mask => (mask,id))

def c20784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20784 : Upper (D 7) (R 7) [34,257,10,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,192,128] 13 (by decide) (choices 1) [4,16,32] r20784 c20784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5900
  · exact u5901
  · exact u5902

def b20785 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 204, targets := 1 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 35 259 14 76 145 48 224 224 480), lower := (rows 35 259 14 76 145 48 64 128 256), losses := [] }

theorem u20785 : Upper (D 7) (R 7) [34,257,10,68,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20785 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20786 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 403, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,6),(1,6),(4,1),(4,6)], upper := (rows 35 259 14 76 145 96 240 176 432), lower := (rows 35 259 14 76 145 96 64 128 256), losses := [] }

theorem u20786 : Upper (D 7) (R 7) [34,257,10,68,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20787 : Route 9 := (fun mask => (mask,id))

def c20787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20787 : Upper (D 7) (R 7) [34,257,10,68,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,68,129,128] 13 (by decide) (choices 1) [16,32] r20787 c20787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5903
  · exact u5904

def b20788 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 76 176 33 208 208 464), lower := (rows 35 259 14 76 176 33 64 128 256), losses := [] }

theorem u20788 : Upper (D 7) (R 7) [34,257,10,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20789 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 14 76 176 48 193 193 449), lower := (rows 35 259 14 76 176 48 64 128 256), losses := [] }

theorem u20789 : Upper (D 7) (R 7) [34,257,10,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20789 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20790 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 403, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,6),(1,6),(4,1),(4,6)], upper := (rows 35 259 14 76 176 96 209 145 401), lower := (rows 35 259 14 76 176 96 64 128 256), losses := [] }

theorem u20790 : Upper (D 7) (R 7) [34,257,10,68,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20791 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 14 76 176 160 81 209 337), lower := (rows 35 259 14 76 176 160 64 128 256), losses := [] }

theorem u20791 : Upper (D 7) (R 7) [34,257,10,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20792 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 259 14 88 52 33 192 192 448), lower := (rows 35 259 14 88 52 33 64 128 256), losses := [] }

theorem u20792 : Upper (D 7) (R 7) [34,257,10,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20793 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 387, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,6),(1,5),(1,6),(4,0)], upper := (rows 35 259 14 88 52 96 193 129 385), lower := (rows 35 259 14 88 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 104 64 128 256), good := (rows 34 258 62 120 52 96 96 128 256) }] }

theorem u20793 : Upper (D 7) (R 7) [34,257,10,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20794 : Route 9 := (fun mask => (mask,id))

def c20794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20794 : Upper (D 7) (R 7) [34,257,10,80,36,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,36,128] 13 (by decide) (choices 1) [1,128] r20794 c20794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5905
  · exact u5906

def b20795 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 14 88 145 36 224 224 480), lower := (rows 35 259 14 88 145 36 64 128 256), losses := [] }

theorem u20795 : Upper (D 7) (R 7) [34,257,10,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20795 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20796 : Route 9 := (fun mask => (mask,id))

def c20796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20796 : Upper (D 7) (R 7) [34,257,10,80,129,64] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,129,64] 13 (by decide) (choices 1) [4,32,128] r20796 c20796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5907
  · exact u5908
  · exact u5909

def r20797 : Route 9 := (fun mask => (mask,id))

def c20797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20797 : Upper (D 7) (R 7) [34,257,10,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,129,128] 13 (by decide) (choices 1) [4,32] r20797 c20797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5910
  · exact u5911

def b20798 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 88 148 33 224 224 480), lower := (rows 35 259 14 88 148 33 64 128 256), losses := [] }

theorem u20798 : Upper (D 7) (R 7) [34,257,10,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20799 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 35 259 14 88 148 96 225 161 417), lower := (rows 35 259 14 88 148 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 111 67 131 259), good := (rows 481 481 508 120 188 96 96 128 256) }] }

theorem u20799 : Upper (D 7) (R 7) [34,257,10,80,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20800 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,1),(4,1)], upper := (rows 35 259 14 88 148 160 97 225 353), lower := (rows 35 259 14 88 148 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 183 67 131 259), good := (rows 481 481 508 120 188 160 64 160 256) }] }

theorem u20800 : Upper (D 7) (R 7) [34,257,10,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20801 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 88 176 33 196 196 452), lower := (rows 35 259 14 88 176 33 64 128 256), losses := [] }

theorem u20801 : Upper (D 7) (R 7) [34,257,10,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20802 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 259 14 88 176 36 193 193 449), lower := (rows 35 259 14 88 176 36 64 128 256), losses := [] }

theorem u20802 : Upper (D 7) (R 7) [34,257,10,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20802 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20803 : Route 9 := (fun mask => (mask,id))

def c20803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20803 : Upper (D 7) (R 7) [34,257,10,80,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,160,64] 13 (by decide) (choices 1) [1,4,128] r20803 c20803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5912
  · exact u5913
  · exact u5914

def b20804 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 14 88 176 160 69 197 325), lower := (rows 35 259 14 88 176 160 64 128 256), losses := [] }

theorem u20804 : Upper (D 7) (R 7) [34,257,10,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20805 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 259 14 104 81 36 208 144 400), lower := (rows 35 259 14 104 81 36 64 128 256), losses := [] }

theorem u20805 : Upper (D 7) (R 7) [34,257,10,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20805 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20806 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 14 104 81 48 196 132 388), lower := (rows 35 259 14 104 81 48 64 128 256), losses := [] }

theorem u20806 : Upper (D 7) (R 7) [34,257,10,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20806 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20807 : Route 9 := (fun mask => (mask,id))

def c20807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20807 : Upper (D 7) (R 7) [34,257,10,96,65,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,65,128] 13 (by decide) (choices 1) [4,16,128] r20807 c20807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5915
  · exact u5916
  · exact u5917

def b20808 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 104 84 33 208 144 400), lower := (rows 35 259 14 104 84 33 64 128 256), losses := [] }

theorem u20808 : Upper (D 7) (R 7) [34,257,10,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20809 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 14 104 84 48 193 129 385), lower := (rows 35 259 14 104 84 48 64 128 256), losses := [] }

theorem u20809 : Upper (D 7) (R 7) [34,257,10,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20809 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20810 : Route 9 := (fun mask => (mask,id))

def c20810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20810 : Upper (D 7) (R 7) [34,257,10,96,68,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,68,128] 13 (by decide) (choices 1) [1,16,128] r20810 c20810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5918
  · exact u5919
  · exact u5920

def b20811 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 259 14 104 145 36 208 208 464), lower := (rows 35 259 14 104 145 36 64 128 256), losses := [] }

theorem u20811 : Upper (D 7) (R 7) [34,257,10,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20811 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20812 : Route 9 := (fun mask => (mask,id))

def c20812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20812 : Upper (D 7) (R 7) [34,257,10,96,129,16] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,129,16] 13 (by decide) (choices 1) [4,128] r20812 c20812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5921
  · exact u5922

def b20813 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 35 259 14 104 145 96 212 148 404), lower := (rows 35 259 14 104 145 96 64 128 256), losses := [] }

theorem u20813 : Upper (D 7) (R 7) [34,257,10,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20814 : Route 9 := (fun mask => (mask,id))

def c20814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20814 : Upper (D 7) (R 7) [34,257,10,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,129,128] 13 (by decide) (choices 1) [4,16] r20814 c20814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5923
  · exact u5924

def b20815 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 104 148 33 208 208 464), lower := (rows 35 259 14 104 148 33 64 128 256), losses := [] }

theorem u20815 : Upper (D 7) (R 7) [34,257,10,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20816 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 259 14 104 148 48 193 193 449), lower := (rows 35 259 14 104 148 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 13 20 52 67 131 259), good := (rows 489 457 508 104 188 48 64 128 256) }] }

theorem u20816 : Upper (D 7) (R 7) [34,257,10,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20816 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20817 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 35 259 14 104 148 96 209 145 401), lower := (rows 35 259 14 104 148 96 64 128 256), losses := [] }

theorem u20817 : Upper (D 7) (R 7) [34,257,10,96,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20818 : Route 9 := (fun mask => (mask,id))

def c20818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20818 : Upper (D 7) (R 7) [34,257,10,96,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,96,132,128] 13 (by decide) (choices 1) [1,16] r20818 c20818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5925
  · exact u5926

def b20819 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 104 208 33 212 148 404), lower := (rows 35 259 14 104 208 33 64 128 256), losses := [] }

theorem u20819 : Upper (D 7) (R 7) [34,257,10,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20819
end Delivery.IrregularNine14.P07
