import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0347
import IrregularNine14P07C0348
import IrregularNine14P07C0349

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35640 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 20, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 28 73 84 162 226 162 418), lower := (rows 35 259 28 73 84 32 64 128 256), losses := [] }

theorem u35640 : Upper (D 7) (R 7) [34,257,24,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35641 : Route 9 := (fun mask => (mask,id))

def c35641 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35641 : Upper (D 7) (R 7) [34,257,24,65,96] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,96] 13 (by decide) (choices 1) [2,4,128] r35641 c35641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20841
  · exact u20842
  · exact u20843

def r35642 : Route 9 := (fun mask => (mask,id))

def c35642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35642 : Upper (D 7) (R 7) [34,257,24,65,130] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,130] 13 (by decide) (choices 1) [4,64,128] r35642 c35642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20844
  · exact u20845
  · exact u20846

def r35643 : Route 9 := (fun mask => (mask,id))

def c35643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35643 : Upper (D 7) (R 7) [34,257,24,65,132] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,132] 13 (by decide) (choices 1) [2,64,128] r35643 c35643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20847
  · exact u20848
  · exact u20849

def r35644 : Route 9 := (fun mask => (mask,id))

def c35644 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35644 : Upper (D 7) (R 7) [34,257,24,65,160] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,160] 13 (by decide) (choices 1) [2,4,64,128] r35644 c35644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20850
  · exact u20851
  · exact u20852
  · exact u20853

def r35645 : Route 9 := (fun mask => (mask,id))

def c35645 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35645 : Upper (D 7) (R 7) [34,257,24,65,192] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,192] 13 (by decide) (choices 1) [2,4,128] r35645 c35645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20854
  · exact u20855
  · exact u20856

def b35646 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 20, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 28 74 84 161 225 161 417), lower := (rows 35 259 28 74 84 32 64 128 256), losses := [] }

theorem u35646 : Upper (D 7) (R 7) [34,257,24,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35647 : Route 9 := (fun mask => (mask,id))

def c35647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35647 : Upper (D 7) (R 7) [34,257,24,66,96] 13 := by
  apply FastRouting.sound _ _ [34,257,24,66,96] 13 (by decide) (choices 1) [1,4,128] r35647 c35647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20857
  · exact u20858
  · exact u20859

def r35648 : Route 9 := (fun mask => (mask,id))

def c35648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35648 : Upper (D 7) (R 7) [34,257,24,66,132] 13 := by
  apply FastRouting.sound _ _ [34,257,24,66,132] 13 (by decide) (choices 1) [1,64,128] r35648 c35648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20860
  · exact u20861
  · exact u20862

def r35649 : Route 9 := (fun mask => (mask,id))

def c35649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35649 : Upper (D 7) (R 7) [34,257,24,66,160] 13 := by
  apply FastRouting.sound _ _ [34,257,24,66,160] 13 (by decide) (choices 1) [1,4,64,128] r35649 c35649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20863
  · exact u20864
  · exact u20865
  · exact u20866

def r35650 : Route 9 := (fun mask => (mask,id))

def c35650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35650 : Upper (D 7) (R 7) [34,257,24,66,192] 13 := by
  apply FastRouting.sound _ _ [34,257,24,66,192] 13 (by decide) (choices 1) [1,4,128] r35650 c35650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20867
  · exact u20868
  · exact u20869

def b35651 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 12, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 28 76 112 163 195 131 387), lower := (rows 35 259 28 76 112 32 64 128 256), losses := [] }

theorem u35651 : Upper (D 7) (R 7) [34,257,24,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35652 : Route 9 := (fun mask => (mask,id))

def c35652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35652 : Upper (D 7) (R 7) [34,257,24,68,160] 13 := by
  apply FastRouting.sound _ _ [34,257,24,68,160] 13 (by decide) (choices 1) [1,2,64,128] r35652 c35652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20870
  · exact u20871
  · exact u20872
  · exact u20873

def b35653 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 12, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 28 76 208 163 227 163 419), lower := (rows 35 259 28 76 208 32 64 128 256), losses := [] }

theorem u35653 : Upper (D 7) (R 7) [34,257,24,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35654 : Route 9 := (fun mask => (mask,id))

def c35654 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35654 : Upper (D 7) (R 7) [34,257,24,96,192] 13 := by
  apply FastRouting.sound _ _ [34,257,24,96,192] 13 (by decide) (choices 1) [1,2,4,128] r35654 c35654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20874
  · exact u20875
  · exact u20876
  · exact u20877

def b35655 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(4,0)], upper := (rows 35 259 28 200 208 39 103 167 295), lower := (rows 35 259 28 200 208 32 64 128 256), losses := [] }

theorem u35655 : Upper (D 7) (R 7) [34,257,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35656 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 259 37 74 84 184 216 152 408), lower := (rows 35 259 37 74 84 32 64 128 256), losses := [] }

theorem u35656 : Upper (D 7) (R 7) [34,257,33,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35657 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 259 37 74 148 248 216 216 472), lower := (rows 35 259 37 74 148 32 64 128 256), losses := [] }

theorem u35657 : Upper (D 7) (R 7) [34,257,33,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35658 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 259 37 74 152 244 212 212 468), lower := (rows 35 259 37 74 152 32 64 128 256), losses := [] }

theorem u35658 : Upper (D 7) (R 7) [34,257,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35659 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 259 37 74 208 188 220 156 412), lower := (rows 35 259 37 74 208 32 64 128 256), losses := [] }

theorem u35659 : Upper (D 7) (R 7) [34,257,33,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35660 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 259 37 76 152 242 210 210 466), lower := (rows 35 259 37 76 152 32 64 128 256), losses := [] }

theorem u35660 : Upper (D 7) (R 7) [34,257,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35661 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 259 37 76 208 186 218 154 410), lower := (rows 35 259 37 76 208 32 64 128 256), losses := [] }

theorem u35661 : Upper (D 7) (R 7) [34,257,33,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35662 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 259 37 88 152 230 198 198 454), lower := (rows 35 259 37 88 152 32 64 128 256), losses := [] }

theorem u35662 : Upper (D 7) (R 7) [34,257,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35663 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 38 73 84 184 216 152 408), lower := (rows 35 259 38 73 84 32 64 128 256), losses := [] }

theorem u35663 : Upper (D 7) (R 7) [34,257,34,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35664 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 38 73 148 248 216 216 472), lower := (rows 35 259 38 73 148 32 64 128 256), losses := [] }

theorem u35664 : Upper (D 7) (R 7) [34,257,34,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35665 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 38 73 152 244 212 212 468), lower := (rows 35 259 38 73 152 32 64 128 256), losses := [] }

theorem u35665 : Upper (D 7) (R 7) [34,257,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35666 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 38 73 208 188 220 156 412), lower := (rows 35 259 38 73 208 32 64 128 256), losses := [] }

theorem u35666 : Upper (D 7) (R 7) [34,257,34,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35667 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 38 76 152 241 209 209 465), lower := (rows 35 259 38 76 152 32 64 128 256), losses := [] }

theorem u35667 : Upper (D 7) (R 7) [34,257,34,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35668 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 38 76 208 185 217 153 409), lower := (rows 35 259 38 76 208 32 64 128 256), losses := [] }

theorem u35668 : Upper (D 7) (R 7) [34,257,34,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35669 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 38 88 152 229 197 197 453), lower := (rows 35 259 38 88 152 32 64 128 256), losses := [] }

theorem u35669 : Upper (D 7) (R 7) [34,257,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35670 : Route 9 := (fun mask => (mask,id))

def c35670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35670 : Upper (D 7) (R 7) [34,257,40,65,66] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,66] 13 (by decide) (choices 1) [4,16,128] r35670 c35670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20878
  · exact u20879
  · exact u20880

def r35671 : Route 9 := (fun mask => (mask,id))

def c35671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35671 : Upper (D 7) (R 7) [34,257,40,65,68] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,68] 13 (by decide) (choices 1) [2,16,128] r35671 c35671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20881
  · exact u20882
  · exact u20883

def r35672 : Route 9 := (fun mask => (mask,id))

def c35672 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35672 : Upper (D 7) (R 7) [34,257,40,65,130] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,130] 13 (by decide) (choices 1) [4,16,64,128] r35672 c35672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20884
  · exact u20885
  · exact u20886
  · exact u20887

def r35673 : Route 9 := (fun mask => (mask,id))

def c35673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35673 : Upper (D 7) (R 7) [34,257,40,65,132] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,132] 13 (by decide) (choices 1) [2,16,64,128] r35673 c35673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20888
  · exact u20889
  · exact u20890
  · exact u20891

def r35674 : Route 9 := (fun mask => (mask,id))

def c35674 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35674 : Upper (D 7) (R 7) [34,257,40,65,192] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,192] 13 (by decide) (choices 1) [2,4,16,128] r35674 c35674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20892
  · exact u20893
  · exact u20894
  · exact u20895

def r35675 : Route 9 := (fun mask => (mask,id))

def c35675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35675 : Upper (D 7) (R 7) [34,257,40,66,65] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,65] 13 (by decide) (choices 1) [4,16,128] r35675 c35675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20896
  · exact u20897
  · exact u20898

def r35676 : Route 9 := (fun mask => (mask,id))

def c35676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35676 : Upper (D 7) (R 7) [34,257,40,66,68] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,68] 13 (by decide) (choices 1) [1,16,128] r35676 c35676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20899
  · exact u20900
  · exact u20901

def r35677 : Route 9 := (fun mask => (mask,id))

def c35677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35677 : Upper (D 7) (R 7) [34,257,40,66,129] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,129] 13 (by decide) (choices 1) [4,16,64,128] r35677 c35677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20902
  · exact u20903
  · exact u20904
  · exact u20905

def r35678 : Route 9 := (fun mask => (mask,id))

def c35678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35678 : Upper (D 7) (R 7) [34,257,40,66,132] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,132] 13 (by decide) (choices 1) [1,16,64,128] r35678 c35678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20906
  · exact u20907
  · exact u20908
  · exact u20909

def r35679 : Route 9 := (fun mask => (mask,id))

def c35679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35679 : Upper (D 7) (R 7) [34,257,40,66,192] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,192] 13 (by decide) (choices 1) [1,4,16,128] r35679 c35679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20910
  · exact u20911
  · exact u20912
  · exact u20913

def b35680 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(4,5)], upper := (rows 35 259 44 76 81 178 210 146 402), lower := (rows 35 259 44 76 81 32 64 128 256), losses := [] }

theorem u35680 : Upper (D 7) (R 7) [34,257,40,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35681 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(4,5)], upper := (rows 35 259 44 76 82 177 209 145 401), lower := (rows 35 259 44 76 82 32 64 128 256), losses := [] }

theorem u35681 : Upper (D 7) (R 7) [34,257,40,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35682 : Route 9 := (fun mask => (mask,id))

def c35682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35682 : Upper (D 7) (R 7) [34,257,40,68,129] 13 := by
  apply FastRouting.sound _ _ [34,257,40,68,129] 13 (by decide) (choices 1) [2,16,64,128] r35682 c35682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20914
  · exact u20915
  · exact u20916
  · exact u20917

def r35683 : Route 9 := (fun mask => (mask,id))

def c35683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35683 : Upper (D 7) (R 7) [34,257,40,68,130] 13 := by
  apply FastRouting.sound _ _ [34,257,40,68,130] 13 (by decide) (choices 1) [1,16,64,128] r35683 c35683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20918
  · exact u20919
  · exact u20920
  · exact u20921

def b35684 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 291, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(4,5)], upper := (rows 35 259 44 76 208 179 211 147 403), lower := (rows 35 259 44 76 208 32 64 128 256), losses := [] }

theorem u35684 : Upper (D 7) (R 7) [34,257,40,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35685 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 44 88 81 166 198 134 390), lower := (rows 35 259 44 88 81 32 64 128 256), losses := [] }

theorem u35685 : Upper (D 7) (R 7) [34,257,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35686 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 44 88 82 165 197 133 389), lower := (rows 35 259 44 88 82 32 64 128 256), losses := [] }

theorem u35686 : Upper (D 7) (R 7) [34,257,40,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35687 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 44 88 84 163 195 131 387), lower := (rows 35 259 44 88 84 32 64 128 256), losses := [] }

theorem u35687 : Upper (D 7) (R 7) [34,257,40,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35688 : Route 9 := (fun mask => (mask,id))

def c35688 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35688 : Upper (D 7) (R 7) [34,257,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,257,40,80,129] 13 (by decide) (choices 1) [2,4,64,128] r35688 c35688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20922
  · exact u20923
  · exact u20924
  · exact u20925

def r35689 : Route 9 := (fun mask => (mask,id))

def c35689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35689 : Upper (D 7) (R 7) [34,257,40,80,130] 13 := by
  apply FastRouting.sound _ _ [34,257,40,80,130] 13 (by decide) (choices 1) [1,4,64,128] r35689 c35689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20926
  · exact u20927
  · exact u20928
  · exact u20929

def r35690 : Route 9 := (fun mask => (mask,id))

def c35690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35690 : Upper (D 7) (R 7) [34,257,40,80,132] 13 := by
  apply FastRouting.sound _ _ [34,257,40,80,132] 13 (by decide) (choices 1) [1,2,64,128] r35690 c35690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20930
  · exact u20931
  · exact u20932
  · exact u20933

def b35691 : PairBound 9 := { available := 135, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 44 88 208 167 199 135 391), lower := (rows 35 259 44 88 208 32 64 128 256), losses := [] }

theorem u35691 : Upper (D 7) (R 7) [34,257,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35692 : Route 9 := (fun mask => (mask,id))

def c35692 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35692 : Upper (D 7) (R 7) [34,257,40,192,65] 13 := by
  apply FastRouting.sound _ _ [34,257,40,192,65] 13 (by decide) (choices 1) [2,4,16,128] r35692 c35692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20934
  · exact u20935
  · exact u20936
  · exact u20937

def r35693 : Route 9 := (fun mask => (mask,id))

def c35693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35693 : Upper (D 7) (R 7) [34,257,40,192,66] 13 := by
  apply FastRouting.sound _ _ [34,257,40,192,66] 13 (by decide) (choices 1) [1,4,16,128] r35693 c35693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20938
  · exact u20939
  · exact u20940
  · exact u20941

def r35694 : Route 9 := (fun mask => (mask,id))

def c35694 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35694 : Upper (D 7) (R 7) [34,257,40,192,68] 13 := by
  apply FastRouting.sound _ _ [34,257,40,192,68] 13 (by decide) (choices 1) [1,2,16,128] r35694 c35694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20942
  · exact u20943
  · exact u20944
  · exact u20945

def b35695 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 35 259 44 200 208 55 87 151 279), lower := (rows 35 259 44 200 208 32 64 128 256), losses := [] }

theorem u35695 : Upper (D 7) (R 7) [34,257,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35696 : Route 9 := (fun mask => (mask,id))

def c35696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35696 : Upper (D 7) (R 7) [34,257,65,66,132] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,132] 13 (by decide) (choices 1) [8,16,128] r35696 c35696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20946
  · exact u20947
  · exact u20948

def r35697 : Route 9 := (fun mask => (mask,id))

def c35697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35697 : Upper (D 7) (R 7) [34,257,65,66,136] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,136] 13 (by decide) (choices 1) [4,16,128] r35697 c35697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20949
  · exact u20950
  · exact u20951

def r35698 : Route 9 := (fun mask => (mask,id))

def c35698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35698 : Upper (D 7) (R 7) [34,257,65,66,160] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,160] 13 (by decide) (choices 1) [4,8,16,128] r35698 c35698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20952
  · exact u20953
  · exact u20954
  · exact u20955

def b35699 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 69 76 146 184 248 184 440), lower := (rows 35 259 69 76 146 32 64 128 256), losses := [] }

theorem u35699 : Upper (D 7) (R 7) [34,257,65,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u35699
end Delivery.IrregularNine14.P07
