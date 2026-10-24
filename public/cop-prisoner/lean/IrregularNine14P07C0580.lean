import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0328
import IrregularNine14P07C0329
import IrregularNine14P07C0330

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34800 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 261 11 208 184 248 184 440), lower := (rows 35 70 261 11 208 32 64 128 256), losses := [] }

theorem u34800 : Upper (D 7) (R 7) [34,68,257,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34801 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 261 25 26 224 224 224 480), lower := (rows 35 70 261 25 26 32 64 128 256), losses := [] }

theorem u34801 : Upper (D 7) (R 7) [34,68,257,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34802 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 261 25 50 232 200 200 456), lower := (rows 35 70 261 25 50 32 64 128 256), losses := [] }

theorem u34802 : Upper (D 7) (R 7) [34,68,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34803 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 261 25 56 226 194 194 450), lower := (rows 35 70 261 25 56 32 64 128 256), losses := [] }

theorem u34803 : Upper (D 7) (R 7) [34,68,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34804 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 261 25 82 168 232 168 424), lower := (rows 35 70 261 25 82 32 64 128 256), losses := [] }

theorem u34804 : Upper (D 7) (R 7) [34,68,257,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34805 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 226, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 35 70 261 25 88 162 226 162 418), lower := (rows 35 70 261 25 88 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 39 71 135 263), good := (rows 482 486 486 504 88 32 64 128 256) }] }

theorem u34805 : Upper (D 7) (R 7) [34,68,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34806 : Route 9 := (fun mask => (mask,id))

def c34806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34806 : Upper (D 7) (R 7) [34,68,257,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,96] 13 (by decide) (choices 1) [2,8,128] r34806 c34806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19729
  · exact u19730
  · exact u19731

def r34807 : Route 9 := (fun mask => (mask,id))

def c34807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34807 : Upper (D 7) (R 7) [34,68,257,17,130] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,130] 13 (by decide) (choices 1) [8,64,128] r34807 c34807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19732
  · exact u19733
  · exact u19734

def r34808 : Route 9 := (fun mask => (mask,id))

def c34808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34808 : Upper (D 7) (R 7) [34,68,257,17,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,136] 13 (by decide) (choices 1) [2,64,128] r34808 c34808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19735
  · exact u19736
  · exact u19737

def r34809 : Route 9 := (fun mask => (mask,id))

def c34809 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34809 : Upper (D 7) (R 7) [34,68,257,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,160] 13 (by decide) (choices 1) [2,8,64,128] r34809 c34809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19738
  · exact u19739
  · exact u19740
  · exact u19741

def r34810 : Route 9 := (fun mask => (mask,id))

def c34810 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34810 : Upper (D 7) (R 7) [34,68,257,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,192] 13 (by decide) (choices 1) [2,8,128] r34810 c34810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19742
  · exact u19743
  · exact u19744

def b34811 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 261 26 49 232 200 200 456), lower := (rows 35 70 261 26 49 32 64 128 256), losses := [] }

theorem u34811 : Upper (D 7) (R 7) [34,68,257,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34812 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 261 26 56 225 193 193 449), lower := (rows 35 70 261 26 56 32 64 128 256), losses := [] }

theorem u34812 : Upper (D 7) (R 7) [34,68,257,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34813 : Route 9 := (fun mask => (mask,id))

def c34813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34813 : Upper (D 7) (R 7) [34,68,257,18,65] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,65] 13 (by decide) (choices 1) [8,128] r34813 c34813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19745
  · exact u19746

def b34814 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 35 70 261 26 88 161 225 161 417), lower := (rows 35 70 261 26 88 32 64 128 256), losses := [] }

theorem u34814 : Upper (D 7) (R 7) [34,68,257,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34815 : Route 9 := (fun mask => (mask,id))

def c34815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34815 : Upper (D 7) (R 7) [34,68,257,18,96] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,96] 13 (by decide) (choices 1) [1,8,128] r34815 c34815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19747
  · exact u19748
  · exact u19749

def r34816 : Route 9 := (fun mask => (mask,id))

def c34816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34816 : Upper (D 7) (R 7) [34,68,257,18,129] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,129] 13 (by decide) (choices 1) [8,64,128] r34816 c34816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19750
  · exact u19751
  · exact u19752

def r34817 : Route 9 := (fun mask => (mask,id))

def c34817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34817 : Upper (D 7) (R 7) [34,68,257,18,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,136] 13 (by decide) (choices 1) [1,64,128] r34817 c34817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19753
  · exact u19754
  · exact u19755

def r34818 : Route 9 := (fun mask => (mask,id))

def c34818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34818 : Upper (D 7) (R 7) [34,68,257,18,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,160] 13 (by decide) (choices 1) [1,8,64,128] r34818 c34818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19756
  · exact u19757
  · exact u19758
  · exact u19759

def r34819 : Route 9 := (fun mask => (mask,id))

def c34819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34819 : Upper (D 7) (R 7) [34,68,257,18,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,192] 13 (by decide) (choices 1) [1,8,128] r34819 c34819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19760
  · exact u19761
  · exact u19762

def b34820 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 261 41 88 178 210 146 402), lower := (rows 35 70 261 41 88 32 64 128 256), losses := [] }

theorem u34820 : Upper (D 7) (R 7) [34,68,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34821 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 261 41 146 248 216 216 472), lower := (rows 35 70 261 41 146 32 64 128 256), losses := [] }

theorem u34821 : Upper (D 7) (R 7) [34,68,257,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34822 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 261 41 152 242 210 210 466), lower := (rows 35 70 261 41 152 32 64 128 256), losses := [] }

theorem u34822 : Upper (D 7) (R 7) [34,68,257,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34823 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 261 41 208 186 218 154 410), lower := (rows 35 70 261 41 208 32 64 128 256), losses := [] }

theorem u34823 : Upper (D 7) (R 7) [34,68,257,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34824 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 261 42 81 184 216 152 408), lower := (rows 35 70 261 42 81 32 64 128 256), losses := [] }

theorem u34824 : Upper (D 7) (R 7) [34,68,257,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34825 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 261 42 88 177 209 145 401), lower := (rows 35 70 261 42 88 32 64 128 256), losses := [] }

theorem u34825 : Upper (D 7) (R 7) [34,68,257,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34826 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 261 42 145 248 216 216 472), lower := (rows 35 70 261 42 145 32 64 128 256), losses := [] }

theorem u34826 : Upper (D 7) (R 7) [34,68,257,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34827 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 261 42 152 241 209 209 465), lower := (rows 35 70 261 42 152 32 64 128 256), losses := [] }

theorem u34827 : Upper (D 7) (R 7) [34,68,257,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34828 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 261 42 208 185 217 153 409), lower := (rows 35 70 261 42 208 32 64 128 256), losses := [] }

theorem u34828 : Upper (D 7) (R 7) [34,68,257,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34829 : Route 9 := (fun mask => (mask,id))

def c34829 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34829 : Upper (D 7) (R 7) [34,68,257,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,65] 13 (by decide) (choices 1) [2,8,128] r34829 c34829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19763
  · exact u19764
  · exact u19765

def b34830 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 261 56 82 169 201 137 393), lower := (rows 35 70 261 56 82 32 64 128 256), losses := [] }

theorem u34830 : Upper (D 7) (R 7) [34,68,257,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34831 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 35 70 261 56 88 163 195 131 387), lower := (rows 35 70 261 56 88 32 64 128 256), losses := [] }

theorem u34831 : Upper (D 7) (R 7) [34,68,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34832 : Route 9 := (fun mask => (mask,id))

def c34832 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34832 : Upper (D 7) (R 7) [34,68,257,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,129] 13 (by decide) (choices 1) [2,8,64,128] r34832 c34832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19766
  · exact u19767
  · exact u19768
  · exact u19769

def r34833 : Route 9 := (fun mask => (mask,id))

def c34833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34833 : Upper (D 7) (R 7) [34,68,257,48,130] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,130] 13 (by decide) (choices 1) [1,8,64,128] r34833 c34833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19770
  · exact u19771
  · exact u19772
  · exact u19773

def r34834 : Route 9 := (fun mask => (mask,id))

def c34834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34834 : Upper (D 7) (R 7) [34,68,257,48,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,136] 13 (by decide) (choices 1) [1,2,64,128] r34834 c34834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19774
  · exact u19775
  · exact u19776
  · exact u19777

def r34835 : Route 9 := (fun mask => (mask,id))

def c34835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34835 : Upper (D 7) (R 7) [34,68,257,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,192] 13 (by decide) (choices 1) [1,2,8,128] r34835 c34835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19778
  · exact u19779
  · exact u19780
  · exact u19781

def r34836 : Route 9 := (fun mask => (mask,id))

def c34836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34836 : Upper (D 7) (R 7) [34,68,257,65,130] 13 := by
  apply FastRouting.sound _ _ [34,68,257,65,130] 13 (by decide) (choices 1) [8,16,128] r34836 c34836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19782
  · exact u19783
  · exact u19784

def r34837 : Route 9 := (fun mask => (mask,id))

def c34837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34837 : Upper (D 7) (R 7) [34,68,257,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,65,136] 13 (by decide) (choices 1) [2,16,128] r34837 c34837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19785
  · exact u19786
  · exact u19787

def r34838 : Route 9 := (fun mask => (mask,id))

def c34838 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34838 : Upper (D 7) (R 7) [34,68,257,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,65,160] 13 (by decide) (choices 1) [2,8,16,128] r34838 c34838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19788
  · exact u19789
  · exact u19790
  · exact u19791

def b34839 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 261 74 145 184 248 184 440), lower := (rows 35 70 261 74 145 32 64 128 256), losses := [] }

theorem u34839 : Upper (D 7) (R 7) [34,68,257,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34840 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 261 74 152 177 241 177 433), lower := (rows 35 70 261 74 152 32 64 128 256), losses := [] }

theorem u34840 : Upper (D 7) (R 7) [34,68,257,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34841 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 261 74 176 185 217 153 409), lower := (rows 35 70 261 74 176 32 64 128 256), losses := [] }

theorem u34841 : Upper (D 7) (R 7) [34,68,257,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34842 : Route 9 := (fun mask => (mask,id))

def c34842 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34842 : Upper (D 7) (R 7) [34,68,257,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,129] 13 (by decide) (choices 1) [2,8,128] r34842 c34842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19792
  · exact u19793
  · exact u19794

def r34843 : Route 9 := (fun mask => (mask,id))

def c34843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34843 : Upper (D 7) (R 7) [34,68,257,80,130] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,130] 13 (by decide) (choices 1) [1,8,128] r34843 c34843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19795
  · exact u19796
  · exact u19797

def r34844 : Route 9 := (fun mask => (mask,id))

def c34844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34844 : Upper (D 7) (R 7) [34,68,257,80,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,136] 13 (by decide) (choices 1) [1,2,128] r34844 c34844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19798
  · exact u19799
  · exact u19800

def r34845 : Route 9 := (fun mask => (mask,id))

def c34845 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34845 : Upper (D 7) (R 7) [34,68,257,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,160] 13 (by decide) (choices 1) [1,2,8,128] r34845 c34845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19801
  · exact u19802
  · exact u19803
  · exact u19804

def r34846 : Route 9 := (fun mask => (mask,id))

def c34846 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34846 : Upper (D 7) (R 7) [34,68,257,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,129] 13 (by decide) (choices 1) [2,8,16,128] r34846 c34846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19805
  · exact u19806
  · exact u19807
  · exact u19808

def r34847 : Route 9 := (fun mask => (mask,id))

def c34847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34847 : Upper (D 7) (R 7) [34,68,257,96,130] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,130] 13 (by decide) (choices 1) [1,8,16,128] r34847 c34847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19809
  · exact u19810
  · exact u19811
  · exact u19812

def r34848 : Route 9 := (fun mask => (mask,id))

def c34848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34848 : Upper (D 7) (R 7) [34,68,257,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,136] 13 (by decide) (choices 1) [1,2,16,128] r34848 c34848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19813
  · exact u19814
  · exact u19815
  · exact u19816

def r34849 : Route 9 := (fun mask => (mask,id))

def c34849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34849 : Upper (D 7) (R 7) [34,68,257,129,130] 13 := by
  apply FastRouting.sound _ _ [34,68,257,129,130] 13 (by decide) (choices 1) [8,16,64] r34849 c34849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19817
  · exact u19818
  · exact u19819

def b34850 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 70 261 137 152 114 114 242 370), lower := (rows 35 70 261 137 152 32 64 128 256), losses := [] }

theorem u34850 : Upper (D 7) (R 7) [34,68,257,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34851 : Route 9 := (fun mask => (mask,id))

def c34851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34851 : Upper (D 7) (R 7) [34,68,257,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,129,160] 13 (by decide) (choices 1) [2,8,16,64] r34851 c34851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19820
  · exact u19821
  · exact u19822
  · exact u19823

def r34852 : Route 9 := (fun mask => (mask,id))

def c34852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34852 : Upper (D 7) (R 7) [34,68,257,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,129,192] 13 (by decide) (choices 1) [2,8,16] r34852 c34852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19824
  · exact u19825
  · exact u19826

def b34853 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 70 261 138 152 113 113 241 369), lower := (rows 35 70 261 138 152 32 64 128 256), losses := [] }

theorem u34853 : Upper (D 7) (R 7) [34,68,257,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34854 : Route 9 := (fun mask => (mask,id))

def c34854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34854 : Upper (D 7) (R 7) [34,68,257,130,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,130,160] 13 (by decide) (choices 1) [1,8,16,64] r34854 c34854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19827
  · exact u19828
  · exact u19829
  · exact u19830

def r34855 : Route 9 := (fun mask => (mask,id))

def c34855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34855 : Upper (D 7) (R 7) [34,68,257,130,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,130,192] 13 (by decide) (choices 1) [1,8,16] r34855 c34855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19831
  · exact u19832
  · exact u19833

def b34856 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 261 152 152 99 99 227 355), lower := (rows 35 70 261 152 152 32 64 128 256), losses := [] }

theorem u34856 : Upper (D 7) (R 7) [34,68,257,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34857 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 261 152 176 107 75 203 331), lower := (rows 35 70 261 152 176 32 64 128 256), losses := [] }

theorem u34857 : Upper (D 7) (R 7) [34,68,257,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34858 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 261 152 208 43 107 171 299), lower := (rows 35 70 261 152 208 32 64 128 256), losses := [] }

theorem u34858 : Upper (D 7) (R 7) [34,68,257,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34859 : Route 9 := (fun mask => (mask,id))

def c34859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34859 : Upper (D 7) (R 7) [34,68,257,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,160,192] 13 (by decide) (choices 1) [1,2,8,16] r34859 c34859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19834
  · exact u19835
  · exact u19836
  · exact u19837

#print axioms u34859
end Delivery.IrregularNine14.P07
