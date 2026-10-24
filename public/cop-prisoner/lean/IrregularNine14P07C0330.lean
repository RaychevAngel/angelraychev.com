import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0089
import IrregularNine14P07C0090

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19800 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 70 261 88 152 160 99 163 291), lower := (rows 35 70 261 88 152 160 64 128 256), losses := [] }

theorem u19800 : Upper (D 7) (R 7) [34,68,257,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19801 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 88 176 33 202 138 394), lower := (rows 35 70 261 88 176 33 64 128 256), losses := [] }

theorem u19801 : Upper (D 7) (R 7) [34,68,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19802 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 88 176 34 201 137 393), lower := (rows 35 70 261 88 176 34 64 128 256), losses := [] }

theorem u19802 : Upper (D 7) (R 7) [34,68,257,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19803 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,5),(2,5),(2,6)], upper := (rows 35 70 261 88 176 40 195 131 387), lower := (rows 35 70 261 88 176 40 64 128 256), losses := [] }

theorem u19803 : Upper (D 7) (R 7) [34,68,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19803 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19804 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 261 88 176 160 75 139 267), lower := (rows 35 70 261 88 176 160 64 128 256), losses := [] }

theorem u19804 : Upper (D 7) (R 7) [34,68,257,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19805 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 104 145 34 216 152 408), lower := (rows 35 70 261 104 145 34 64 128 256), losses := [] }

theorem u19805 : Upper (D 7) (R 7) [34,68,257,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19806 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 261 104 145 40 210 146 402), lower := (rows 35 70 261 104 145 40 64 128 256), losses := [] }

theorem u19806 : Upper (D 7) (R 7) [34,68,257,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19806 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19807 : Route 9 := (fun mask => (mask,id))

def c19807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19807 : Upper (D 7) (R 7) [34,68,257,96,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,129,16] 13 (by decide) (choices 1) [2,8,128] r19807 c19807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5394
  · exact u5395
  · exact u5396

def r19808 : Route 9 := (fun mask => (mask,id))

def c19808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19808 : Upper (D 7) (R 7) [34,68,257,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,129,128] 13 (by decide) (choices 1) [2,8,16] r19808 c19808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5397
  · exact u5398
  · exact u5399

def b19809 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,0),(3,7),(4,0)], upper := (rows 35 70 261 104 146 33 216 152 408), lower := (rows 35 70 261 104 146 33 64 128 256), losses := [] }

theorem u19809 : Upper (D 7) (R 7) [34,68,257,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19810 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 261 104 146 40 209 145 401), lower := (rows 35 70 261 104 146 40 64 128 256), losses := [] }

theorem u19810 : Upper (D 7) (R 7) [34,68,257,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19810 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19811 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 261 104 146 48 201 137 393), lower := (rows 35 70 261 104 146 48 64 128 256), losses := [] }

theorem u19811 : Upper (D 7) (R 7) [34,68,257,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19811 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19812 : Route 9 := (fun mask => (mask,id))

def c19812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19812 : Upper (D 7) (R 7) [34,68,257,96,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,130,128] 13 (by decide) (choices 1) [1,8,16] r19812 c19812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5400
  · exact u5401
  · exact u5402

def b19813 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,0),(3,7),(4,0)], upper := (rows 35 70 261 104 152 33 210 146 402), lower := (rows 35 70 261 104 152 33 64 128 256), losses := [] }

theorem u19813 : Upper (D 7) (R 7) [34,68,257,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19814 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 104 152 34 209 145 401), lower := (rows 35 70 261 104 152 34 64 128 256), losses := [] }

theorem u19814 : Upper (D 7) (R 7) [34,68,257,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19815 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,5),(2,5),(2,6)], upper := (rows 35 70 261 104 152 48 195 131 387), lower := (rows 35 70 261 104 152 48 64 128 256), losses := [] }

theorem u19815 : Upper (D 7) (R 7) [34,68,257,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19815 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19816 : Route 9 := (fun mask => (mask,id))

def c19816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19816 : Upper (D 7) (R 7) [34,68,257,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,136,128] 13 (by decide) (choices 1) [1,2,16] r19816 c19816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5403
  · exact u5404
  · exact u5405

def b19817 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 70 261 137 146 40 112 240 368), lower := (rows 35 70 261 137 146 40 64 128 256), losses := [] }

theorem u19817 : Upper (D 7) (R 7) [34,68,257,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19817 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19818 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 261 137 146 48 104 232 360), lower := (rows 35 70 261 137 146 48 64 128 256), losses := [] }

theorem u19818 : Upper (D 7) (R 7) [34,68,257,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19818 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19819 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 137 146 96 120 184 312), lower := (rows 35 70 261 137 146 96 64 128 256), losses := [] }

theorem u19819 : Upper (D 7) (R 7) [34,68,257,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19820 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 137 176 34 88 216 344), lower := (rows 35 70 261 137 176 34 64 128 256), losses := [] }

theorem u19820 : Upper (D 7) (R 7) [34,68,257,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19821 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 261 137 176 40 82 210 338), lower := (rows 35 70 261 137 176 40 64 128 256), losses := [] }

theorem u19821 : Upper (D 7) (R 7) [34,68,257,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19821 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19822 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 261 137 176 48 74 202 330), lower := (rows 35 70 261 137 176 48 64 128 256), losses := [] }

theorem u19822 : Upper (D 7) (R 7) [34,68,257,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19822 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19823 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 137 176 96 90 154 282), lower := (rows 35 70 261 137 176 96 64 128 256), losses := [] }

theorem u19823 : Upper (D 7) (R 7) [34,68,257,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19824 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 137 208 34 120 184 312), lower := (rows 35 70 261 137 208 34 64 128 256), losses := [] }

theorem u19824 : Upper (D 7) (R 7) [34,68,257,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19825 : Route 9 := (fun mask => (mask,id))

def c19825 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19825 : Upper (D 7) (R 7) [34,68,257,129,192,8] 13 := by
  apply FastRouting.sound _ _ [34,68,257,129,192,8] 13 (by decide) (choices 1) [2,16,32] r19825 c19825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5406
  · exact u5407
  · exact u5408

def r19826 : Route 9 := (fun mask => (mask,id))

def c19826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19826 : Upper (D 7) (R 7) [34,68,257,129,192,16] 13 := by
  apply FastRouting.sound _ _ [34,68,257,129,192,16] 13 (by decide) (choices 1) [2,8,32] r19826 c19826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5409
  · exact u5410
  · exact u5411

def b19827 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 138 176 33 88 216 344), lower := (rows 35 70 261 138 176 33 64 128 256), losses := [] }

theorem u19827 : Upper (D 7) (R 7) [34,68,257,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19828 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 261 138 176 40 81 209 337), lower := (rows 35 70 261 138 176 40 64 128 256), losses := [] }

theorem u19828 : Upper (D 7) (R 7) [34,68,257,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19828 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19829 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 261 138 176 48 73 201 329), lower := (rows 35 70 261 138 176 48 64 128 256), losses := [] }

theorem u19829 : Upper (D 7) (R 7) [34,68,257,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19829 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19830 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 138 176 96 89 153 281), lower := (rows 35 70 261 138 176 96 64 128 256), losses := [] }

theorem u19830 : Upper (D 7) (R 7) [34,68,257,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19831 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 138 208 33 120 184 312), lower := (rows 35 70 261 138 208 33 64 128 256), losses := [] }

theorem u19831 : Upper (D 7) (R 7) [34,68,257,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19832 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 261 138 208 40 113 177 305), lower := (rows 35 70 261 138 208 40 64 128 256), losses := [] }

theorem u19832 : Upper (D 7) (R 7) [34,68,257,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19832 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19833 : Route 9 := (fun mask => (mask,id))

def c19833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19833 : Upper (D 7) (R 7) [34,68,257,130,192,16] 13 := by
  apply FastRouting.sound _ _ [34,68,257,130,192,16] 13 (by decide) (choices 1) [1,8,32] r19833 c19833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5412
  · exact u5413
  · exact u5414

def b19834 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 168 208 33 90 154 282), lower := (rows 35 70 261 168 208 33 64 128 256), losses := [] }

theorem u19834 : Upper (D 7) (R 7) [34,68,257,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19835 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 168 208 34 89 153 281), lower := (rows 35 70 261 168 208 34 64 128 256), losses := [] }

theorem u19835 : Upper (D 7) (R 7) [34,68,257,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19836 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 261 168 208 40 83 147 275), lower := (rows 35 70 261 168 208 40 64 128 256), losses := [] }

theorem u19836 : Upper (D 7) (R 7) [34,68,257,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19836 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19837 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 261 168 208 48 75 139 267), lower := (rows 35 70 261 168 208 48 64 128 256), losses := [] }

theorem u19837 : Upper (D 7) (R 7) [34,68,257,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19837 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19838 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 0, region := 216, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 70 262 25 152 33 224 224 480), lower := (rows 35 70 262 25 152 33 64 128 256), losses := [] }

theorem u19838 : Upper (D 7) (R 7) [34,68,258,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19839 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 152, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 262 25 152 96 225 161 417), lower := (rows 35 70 262 25 152 96 64 128 256), losses := [] }

theorem u19839 : Upper (D 7) (R 7) [34,68,258,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19840 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 35 70 262 25 152 160 97 225 353), lower := (rows 35 70 262 25 152 160 64 128 256), losses := [] }

theorem u19840 : Upper (D 7) (R 7) [34,68,258,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19841 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 262 25 208 33 232 168 424), lower := (rows 35 70 262 25 208 33 64 128 256), losses := [] }

theorem u19841 : Upper (D 7) (R 7) [34,68,258,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19842 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 262 25 208 40 225 161 417), lower := (rows 35 70 262 25 208 40 64 128 256), losses := [] }

theorem u19842 : Upper (D 7) (R 7) [34,68,258,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19842 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19843 : Route 9 := (fun mask => (mask,id))

def c19843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19843 : Upper (D 7) (R 7) [34,68,258,17,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,258,17,192,128] 13 (by decide) (choices 1) [1,8,32] r19843 c19843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5415
  · exact u5416
  · exact u5417

def b19844 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 262 56 81 33 200 136 392), lower := (rows 35 70 262 56 81 33 64 128 256), losses := [] }

theorem u19844 : Upper (D 7) (R 7) [34,68,258,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19845 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 262 56 81 40 193 129 385), lower := (rows 35 70 262 56 81 40 64 128 256), losses := [] }

theorem u19845 : Upper (D 7) (R 7) [34,68,258,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19845 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19846 : Route 9 := (fun mask => (mask,id))

def c19846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19846 : Upper (D 7) (R 7) [34,68,258,48,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,258,48,65,128] 13 (by decide) (choices 1) [1,8,128] r19846 c19846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5418
  · exact u5419
  · exact u5420

def b19847 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 262 56 145 33 200 200 456), lower := (rows 35 70 262 56 145 33 64 128 256), losses := [] }

theorem u19847 : Upper (D 7) (R 7) [34,68,258,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19848 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 262 56 145 40 193 193 449), lower := (rows 35 70 262 56 145 40 64 128 256), losses := [] }

theorem u19848 : Upper (D 7) (R 7) [34,68,258,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19848 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19849 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 152, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 262 56 145 96 201 137 393), lower := (rows 35 70 262 56 145 96 64 128 256), losses := [] }

theorem u19849 : Upper (D 7) (R 7) [34,68,258,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19850 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 35 70 262 56 145 160 73 201 329), lower := (rows 35 70 262 56 145 160 64 128 256), losses := [] }

theorem u19850 : Upper (D 7) (R 7) [34,68,258,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19851 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 262 56 208 33 201 137 393), lower := (rows 35 70 262 56 208 33 64 128 256), losses := [] }

theorem u19851 : Upper (D 7) (R 7) [34,68,258,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19852 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 262 56 208 40 193 129 385), lower := (rows 35 70 262 56 208 40 64 128 256), losses := [] }

theorem u19852 : Upper (D 7) (R 7) [34,68,258,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19852 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19853 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 262 56 208 160 73 137 265), lower := (rows 35 70 262 56 208 160 64 128 256), losses := [] }

theorem u19853 : Upper (D 7) (R 7) [34,68,258,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19854 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 262 73 145 40 240 176 432), lower := (rows 35 70 262 73 145 40 64 128 256), losses := [] }

theorem u19854 : Upper (D 7) (R 7) [34,68,258,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19854 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19855 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 176, targets := 64 }], pairs := [(3,1),(4,1),(4,6)], upper := (rows 35 70 262 73 145 48 232 168 424), lower := (rows 35 70 262 73 145 48 64 128 256), losses := [] }

theorem u19855 : Upper (D 7) (R 7) [34,68,258,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19855 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19856 : Route 9 := (fun mask => (mask,id))

def c19856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19856 : Upper (D 7) (R 7) [34,68,258,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,258,65,129,128] 13 (by decide) (choices 1) [8,16,32] r19856 c19856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5421
  · exact u5422
  · exact u5423

def b19857 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 262 73 152 33 240 176 432), lower := (rows 35 70 262 73 152 33 64 128 256), losses := [] }

theorem u19857 : Upper (D 7) (R 7) [34,68,258,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19858 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 262 73 152 48 225 161 417), lower := (rows 35 70 262 73 152 48 64 128 256), losses := [] }

theorem u19858 : Upper (D 7) (R 7) [34,68,258,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19858 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19859 : Route 9 := (fun mask => (mask,id))

def c19859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19859 : Upper (D 7) (R 7) [34,68,258,65,136,128] 13 := by
  apply FastRouting.sound _ _ [34,68,258,65,136,128] 13 (by decide) (choices 1) [1,16,32] r19859 c19859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5424
  · exact u5425
  · exact u5426

#print axioms u19859
end Delivery.IrregularNine14.P07
