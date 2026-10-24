import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0109
import IrregularNine14P07C0110

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22020 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 200 145 34 85 149 277), lower := (rows 35 322 44 200 145 34 64 128 256), losses := [] }

theorem u22020 : Upper (D 7) (R 7) [34,320,40,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22021 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 200 145 36 83 147 275), lower := (rows 35 322 44 200 145 36 64 128 256), losses := [] }

theorem u22021 : Upper (D 7) (R 7) [34,320,40,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22021 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22022 : Route 9 := (fun mask => (mask,id))

def c22022 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22022 : Upper (D 7) (R 7) [34,320,40,192,129,16] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,129,16] 13 (by decide) (choices 1) [1,2,4] r22022 c22022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6593
  · exact u6594
  · exact u6595

def r22023 : Route 9 := (fun mask => (mask,id))

def c22023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22023 : Upper (D 7) (R 7) [34,320,40,192,130,1] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,130,1] 13 (by decide) (choices 1) [1,4,16] r22023 c22023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6596
  · exact u6597
  · exact u6598

def b22024 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 200 146 36 81 145 273), lower := (rows 35 322 44 200 146 36 64 128 256), losses := [] }

theorem u22024 : Upper (D 7) (R 7) [34,320,40,192,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22024 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22025 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 322 44 200 146 48 69 133 261), lower := (rows 35 322 44 200 146 48 64 128 256), losses := [] }

theorem u22025 : Upper (D 7) (R 7) [34,320,40,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22025 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22026 : Route 9 := (fun mask => (mask,id))

def c22026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22026 : Upper (D 7) (R 7) [34,320,40,192,132,1] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,132,1] 13 (by decide) (choices 1) [1,2,16] r22026 c22026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6599
  · exact u6600
  · exact u6601

def b22027 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 44 200 148 34 81 145 273), lower := (rows 35 322 44 200 148 34 64 128 256), losses := [] }

theorem u22027 : Upper (D 7) (R 7) [34,320,40,192,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22028 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 322 44 200 148 48 67 131 259), lower := (rows 35 322 44 200 148 48 64 128 256), losses := [] }

theorem u22028 : Upper (D 7) (R 7) [34,320,40,192,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22028 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22029 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 322 69 137 146 36 120 184 312), lower := (rows 35 322 69 137 146 36 64 128 256), losses := [] }

theorem u22029 : Upper (D 7) (R 7) [34,320,65,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22029 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22030 : Route 9 := (fun mask => (mask,id))

def c22030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22030 : Upper (D 7) (R 7) [34,320,65,129,130,8] 13 := by
  apply FastRouting.sound _ _ [34,320,65,129,130,8] 13 (by decide) (choices 1) [4,16,32] r22030 c22030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6602
  · exact u6603
  · exact u6604

def b22031 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 322 69 137 146 48 108 172 300), lower := (rows 35 322 69 137 146 48 64 128 256), losses := [] }

theorem u22031 : Upper (D 7) (R 7) [34,320,65,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22031 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22032 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 69 137 148 34 120 184 312), lower := (rows 35 322 69 137 148 34 64 128 256), losses := [] }

theorem u22032 : Upper (D 7) (R 7) [34,320,65,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22033 : Route 9 := (fun mask => (mask,id))

def c22033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22033 : Upper (D 7) (R 7) [34,320,65,129,132,8] 13 := by
  apply FastRouting.sound _ _ [34,320,65,129,132,8] 13 (by decide) (choices 1) [2,16,32] r22033 c22033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6605
  · exact u6606
  · exact u6607

def r22034 : Route 9 := (fun mask => (mask,id))

def c22034 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22034 : Upper (D 7) (R 7) [34,320,65,129,132,16] 13 := by
  apply FastRouting.sound _ _ [34,320,65,129,132,16] 13 (by decide) (choices 1) [2,8,32] r22034 c22034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6608
  · exact u6609
  · exact u6610

def b22035 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 69 137 176 34 92 156 284), lower := (rows 35 322 69 137 176 34 64 128 256), losses := [] }

theorem u22035 : Upper (D 7) (R 7) [34,320,65,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22036 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 322 69 137 176 36 90 154 282), lower := (rows 35 322 69 137 176 36 64 128 256), losses := [] }

theorem u22036 : Upper (D 7) (R 7) [34,320,65,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22036 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22037 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 322 69 137 176 40 86 150 278), lower := (rows 35 322 69 137 176 40 64 128 256), losses := [] }

theorem u22037 : Upper (D 7) (R 7) [34,320,65,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22037 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22038 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 69 137 176 48 78 142 270), lower := (rows 35 322 69 137 176 48 64 128 256), losses := [] }

theorem u22038 : Upper (D 7) (R 7) [34,320,65,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22038 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22039 : Route 9 := (fun mask => (mask,id))

def c22039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22039 : Upper (D 7) (R 7) [34,320,65,130,132,1] 13 := by
  apply FastRouting.sound _ _ [34,320,65,130,132,1] 13 (by decide) (choices 1) [8,16,32] r22039 c22039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6611
  · exact u6612
  · exact u6613

def b22040 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 322 69 138 148 40 113 177 305), lower := (rows 35 322 69 138 148 40 64 128 256), losses := [] }

theorem u22040 : Upper (D 7) (R 7) [34,320,65,130,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22040 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22041 : Route 9 := (fun mask => (mask,id))

def c22041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22041 : Upper (D 7) (R 7) [34,320,65,130,132,16] 13 := by
  apply FastRouting.sound _ _ [34,320,65,130,132,16] 13 (by decide) (choices 1) [1,8,32] r22041 c22041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6614
  · exact u6615
  · exact u6616

def b22042 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 35 322 69 138 176 33 92 156 284), lower := (rows 35 322 69 138 176 33 64 128 256), losses := [] }

theorem u22042 : Upper (D 7) (R 7) [34,320,65,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22043 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 322 69 138 176 36 89 153 281), lower := (rows 35 322 69 138 176 36 64 128 256), losses := [] }

theorem u22043 : Upper (D 7) (R 7) [34,320,65,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22043 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22044 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 69 138 176 40 85 149 277), lower := (rows 35 322 69 138 176 40 64 128 256), losses := [] }

theorem u22044 : Upper (D 7) (R 7) [34,320,65,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22044 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22045 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 69 138 176 48 77 141 269), lower := (rows 35 322 69 138 176 48 64 128 256), losses := [] }

theorem u22045 : Upper (D 7) (R 7) [34,320,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22045 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22046 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,1)], upper := (rows 35 322 69 140 176 33 90 154 282), lower := (rows 35 322 69 140 176 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 37 64 128 256), good := (rows 33 320 101 188 176 33 64 128 256) }] }

theorem u22046 : Upper (D 7) (R 7) [34,320,65,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22047 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 69 140 176 34 89 153 281), lower := (rows 35 322 69 140 176 34 64 128 256), losses := [] }

theorem u22047 : Upper (D 7) (R 7) [34,320,65,132,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22048 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 322 69 140 176 40 83 147 275), lower := (rows 35 322 69 140 176 40 64 128 256), losses := [] }

theorem u22048 : Upper (D 7) (R 7) [34,320,65,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22048 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22049 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 69 140 176 48 75 139 267), lower := (rows 35 322 69 140 176 48 64 128 256), losses := [] }

theorem u22049 : Upper (D 7) (R 7) [34,320,65,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22049 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22050 : Route 9 := (fun mask => (mask,id))

def c22050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22050 : Upper (D 7) (R 7) [34,320,72,129,130,1] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129,130,1] 13 (by decide) (choices 1) [4,16,32] r22050 c22050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6617
  · exact u6618
  · exact u6619

def r22051 : Route 9 := (fun mask => (mask,id))

def c22051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22051 : Upper (D 7) (R 7) [34,320,72,129,130,4] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129,130,4] 13 (by decide) (choices 1) [1,16,32] r22051 c22051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6620
  · exact u6621
  · exact u6622

def b22052 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 322 76 137 146 48 101 165 293), lower := (rows 35 322 76 137 146 48 64 128 256), losses := [] }

theorem u22052 : Upper (D 7) (R 7) [34,320,72,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22052 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22053 : Route 9 := (fun mask => (mask,id))

def c22053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22053 : Upper (D 7) (R 7) [34,320,72,129,132,1] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129,132,1] 13 (by decide) (choices 1) [2,16,32] r22053 c22053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6623
  · exact u6624
  · exact u6625

def b22054 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 76 137 148 34 113 177 305), lower := (rows 35 322 76 137 148 34 64 128 256), losses := [] }

theorem u22054 : Upper (D 7) (R 7) [34,320,72,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22055 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 0, region := 136, targets := 64 }], pairs := [(0,7),(1,7),(3,6)], upper := (rows 35 322 76 137 148 48 99 163 291), lower := (rows 35 322 76 137 148 48 64 128 256), losses := [] }

theorem u22055 : Upper (D 7) (R 7) [34,320,72,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22055 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22056 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 3, region := 48, targets := 66 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 322 76 137 176 33 86 150 278), lower := (rows 35 322 76 137 176 33 64 128 256), losses := [] }

theorem u22056 : Upper (D 7) (R 7) [34,320,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22057 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 76 137 176 34 85 149 277), lower := (rows 35 322 76 137 176 34 64 128 256), losses := [] }

theorem u22057 : Upper (D 7) (R 7) [34,320,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22058 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 322 76 137 176 36 83 147 275), lower := (rows 35 322 76 137 176 36 64 128 256), losses := [] }

theorem u22058 : Upper (D 7) (R 7) [34,320,72,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22058 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22059 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 76 137 176 48 71 135 263), lower := (rows 35 322 76 137 176 48 64 128 256), losses := [] }

theorem u22059 : Upper (D 7) (R 7) [34,320,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22059 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22060 : Route 9 := (fun mask => (mask,id))

def c22060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22060 : Upper (D 7) (R 7) [34,320,72,130,129,1] 13 := by
  apply FastRouting.sound _ _ [34,320,72,130,129,1] 13 (by decide) (choices 1) [4,16,32] r22060 c22060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6626
  · exact u6627
  · exact u6628

def b22061 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(3,6),(4,1),(4,6)], upper := (rows 35 322 76 138 145 36 113 177 305), lower := (rows 35 322 76 138 145 36 64 128 256), losses := [] }

theorem u22061 : Upper (D 7) (R 7) [34,320,72,130,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22061 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22062 : Route 9 := (fun mask => (mask,id))

def c22062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22062 : Upper (D 7) (R 7) [34,320,72,130,129,16] 13 := by
  apply FastRouting.sound _ _ [34,320,72,130,129,16] 13 (by decide) (choices 1) [1,4,32] r22062 c22062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6629
  · exact u6630
  · exact u6631

def b22063 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 76 138 148 33 113 177 305), lower := (rows 35 322 76 138 148 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 47 0 132 260), good := (rows 35 291 445 171 436 33 0 128 256) }] }

theorem u22063 : Upper (D 7) (R 7) [34,320,72,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22064 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 0, region := 136, targets := 64 }], pairs := [(0,7),(1,7),(3,6)], upper := (rows 35 322 76 138 148 48 97 161 289), lower := (rows 35 322 76 138 148 48 64 128 256), losses := [] }

theorem u22064 : Upper (D 7) (R 7) [34,320,72,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22064 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22065 : Route 9 := (fun mask => (mask,id))

def c22065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22065 : Upper (D 7) (R 7) [34,320,72,130,160,1] 13 := by
  apply FastRouting.sound _ _ [34,320,72,130,160,1] 13 (by decide) (choices 1) [1,4,16] r22065 c22065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6632
  · exact u6633
  · exact u6634

def b22066 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 322 76 138 176 36 81 145 273), lower := (rows 35 322 76 138 176 36 64 128 256), losses := [] }

theorem u22066 : Upper (D 7) (R 7) [34,320,72,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22066 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22067 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 76 138 176 48 69 133 261), lower := (rows 35 322 76 138 176 48 64 128 256), losses := [] }

theorem u22067 : Upper (D 7) (R 7) [34,320,72,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22067 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22068 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 40, targets := 66 }], pairs := [(0,6),(0,7),(3,1),(3,6)], upper := (rows 35 322 76 168 145 33 86 150 278), lower := (rows 35 322 76 168 145 33 64 128 256), losses := [] }

theorem u22068 : Upper (D 7) (R 7) [34,320,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22069 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 76 168 145 34 85 149 277), lower := (rows 35 322 76 168 145 34 64 128 256), losses := [] }

theorem u22069 : Upper (D 7) (R 7) [34,320,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22070 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 152, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 35 322 76 168 145 36 83 147 275), lower := (rows 35 322 76 168 145 36 64 128 256), losses := [] }

theorem u22070 : Upper (D 7) (R 7) [34,320,72,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22070 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22071 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 76 168 145 48 71 135 263), lower := (rows 35 322 76 168 145 48 64 128 256), losses := [] }

theorem u22071 : Upper (D 7) (R 7) [34,320,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22071 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22072 : Route 9 := (fun mask => (mask,id))

def c22072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22072 : Upper (D 7) (R 7) [34,320,72,160,130,1] 13 := by
  apply FastRouting.sound _ _ [34,320,72,160,130,1] 13 (by decide) (choices 1) [1,4,16] r22072 c22072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6635
  · exact u6636
  · exact u6637

def b22073 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 152, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 35 322 76 168 146 36 81 145 273), lower := (rows 35 322 76 168 146 36 64 128 256), losses := [] }

theorem u22073 : Upper (D 7) (R 7) [34,320,72,160,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22073 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22074 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 76 168 146 48 69 133 261), lower := (rows 35 322 76 168 146 48 64 128 256), losses := [] }

theorem u22074 : Upper (D 7) (R 7) [34,320,72,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22074 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22075 : Route 9 := (fun mask => (mask,id))

def c22075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22075 : Upper (D 7) (R 7) [34,320,72,160,132,1] 13 := by
  apply FastRouting.sound _ _ [34,320,72,160,132,1] 13 (by decide) (choices 1) [1,2,16] r22075 c22075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6638
  · exact u6639
  · exact u6640

def b22076 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 76 168 148 34 81 145 273), lower := (rows 35 322 76 168 148 34 64 128 256), losses := [] }

theorem u22076 : Upper (D 7) (R 7) [34,320,72,160,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22077 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 76 168 148 48 67 131 259), lower := (rows 35 322 76 168 148 48 64 128 256), losses := [] }

theorem u22077 : Upper (D 7) (R 7) [34,320,72,160,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22077 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22078 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,6)], upper := (rows 35 322 100 137 146 33 92 156 284), lower := (rows 35 322 100 137 146 33 64 128 256), losses := [] }

theorem u22078 : Upper (D 7) (R 7) [34,320,96,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22079 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 322 100 137 146 36 89 153 281), lower := (rows 35 322 100 137 146 36 64 128 256), losses := [] }

theorem u22079 : Upper (D 7) (R 7) [34,320,96,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22079 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22079
end Delivery.IrregularNine14.P07
