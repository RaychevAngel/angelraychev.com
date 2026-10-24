import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0101
import IrregularNine14P07C0102

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r21060 : Route 9 := (fun mask => (mask,id))

def c21060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21060 : Upper (D 7) (R 7) [34,260,9,66,96,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,96,128] 13 (by decide) (choices 1) [1,16,128] r21060 c21060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6106
  · exact u6107
  · exact u6108

def b21061 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 200, targets := 1 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(3,0),(4,1)], upper := (rows 35 262 13 74 145 48 224 224 480), lower := (rows 35 262 13 74 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 13 16 48 113 177 305), good := (rows 490 270 462 74 504 496 64 128 256) }] }

theorem u21061 : Upper (D 7) (R 7) [34,260,9,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21061 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21062 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 128 },{ cop := 0, region := 144, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 35 262 13 74 145 96 240 176 432), lower := (rows 35 262 13 74 145 96 64 128 256), losses := [] }

theorem u21062 : Upper (D 7) (R 7) [34,260,9,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21063 : Route 9 := (fun mask => (mask,id))

def c21063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21063 : Upper (D 7) (R 7) [34,260,9,66,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,129,128] 13 (by decide) (choices 1) [16,32] r21063 c21063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6109
  · exact u6110

def b21064 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 262 13 74 176 33 208 208 464), lower := (rows 35 262 13 74 176 33 64 128 256), losses := [] }

theorem u21064 : Upper (D 7) (R 7) [34,260,9,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21065 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 13 74 176 48 193 193 449), lower := (rows 35 262 13 74 176 48 64 128 256), losses := [] }

theorem u21065 : Upper (D 7) (R 7) [34,260,9,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21065 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21066 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 128 },{ cop := 0, region := 144, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 35 262 13 74 176 96 209 145 401), lower := (rows 35 262 13 74 176 96 64 128 256), losses := [] }

theorem u21066 : Upper (D 7) (R 7) [34,260,9,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21067 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 13 74 176 160 81 209 337), lower := (rows 35 262 13 74 176 160 64 128 256), losses := [] }

theorem u21067 : Upper (D 7) (R 7) [34,260,9,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21068 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 262 13 74 208 33 240 176 432), lower := (rows 35 262 13 74 208 33 64 128 256), losses := [] }

theorem u21068 : Upper (D 7) (R 7) [34,260,9,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21069 : Route 9 := (fun mask => (mask,id))

def c21069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21069 : Upper (D 7) (R 7) [34,260,9,66,192,16] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,192,16] 13 (by decide) (choices 1) [1,32,128] r21069 c21069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6111
  · exact u6112
  · exact u6113

def r21070 : Route 9 := (fun mask => (mask,id))

def c21070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21070 : Upper (D 7) (R 7) [34,260,9,66,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,192,128] 13 (by decide) (choices 1) [1,16,32] r21070 c21070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6114
  · exact u6115
  · exact u6116

def b21071 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 13 88 145 34 224 224 480), lower := (rows 35 262 13 88 145 34 64 128 256), losses := [] }

theorem u21071 : Upper (D 7) (R 7) [34,260,9,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21072 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 144, targets := 64 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 35 262 13 88 145 96 226 162 418), lower := (rows 35 262 13 88 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 127 71 135 263), good := (rows 482 486 494 120 504 96 96 128 256) },{ target := 6, region := (rows 1 6 4 8 21 32 0 129 257), good := (rows 435 278 415 24 401 32 0 128 256) }] }

theorem u21072 : Upper (D 7) (R 7) [34,260,9,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21073 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 35 262 13 88 145 160 98 226 354), lower := (rows 35 262 13 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 183 71 135 263), good := (rows 482 486 494 120 504 160 64 160 256) },{ target := 7, region := (rows 1 22 20 24 16 32 65 0 257), good := (rows 355 262 335 94 351 32 64 0 256) }] }

theorem u21073 : Upper (D 7) (R 7) [34,260,9,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21074 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 13 88 146 33 224 224 480), lower := (rows 35 262 13 88 146 33 64 128 256), losses := [] }

theorem u21074 : Upper (D 7) (R 7) [34,260,9,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21075 : Route 9 := (fun mask => (mask,id))

def c21075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21075 : Upper (D 7) (R 7) [34,260,9,80,130,64] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80,130,64] 13 (by decide) (choices 1) [1,32,128] r21075 c21075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6117
  · exact u6118
  · exact u6119

def r21076 : Route 9 := (fun mask => (mask,id))

def c21076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21076 : Upper (D 7) (R 7) [34,260,9,80,130,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80,130,128] 13 (by decide) (choices 1) [1,32] r21076 c21076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6120
  · exact u6121

def b21077 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 13 88 176 33 194 194 450), lower := (rows 35 262 13 88 176 33 64 128 256), losses := [] }

theorem u21077 : Upper (D 7) (R 7) [34,260,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21078 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 13 88 176 34 193 193 449), lower := (rows 35 262 13 88 176 34 64 128 256), losses := [] }

theorem u21078 : Upper (D 7) (R 7) [34,260,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21079 : Route 9 := (fun mask => (mask,id))

def c21079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21079 : Upper (D 7) (R 7) [34,260,9,80,160,64] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80,160,64] 13 (by decide) (choices 1) [1,2,128] r21079 c21079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6122
  · exact u6123
  · exact u6124

def b21080 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 13 88 176 160 67 195 323), lower := (rows 35 262 13 88 176 160 64 128 256), losses := [] }

theorem u21080 : Upper (D 7) (R 7) [34,260,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21081 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 13 104 81 34 208 144 400), lower := (rows 35 262 13 104 81 34 64 128 256), losses := [] }

theorem u21081 : Upper (D 7) (R 7) [34,260,9,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21082 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 44, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 262 13 104 81 48 194 130 386), lower := (rows 35 262 13 104 81 48 64 128 256), losses := [] }

theorem u21082 : Upper (D 7) (R 7) [34,260,9,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21082 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21083 : Route 9 := (fun mask => (mask,id))

def c21083 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21083 : Upper (D 7) (R 7) [34,260,9,96,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,65,128] 13 (by decide) (choices 1) [2,16,128] r21083 c21083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6125
  · exact u6126
  · exact u6127

def b21084 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 262 13 104 82 33 208 144 400), lower := (rows 35 262 13 104 82 33 64 128 256), losses := [] }

theorem u21084 : Upper (D 7) (R 7) [34,260,9,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21085 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 262 13 104 82 48 193 129 385), lower := (rows 35 262 13 104 82 48 64 128 256), losses := [] }

theorem u21085 : Upper (D 7) (R 7) [34,260,9,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21085 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21086 : Route 9 := (fun mask => (mask,id))

def c21086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21086 : Upper (D 7) (R 7) [34,260,9,96,66,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,66,128] 13 (by decide) (choices 1) [1,16,128] r21086 c21086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6128
  · exact u6129
  · exact u6130

def b21087 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 13 104 145 34 208 208 464), lower := (rows 35 262 13 104 145 34 64 128 256), losses := [] }

theorem u21087 : Upper (D 7) (R 7) [34,260,9,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21088 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 262 13 104 145 48 194 194 450), lower := (rows 35 262 13 104 145 48 64 128 256), losses := [] }

theorem u21088 : Upper (D 7) (R 7) [34,260,9,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21088 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21089 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 35 262 13 104 145 96 210 146 402), lower := (rows 35 262 13 104 145 96 64 128 256), losses := [] }

theorem u21089 : Upper (D 7) (R 7) [34,260,9,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21090 : Route 9 := (fun mask => (mask,id))

def c21090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21090 : Upper (D 7) (R 7) [34,260,9,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,129,128] 13 (by decide) (choices 1) [2,16] r21090 c21090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6131
  · exact u6132

def b21091 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 262 13 104 146 33 208 208 464), lower := (rows 35 262 13 104 146 33 64 128 256), losses := [] }

theorem u21091 : Upper (D 7) (R 7) [34,260,9,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21092 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 262 13 104 146 48 193 193 449), lower := (rows 35 262 13 104 146 48 64 128 256), losses := [] }

theorem u21092 : Upper (D 7) (R 7) [34,260,9,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21092 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21093 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 35 262 13 104 146 96 209 145 401), lower := (rows 35 262 13 104 146 96 64 128 256), losses := [] }

theorem u21093 : Upper (D 7) (R 7) [34,260,9,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21094 : Route 9 := (fun mask => (mask,id))

def c21094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21094 : Upper (D 7) (R 7) [34,260,9,96,130,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,130,128] 13 (by decide) (choices 1) [1,16] r21094 c21094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6133
  · exact u6134

def b21095 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 262 13 104 208 33 210 146 402), lower := (rows 35 262 13 104 208 33 64 128 256), losses := [] }

theorem u21095 : Upper (D 7) (R 7) [34,260,9,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21096 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 13 104 208 34 209 145 401), lower := (rows 35 262 13 104 208 34 64 128 256), losses := [] }

theorem u21096 : Upper (D 7) (R 7) [34,260,9,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21097 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 262 13 104 208 48 195 131 387), lower := (rows 35 262 13 104 208 48 64 128 256), losses := [] }

theorem u21097 : Upper (D 7) (R 7) [34,260,9,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21097 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21098 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 3 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 35 262 13 104 208 160 83 147 275), lower := (rows 35 262 13 104 208 160 64 128 256), losses := [] }

theorem u21098 : Upper (D 7) (R 7) [34,260,9,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21099 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 13 200 81 34 240 176 432), lower := (rows 35 262 13 200 81 34 64 128 256), losses := [] }

theorem u21099 : Upper (D 7) (R 7) [34,260,9,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21100 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 35 262 13 200 81 48 226 162 418), lower := (rows 35 262 13 200 81 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 29 16 48 65 129 257), good := (rows 490 270 462 200 504 56 64 128 256) },{ target := 6, region := (rows 1 6 4 8 16 48 0 129 257), good := (rows 419 262 399 136 433 48 0 128 256) }] }

theorem u21100 : Upper (D 7) (R 7) [34,260,9,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21100 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21101 : Route 9 := (fun mask => (mask,id))

def c21101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21101 : Upper (D 7) (R 7) [34,260,9,192,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192,65,128] 13 (by decide) (choices 1) [2,16,32] r21101 c21101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6135
  · exact u6136
  · exact u6137

def b21102 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 13 200 82 33 240 176 432), lower := (rows 35 262 13 200 82 33 64 128 256), losses := [] }

theorem u21102 : Upper (D 7) (R 7) [34,260,9,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21103 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 262 13 200 82 48 225 161 417), lower := (rows 35 262 13 200 82 48 64 128 256), losses := [] }

theorem u21103 : Upper (D 7) (R 7) [34,260,9,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21103 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21104 : Route 9 := (fun mask => (mask,id))

def c21104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21104 : Upper (D 7) (R 7) [34,260,9,192,66,128] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192,66,128] 13 (by decide) (choices 1) [1,16,32] r21104 c21104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6138
  · exact u6139
  · exact u6140

def b21105 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 13 200 112 33 210 146 402), lower := (rows 35 262 13 200 112 33 64 128 256), losses := [] }

theorem u21105 : Upper (D 7) (R 7) [34,260,9,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21106 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 13 200 112 34 209 145 401), lower := (rows 35 262 13 200 112 34 64 128 256), losses := [] }

theorem u21106 : Upper (D 7) (R 7) [34,260,9,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21107 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 13 200 112 48 195 131 387), lower := (rows 35 262 13 200 112 48 64 128 256), losses := [] }

theorem u21107 : Upper (D 7) (R 7) [34,260,9,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21107 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21108 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 0, region := 80, targets := 128 }], pairs := [(1,7),(4,0),(4,1),(4,7)], upper := (rows 35 262 13 200 112 160 83 147 275), lower := (rows 35 262 13 200 112 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 17 32 69 0 261), good := (rows 371 326 351 72 112 32 64 0 256) }] }

theorem u21108 : Upper (D 7) (R 7) [34,260,9,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21109 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 25 208 33 224 224 480), lower := (rows 35 262 14 25 208 33 64 128 256), losses := [] }

theorem u21109 : Upper (D 7) (R 7) [34,260,10,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21110 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 }], pairs := [(1,6),(2,6),(3,1),(4,1)], upper := (rows 35 262 14 25 208 96 225 161 417), lower := (rows 35 262 14 25 208 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 32 0 129 257), good := (rows 419 262 14 415 144 32 0 128 256) }] }

theorem u21110 : Upper (D 7) (R 7) [34,260,10,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21111 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 56 208 33 193 193 449), lower := (rows 35 262 14 56 208 33 64 128 256), losses := [] }

theorem u21111 : Upper (D 7) (R 7) [34,260,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21112 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 35 262 14 56 208 96 193 129 385), lower := (rows 35 262 14 56 208 96 64 128 256), losses := [] }

theorem u21112 : Upper (D 7) (R 7) [34,260,10,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21113 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 73 112 33 208 144 400), lower := (rows 35 262 14 73 112 33 64 128 256), losses := [] }

theorem u21113 : Upper (D 7) (R 7) [34,260,10,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21114 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 14 73 112 48 193 129 385), lower := (rows 35 262 14 73 112 48 64 128 256), losses := [] }

theorem u21114 : Upper (D 7) (R 7) [34,260,10,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21114 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21115 : Route 9 := (fun mask => (mask,id))

def c21115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21115 : Upper (D 7) (R 7) [34,260,10,65,96,128] 13 := by
  apply FastRouting.sound _ _ [34,260,10,65,96,128] 13 (by decide) (choices 1) [1,16,128] r21115 c21115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6141
  · exact u6142
  · exact u6143

def b21116 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 2 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 35 262 14 73 145 48 224 224 480), lower := (rows 35 262 14 73 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 113 177 305), good := (rows 482 262 14 462 496 496 64 128 256) }] }

theorem u21116 : Upper (D 7) (R 7) [34,260,10,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21116 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21117 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,6),(3,1),(4,1),(4,6)], upper := (rows 35 262 14 73 145 96 240 176 432), lower := (rows 35 262 14 73 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 25 32 0 129 257), good := (rows 435 262 30 415 401 32 0 128 256) }] }

theorem u21117 : Upper (D 7) (R 7) [34,260,10,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21118 : Route 9 := (fun mask => (mask,id))

def c21118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21118 : Upper (D 7) (R 7) [34,260,10,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,10,65,129,128] 13 (by decide) (choices 1) [16,32] r21118 c21118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6144
  · exact u6145

def b21119 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 73 176 33 208 208 464), lower := (rows 35 262 14 73 176 33 64 128 256), losses := [] }

theorem u21119 : Upper (D 7) (R 7) [34,260,10,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21119
end Delivery.IrregularNine14.P07
