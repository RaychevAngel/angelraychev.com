import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0118
import IrregularNine14P07C0119

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22980 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 69 168 400 33 82 146 274), lower := (rows 37 74 69 168 400 33 64 128 256), losses := [] }

theorem u22980 : Upper (D 7) (R 7) [36,72,65,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22981 : Route 9 := (fun mask => (mask,id))

def c22981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22981 : Upper (D 7) (R 7) [36,72,65,160,384,2] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,384,2] 13 (by decide) (choices 1) [1,2,16] r22981 c22981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7137
  · exact u7138
  · exact u7139

def b22982 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 69 168 400 48 67 131 259), lower := (rows 37 74 69 168 400 48 64 128 256), losses := [] }

theorem u22982 : Upper (D 7) (R 7) [36,72,65,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22982 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22983 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 69 265 50 34 208 144 400), lower := (rows 37 74 69 265 50 34 64 128 256), losses := [] }

theorem u22983 : Upper (D 7) (R 7) [36,72,65,257,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22984 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 265 50 48 194 130 386), lower := (rows 37 74 69 265 50 48 64 128 256), losses := [] }

theorem u22984 : Upper (D 7) (R 7) [36,72,65,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22984 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22985 : Route 9 := (fun mask => (mask,id))

def c22985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22985 : Upper (D 7) (R 7) [36,72,65,257,34,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,257,34,128] 13 (by decide) (choices 1) [2,16,128] r22985 c22985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7140
  · exact u7141
  · exact u7142

def b22986 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 69 265 146 34 240 176 432), lower := (rows 37 74 69 265 146 34 64 128 256), losses := [] }

theorem u22986 : Upper (D 7) (R 7) [36,72,65,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22987 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 176, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 74 69 265 146 48 226 162 418), lower := (rows 37 74 69 265 146 48 64 128 256), losses := [] }

theorem u22987 : Upper (D 7) (R 7) [36,72,65,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22987 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22988 : Route 9 := (fun mask => (mask,id))

def c22988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22988 : Upper (D 7) (R 7) [36,72,65,257,130,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,257,130,128] 13 (by decide) (choices 1) [2,16,32] r22988 c22988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7143
  · exact u7144
  · exact u7145

def b22989 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 69 265 176 34 210 146 402), lower := (rows 37 74 69 265 176 34 64 128 256), losses := [] }

theorem u22989 : Upper (D 7) (R 7) [36,72,65,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22990 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 265 176 48 194 130 386), lower := (rows 37 74 69 265 176 48 64 128 256), losses := [] }

theorem u22990 : Upper (D 7) (R 7) [36,72,65,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22990 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22991 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 69 265 176 160 82 146 274), lower := (rows 37 74 69 265 176 160 64 128 256), losses := [] }

theorem u22991 : Upper (D 7) (R 7) [36,72,65,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22992 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 266 50 33 208 144 400), lower := (rows 37 74 69 266 50 33 64 128 256), losses := [] }

theorem u22992 : Upper (D 7) (R 7) [36,72,65,258,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22993 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 266 50 48 193 129 385), lower := (rows 37 74 69 266 50 48 64 128 256), losses := [] }

theorem u22993 : Upper (D 7) (R 7) [36,72,65,258,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22993 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22994 : Route 9 := (fun mask => (mask,id))

def c22994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22994 : Upper (D 7) (R 7) [36,72,65,258,34,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,34,128] 13 (by decide) (choices 1) [1,16,128] r22994 c22994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7146
  · exact u7147
  · exact u7148

def b22995 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 74 69 266 145 34 240 176 432), lower := (rows 37 74 69 266 145 34 64 128 256), losses := [] }

theorem u22995 : Upper (D 7) (R 7) [36,72,65,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22996 : Route 9 := (fun mask => (mask,id))

def c22996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22996 : Upper (D 7) (R 7) [36,72,65,258,129,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,129,16] 13 (by decide) (choices 1) [2,32,128] r22996 c22996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7149
  · exact u7150
  · exact u7151

def r22997 : Route 9 := (fun mask => (mask,id))

def c22997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22997 : Upper (D 7) (R 7) [36,72,65,258,129,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,129,128] 13 (by decide) (choices 1) [2,16,32] r22997 c22997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7152
  · exact u7153
  · exact u7154

def b22998 : PairBound 9 := { available := 176, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 266 146 33 240 176 432), lower := (rows 37 74 69 266 146 33 64 128 256), losses := [] }

theorem u22998 : Upper (D 7) (R 7) [36,72,65,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22999 : Route 9 := (fun mask => (mask,id))

def c22999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22999 : Upper (D 7) (R 7) [36,72,65,258,130,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,130,16] 13 (by decide) (choices 1) [1,32,128] r22999 c22999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7155
  · exact u7156
  · exact u7157

def r23000 : Route 9 := (fun mask => (mask,id))

def c23000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23000 : Upper (D 7) (R 7) [36,72,65,258,130,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,130,128] 13 (by decide) (choices 1) [1,16,32] r23000 c23000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7158
  · exact u7159
  · exact u7160

def b23001 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 266 176 33 210 146 402), lower := (rows 37 74 69 266 176 33 64 128 256), losses := [] }

theorem u23001 : Upper (D 7) (R 7) [36,72,65,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23002 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 37 74 69 266 176 34 209 145 401), lower := (rows 37 74 69 266 176 34 64 128 256), losses := [] }

theorem u23002 : Upper (D 7) (R 7) [36,72,65,258,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23003 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 266 176 48 195 131 387), lower := (rows 37 74 69 266 176 48 64 128 256), losses := [] }

theorem u23003 : Upper (D 7) (R 7) [36,72,65,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23003 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23004 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 69 266 176 160 83 147 275), lower := (rows 37 74 69 266 176 160 64 128 256), losses := [] }

theorem u23004 : Upper (D 7) (R 7) [36,72,65,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23005 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 69 280 19 34 224 160 416), lower := (rows 37 74 69 280 19 34 64 128 256), losses := [] }

theorem u23005 : Upper (D 7) (R 7) [36,72,65,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23006 : Route 9 := (fun mask => (mask,id))

def c23006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23006 : Upper (D 7) (R 7) [36,72,65,272,3,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,3,128] 13 (by decide) (choices 1) [2,32,128] r23006 c23006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7161
  · exact u7162
  · exact u7163

def b23007 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 280 50 33 194 130 386), lower := (rows 37 74 69 280 50 33 64 128 256), losses := [] }

theorem u23007 : Upper (D 7) (R 7) [36,72,65,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23008 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 69 280 50 34 193 129 385), lower := (rows 37 74 69 280 50 34 64 128 256), losses := [] }

theorem u23008 : Upper (D 7) (R 7) [36,72,65,272,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23009 : Route 9 := (fun mask => (mask,id))

def c23009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23009 : Upper (D 7) (R 7) [36,72,65,272,34,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,34,128] 13 (by decide) (choices 1) [1,2,128] r23009 c23009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7164
  · exact u7165
  · exact u7166

def b23010 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 280 145 34 226 162 418), lower := (rows 37 74 69 280 145 34 64 128 256), losses := [] }

theorem u23010 : Upper (D 7) (R 7) [36,72,65,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23011 : Route 9 := (fun mask => (mask,id))

def c23011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23011 : Upper (D 7) (R 7) [36,72,65,272,129,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,129,128] 13 (by decide) (choices 1) [2,32] r23011 c23011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7167
  · exact u7168

def b23012 : PairBound 9 := { available := 162, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 280 146 33 226 162 418), lower := (rows 37 74 69 280 146 33 64 128 256), losses := [] }

theorem u23012 : Upper (D 7) (R 7) [36,72,65,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23013 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 280 146 34 225 161 417), lower := (rows 37 74 69 280 146 34 64 128 256), losses := [] }

theorem u23013 : Upper (D 7) (R 7) [36,72,65,272,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23014 : Route 9 := (fun mask => (mask,id))

def c23014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23014 : Upper (D 7) (R 7) [36,72,65,272,130,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,130,128] 13 (by decide) (choices 1) [1,2,32] r23014 c23014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7169
  · exact u7170
  · exact u7171

def b23015 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 280 176 33 194 130 386), lower := (rows 37 74 69 280 176 33 64 128 256), losses := [] }

theorem u23015 : Upper (D 7) (R 7) [36,72,65,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23016 : Route 9 := (fun mask => (mask,id))

def c23016 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23016 : Upper (D 7) (R 7) [36,72,65,272,160,2] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,160,2] 13 (by decide) (choices 1) [1,2,128] r23016 c23016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7172
  · exact u7173
  · exact u7174

def b23017 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 69 280 176 160 67 131 259), lower := (rows 37 74 69 280 176 160 64 128 256), losses := [] }

theorem u23017 : Upper (D 7) (R 7) [36,72,65,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23018 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 296 145 34 210 146 402), lower := (rows 37 74 69 296 145 34 64 128 256), losses := [] }

theorem u23018 : Upper (D 7) (R 7) [36,72,65,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23019 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 69 296 145 48 194 130 386), lower := (rows 37 74 69 296 145 48 64 128 256), losses := [] }

theorem u23019 : Upper (D 7) (R 7) [36,72,65,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23019 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23020 : Route 9 := (fun mask => (mask,id))

def c23020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23020 : Upper (D 7) (R 7) [36,72,65,288,129,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,288,129,128] 13 (by decide) (choices 1) [2,16] r23020 c23020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7175
  · exact u7176

def b23021 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 69 296 146 33 210 146 402), lower := (rows 37 74 69 296 146 33 64 128 256), losses := [] }

theorem u23021 : Upper (D 7) (R 7) [36,72,65,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23022 : Route 9 := (fun mask => (mask,id))

def c23022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23022 : Upper (D 7) (R 7) [36,72,65,288,130,2] 13 := by
  apply FastRouting.sound _ _ [36,72,65,288,130,2] 13 (by decide) (choices 1) [1,16,128] r23022 c23022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7177
  · exact u7178
  · exact u7179

def r23023 : Route 9 := (fun mask => (mask,id))

def c23023 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23023 : Upper (D 7) (R 7) [36,72,65,288,130,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,288,130,16] 13 (by decide) (choices 1) [1,2,128] r23023 c23023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7180
  · exact u7181
  · exact u7182

def r23024 : Route 9 := (fun mask => (mask,id))

def c23024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23024 : Upper (D 7) (R 7) [36,72,65,288,130,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,288,130,128] 13 (by decide) (choices 1) [1,2,16] r23024 c23024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7183
  · exact u7184
  · exact u7185

def b23025 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 69 392 19 34 240 176 432), lower := (rows 37 74 69 392 19 34 64 128 256), losses := [] }

theorem u23025 : Upper (D 7) (R 7) [36,72,65,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23026 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 69 392 19 48 226 162 418), lower := (rows 37 74 69 392 19 48 64 128 256), losses := [] }

theorem u23026 : Upper (D 7) (R 7) [36,72,65,384,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23026 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23027 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(1,0),(3,0),(3,6)], upper := (rows 37 74 69 392 19 160 114 178 306), lower := (rows 37 74 69 392 19 160 64 128 256), losses := [{ target := 1, region := (rows 3 0 6 8 16 168 64 128 256), good := (rows 37 109 69 424 21 160 64 160 256) }] }

theorem u23027 : Upper (D 7) (R 7) [36,72,65,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23028 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 392 50 33 210 146 402), lower := (rows 37 74 69 392 50 33 64 128 256), losses := [] }

theorem u23028 : Upper (D 7) (R 7) [36,72,65,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23029 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 69 392 50 34 209 145 401), lower := (rows 37 74 69 392 50 34 64 128 256), losses := [] }

theorem u23029 : Upper (D 7) (R 7) [36,72,65,384,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23030 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 392 50 48 195 131 387), lower := (rows 37 74 69 392 50 48 64 128 256), losses := [] }

theorem u23030 : Upper (D 7) (R 7) [36,72,65,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23030 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23031 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,0)], upper := (rows 37 74 69 392 50 160 83 147 275), lower := (rows 37 74 69 392 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 36 122 68 424 50 160 64 160 256) },{ target := 1, region := (rows 19 0 6 8 16 168 64 128 256), good := (rows 37 109 69 424 53 160 64 160 256) }] }

theorem u23031 : Upper (D 7) (R 7) [36,72,65,384,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23032 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 392 145 34 114 178 306), lower := (rows 37 74 69 392 145 34 64 128 256), losses := [] }

theorem u23032 : Upper (D 7) (R 7) [36,72,65,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23033 : Route 9 := (fun mask => (mask,id))

def c23033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23033 : Upper (D 7) (R 7) [36,72,65,384,129,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,129,16] 13 (by decide) (choices 1) [2,32] r23033 c23033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7186
  · exact u7187

def b23034 : PairBound 9 := { available := 50, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 392 146 33 114 178 306), lower := (rows 37 74 69 392 146 33 64 128 256), losses := [] }

theorem u23034 : Upper (D 7) (R 7) [36,72,65,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23035 : Route 9 := (fun mask => (mask,id))

def c23035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23035 : Upper (D 7) (R 7) [36,72,65,384,130,2] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,130,2] 13 (by decide) (choices 1) [1,16,32] r23035 c23035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7188
  · exact u7189
  · exact u7190

def r23036 : Route 9 := (fun mask => (mask,id))

def c23036 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23036 : Upper (D 7) (R 7) [36,72,65,384,130,16] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,130,16] 13 (by decide) (choices 1) [1,2,32] r23036 c23036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7191
  · exact u7192
  · exact u7193

def b23037 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 69 392 176 33 82 146 274), lower := (rows 37 74 69 392 176 33 64 128 256), losses := [] }

theorem u23037 : Upper (D 7) (R 7) [36,72,65,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23038 : Route 9 := (fun mask => (mask,id))

def c23038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23038 : Upper (D 7) (R 7) [36,72,65,384,160,2] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,160,2] 13 (by decide) (choices 1) [1,2,16] r23038 c23038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7194
  · exact u7195
  · exact u7196

def b23039 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 392 176 48 67 131 259), lower := (rows 37 74 69 392 176 48 64 128 256), losses := [] }

theorem u23039 : Upper (D 7) (R 7) [36,72,65,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23039 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23039
end Delivery.IrregularNine14.P07
