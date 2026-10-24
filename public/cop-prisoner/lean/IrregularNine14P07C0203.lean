import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0019

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12180 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 168 400 48 74 202 330), lower := (rows 7 35 69 168 400 48 64 128 256), losses := [] }

theorem u12180 : Upper (D 7) (R 7) [6,33,65,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12180 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12181 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 168 400 96 90 154 282), lower := (rows 7 35 69 168 400 96 64 128 256), losses := [] }

theorem u12181 : Upper (D 7) (R 7) [6,33,65,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12182 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 200 274 40 240 176 432), lower := (rows 7 35 69 200 274 40 64 128 256), losses := [] }

theorem u12182 : Upper (D 7) (R 7) [6,33,65,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12182 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12183 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 200 274 48 232 168 424), lower := (rows 7 35 69 200 274 48 64 128 256), losses := [] }

theorem u12183 : Upper (D 7) (R 7) [6,33,65,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12183 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12184 : Route 9 := (fun mask => (mask,id))

def c12184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12184 : Upper (D 7) (R 7) [6,33,65,192,258,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,258,128] 13 (by decide) (choices 1) [8,16,32] r12184 c12184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1151
  · exact u1152
  · exact u1153

def b12185 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 200 280 34 240 176 432), lower := (rows 7 35 69 200 280 34 64 128 256), losses := [] }

theorem u12185 : Upper (D 7) (R 7) [6,33,65,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12186 : Route 9 := (fun mask => (mask,id))

def c12186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12186 : Upper (D 7) (R 7) [6,33,65,192,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,264,16] 13 (by decide) (choices 1) [2,32,128] r12186 c12186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1154
  · exact u1155
  · exact u1156

def r12187 : Route 9 := (fun mask => (mask,id))

def c12187 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12187 : Upper (D 7) (R 7) [6,33,65,192,264,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,264,128] 13 (by decide) (choices 1) [2,16,32] r12187 c12187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1157
  · exact u1158
  · exact u1159

def b12188 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 200 304 34 216 152 408), lower := (rows 7 35 69 200 304 34 64 128 256), losses := [] }

theorem u12188 : Upper (D 7) (R 7) [6,33,65,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12189 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 200 304 40 210 146 402), lower := (rows 7 35 69 200 304 40 64 128 256), losses := [] }

theorem u12189 : Upper (D 7) (R 7) [6,33,65,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12189 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12190 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 35 69 200 304 48 202 138 394), lower := (rows 7 35 69 200 304 48 64 128 256), losses := [] }

theorem u12190 : Upper (D 7) (R 7) [6,33,65,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12190 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12191 : Route 9 := (fun mask => (mask,id))

def c12191 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12191 : Upper (D 7) (R 7) [6,33,65,192,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,288,128] 13 (by decide) (choices 1) [2,8,16] r12191 c12191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1160
  · exact u1161
  · exact u1162

def b12192 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 200 400 34 120 184 312), lower := (rows 7 35 69 200 400 34 64 128 256), losses := [] }

theorem u12192 : Upper (D 7) (R 7) [6,33,65,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12193 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 200 400 40 114 178 306), lower := (rows 7 35 69 200 400 40 64 128 256), losses := [] }

theorem u12193 : Upper (D 7) (R 7) [6,33,65,192,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12193 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12194 : Route 9 := (fun mask => (mask,id))

def c12194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12194 : Upper (D 7) (R 7) [6,33,65,192,384,16] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,384,16] 13 (by decide) (choices 1) [2,8,32] r12194 c12194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1163
  · exact u1164
  · exact u1165

def b12195 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 25 146 96 480 416 416), lower := (rows 7 35 76 25 146 96 64 128 256), losses := [] }

theorem u12195 : Upper (D 7) (R 7) [6,33,72,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12196 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(2,0),(2,1),(4,0)], upper := (rows 7 35 76 25 146 160 352 480 352), lower := (rows 7 35 76 25 146 160 64 128 256), losses := [{ target := 6, region := (rows 5 10 4 8 16 176 0 128 256), good := (rows 7 35 15 59 178 160 0 160 256) }] }

theorem u12196 : Upper (D 7) (R 7) [6,33,72,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12197 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 0, region := 496, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 76 25 146 288 224 224 480), lower := (rows 7 35 76 25 146 288 64 128 256), losses := [] }

theorem u12197 : Upper (D 7) (R 7) [6,33,72,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12197 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12198 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 25 176 34 448 448 448), lower := (rows 7 35 76 25 176 34 64 128 256), losses := [] }

theorem u12198 : Upper (D 7) (R 7) [6,33,72,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12199 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 25 176 96 450 386 386), lower := (rows 7 35 76 25 176 96 64 128 256), losses := [] }

theorem u12199 : Upper (D 7) (R 7) [6,33,72,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12200 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 25 176 160 322 450 322), lower := (rows 7 35 76 25 176 160 64 128 256), losses := [] }

theorem u12200 : Upper (D 7) (R 7) [6,33,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12201 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 496, targets := 1 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 7 35 76 25 176 288 194 194 450), lower := (rows 7 35 76 25 176 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 299 67 131 259), good := (rows 502 498 124 508 176 288 64 128 288) },{ target := 5, region := (rows 1 2 12 8 16 0 67 131 259), good := (rows 455 451 76 477 144 256 64 128 256) }] }

theorem u12201 : Upper (D 7) (R 7) [6,33,72,17,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12201 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12202 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 25 274 96 224 160 416), lower := (rows 7 35 76 25 274 96 64 128 256), losses := [] }

theorem u12202 : Upper (D 7) (R 7) [6,33,72,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12203 : Route 9 := (fun mask => (mask,id))

def c12203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12203 : Upper (D 7) (R 7) [6,33,72,17,258,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,258,128] 13 (by decide) (choices 1) [32,128] r12203 c12203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1166
  · exact u1167

def b12204 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 25 304 34 192 192 448), lower := (rows 7 35 76 25 304 34 64 128 256), losses := [] }

theorem u12204 : Upper (D 7) (R 7) [6,33,72,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12205 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 25 304 96 194 130 386), lower := (rows 7 35 76 25 304 96 64 128 256), losses := [] }

theorem u12205 : Upper (D 7) (R 7) [6,33,72,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12206 : Route 9 := (fun mask => (mask,id))

def c12206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12206 : Upper (D 7) (R 7) [6,33,72,17,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,288,128] 13 (by decide) (choices 1) [2,128] r12206 c12206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1168
  · exact u1169

def b12207 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 25 400 34 224 224 480), lower := (rows 7 35 76 25 400 34 64 128 256), losses := [] }

theorem u12207 : Upper (D 7) (R 7) [6,33,72,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12208 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 25 400 96 226 162 418), lower := (rows 7 35 76 25 400 96 64 128 256), losses := [] }

theorem u12208 : Upper (D 7) (R 7) [6,33,72,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12209 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 76 25 400 160 98 226 354), lower := (rows 7 35 76 25 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 187 67 131 259), good := (rows 502 498 124 508 432 160 64 160 256) },{ target := 6, region := (rows 5 10 4 8 16 176 0 128 256), good := (rows 7 35 15 59 432 160 0 160 256) }] }

theorem u12209 : Upper (D 7) (R 7) [6,33,72,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12210 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 26 145 96 480 416 416), lower := (rows 7 35 76 26 145 96 64 128 256), losses := [] }

theorem u12210 : Upper (D 7) (R 7) [6,33,72,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12211 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 7 35 76 26 145 160 352 480 352), lower := (rows 7 35 76 26 145 160 64 128 256), losses := [] }

theorem u12211 : Upper (D 7) (R 7) [6,33,72,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12212 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 0, region := 496, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 35 76 26 145 288 224 224 480), lower := (rows 7 35 76 26 145 288 64 128 256), losses := [] }

theorem u12212 : Upper (D 7) (R 7) [6,33,72,18,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12212 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12213 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 26 273 96 224 160 416), lower := (rows 7 35 76 26 273 96 64 128 256), losses := [] }

theorem u12213 : Upper (D 7) (R 7) [6,33,72,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12214 : Route 9 := (fun mask => (mask,id))

def c12214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12214 : Upper (D 7) (R 7) [6,33,72,18,257,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,257,128] 13 (by decide) (choices 1) [32,128] r12214 c12214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1170
  · exact u1171

def b12215 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 26 400 33 224 224 480), lower := (rows 7 35 76 26 400 33 64 128 256), losses := [] }

theorem u12215 : Upper (D 7) (R 7) [6,33,72,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12216 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 26 400 96 225 161 417), lower := (rows 7 35 76 26 400 96 64 128 256), losses := [] }

theorem u12216 : Upper (D 7) (R 7) [6,33,72,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12217 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 496, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 35 76 26 400 160 97 225 353), lower := (rows 7 35 76 26 400 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 187 67 131 259), good := (rows 501 497 124 508 432 160 64 160 256) },{ target := 7, region := (rows 9 2 12 8 16 32 66 0 258), good := (rows 327 355 77 351 272 32 64 0 256) }] }

theorem u12217 : Upper (D 7) (R 7) [6,33,72,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12218 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 56 145 34 448 448 448), lower := (rows 7 35 76 56 145 34 64 128 256), losses := [] }

theorem u12218 : Upper (D 7) (R 7) [6,33,72,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12219 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 56 145 96 450 386 386), lower := (rows 7 35 76 56 145 96 64 128 256), losses := [] }

theorem u12219 : Upper (D 7) (R 7) [6,33,72,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12220 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 76 56 145 160 322 450 322), lower := (rows 7 35 76 56 145 160 64 128 256), losses := [] }

theorem u12220 : Upper (D 7) (R 7) [6,33,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12221 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 35 76 56 145 288 194 194 450), lower := (rows 7 35 76 56 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 307 67 131 259), good := (rows 486 482 76 60 508 288 64 128 288) }] }

theorem u12221 : Upper (D 7) (R 7) [6,33,72,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12221 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12222 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 56 146 33 448 448 448), lower := (rows 7 35 76 56 146 33 64 128 256), losses := [] }

theorem u12222 : Upper (D 7) (R 7) [6,33,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12223 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 56 146 96 449 385 385), lower := (rows 7 35 76 56 146 96 64 128 256), losses := [] }

theorem u12223 : Upper (D 7) (R 7) [6,33,72,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12224 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 76 56 146 160 321 449 321), lower := (rows 7 35 76 56 146 160 64 128 256), losses := [] }

theorem u12224 : Upper (D 7) (R 7) [6,33,72,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12225 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 35 76 56 146 288 193 193 449), lower := (rows 7 35 76 56 146 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 307 67 131 259), good := (rows 485 481 76 60 508 288 64 128 288) }] }

theorem u12225 : Upper (D 7) (R 7) [6,33,72,48,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12225 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12226 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 56 208 33 450 386 386), lower := (rows 7 35 76 56 208 33 64 128 256), losses := [] }

theorem u12226 : Upper (D 7) (R 7) [6,33,72,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12227 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 56 208 34 449 385 385), lower := (rows 7 35 76 56 208 34 64 128 256), losses := [] }

theorem u12227 : Upper (D 7) (R 7) [6,33,72,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12228 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 76 56 208 160 323 387 259), lower := (rows 7 35 76 56 208 160 64 128 256), losses := [] }

theorem u12228 : Upper (D 7) (R 7) [6,33,72,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12229 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(1,6),(4,5)], upper := (rows 7 35 76 56 208 288 195 131 387), lower := (rows 7 35 76 56 208 288 64 128 256), losses := [] }

theorem u12229 : Upper (D 7) (R 7) [6,33,72,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12229 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12230 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 56 273 34 192 192 448), lower := (rows 7 35 76 56 273 34 64 128 256), losses := [] }

theorem u12230 : Upper (D 7) (R 7) [6,33,72,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12231 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 56 273 96 194 130 386), lower := (rows 7 35 76 56 273 96 64 128 256), losses := [] }

theorem u12231 : Upper (D 7) (R 7) [6,33,72,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12232 : Route 9 := (fun mask => (mask,id))

def c12232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12232 : Upper (D 7) (R 7) [6,33,72,48,257,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,257,128] 13 (by decide) (choices 1) [2,128] r12232 c12232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1172
  · exact u1173

def b12233 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 56 274 33 192 192 448), lower := (rows 7 35 76 56 274 33 64 128 256), losses := [] }

theorem u12233 : Upper (D 7) (R 7) [6,33,72,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12234 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 56 274 96 193 129 385), lower := (rows 7 35 76 56 274 96 64 128 256), losses := [] }

theorem u12234 : Upper (D 7) (R 7) [6,33,72,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12235 : Route 9 := (fun mask => (mask,id))

def c12235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12235 : Upper (D 7) (R 7) [6,33,72,48,258,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,258,128] 13 (by decide) (choices 1) [1,128] r12235 c12235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1174
  · exact u1175

def b12236 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 56 336 33 194 130 386), lower := (rows 7 35 76 56 336 33 64 128 256), losses := [] }

theorem u12236 : Upper (D 7) (R 7) [6,33,72,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12237 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 56 336 34 193 129 385), lower := (rows 7 35 76 56 336 34 64 128 256), losses := [] }

theorem u12237 : Upper (D 7) (R 7) [6,33,72,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12238 : Route 9 := (fun mask => (mask,id))

def c12238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12238 : Upper (D 7) (R 7) [6,33,72,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,320,128] 13 (by decide) (choices 1) [1,2,128] r12238 c12238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1176
  · exact u1177
  · exact u1178

def b12239 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 56 400 33 194 194 450), lower := (rows 7 35 76 56 400 33 64 128 256), losses := [] }

theorem u12239 : Upper (D 7) (R 7) [6,33,72,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12239
end Delivery.IrregularNine14.P07
