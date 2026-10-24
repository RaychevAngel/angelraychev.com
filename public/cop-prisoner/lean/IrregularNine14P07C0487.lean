import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0185

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29220 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 25 176 96 75 139 267), lower := (rows 97 262 134 25 176 96 64 128 256), losses := [] }

theorem u29220 : Upper (D 7) (R 7) [96,260,130,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29221 : Route 9 := (fun mask => (mask,id))

def c29221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29221 : Upper (D 7) (R 7) [96,260,130,18,129,1] 13 := by
  apply FastRouting.sound _ _ [96,260,130,18,129,1] 13 (by decide) (choices 1) [8,32] r29221 c29221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11133
  · exact u11134

def b29222 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 3, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 262 134 26 145 40 97 225 353), lower := (rows 97 262 134 26 145 40 64 128 256), losses := [] }

theorem u29222 : Upper (D 7) (R 7) [96,260,130,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29222 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29223 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 26 145 96 105 169 297), lower := (rows 97 262 134 26 145 96 64 128 256), losses := [] }

theorem u29223 : Upper (D 7) (R 7) [96,260,130,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29224 : Route 9 := (fun mask => (mask,id))

def c29224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29224 : Upper (D 7) (R 7) [96,260,130,18,160,1] 13 := by
  apply FastRouting.sound _ _ [96,260,130,18,160,1] 13 (by decide) (choices 1) [1,8] r29224 c29224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11135
  · exact u11136

def b29225 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 262 134 26 176 40 65 193 321), lower := (rows 97 262 134 26 176 40 64 128 256), losses := [] }

theorem u29225 : Upper (D 7) (R 7) [96,260,130,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29225 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29226 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 26 176 96 73 137 265), lower := (rows 97 262 134 26 176 96 64 128 256), losses := [] }

theorem u29226 : Upper (D 7) (R 7) [96,260,130,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29227 : Route 9 := (fun mask => (mask,id))

def c29227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29227 : Upper (D 7) (R 7) [96,260,130,34,72,1] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,72,1] 13 (by decide) (choices 1) [1,16,128] r29227 c29227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11137
  · exact u11138
  · exact u11139

def b29228 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 134 42 88 48 193 129 385), lower := (rows 97 262 134 42 88 48 64 128 256), losses := [] }

theorem u29228 : Upper (D 7) (R 7) [96,260,130,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29228 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29229 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 40, targets := 65 },{ cop := 3, region := 81, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(4,1)], upper := (rows 97 262 134 42 88 160 81 145 273), lower := (rows 97 262 134 42 88 160 64 128 256), losses := [] }

theorem u29229 : Upper (D 7) (R 7) [96,260,130,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29230 : Route 9 := (fun mask => (mask,id))

def c29230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29230 : Upper (D 7) (R 7) [96,260,130,34,129,1] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,129,1] 13 (by decide) (choices 1) [8,16] r29230 c29230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11140
  · exact u11141

def b29231 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 134 42 145 40 81 209 337), lower := (rows 97 262 134 42 145 40 64 128 256), losses := [] }

theorem u29231 : Upper (D 7) (R 7) [96,260,130,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29231 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29232 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 209, targets := 2 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 262 134 42 145 48 73 201 329), lower := (rows 97 262 134 42 145 48 64 128 256), losses := [] }

theorem u29232 : Upper (D 7) (R 7) [96,260,130,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29232 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29233 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 42 145 96 89 153 281), lower := (rows 97 262 134 42 145 96 64 128 256), losses := [] }

theorem u29233 : Upper (D 7) (R 7) [96,260,130,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29234 : Route 9 := (fun mask => (mask,id))

def c29234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29234 : Upper (D 7) (R 7) [96,260,130,34,136,1] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,136,1] 13 (by decide) (choices 1) [1,16] r29234 c29234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11142
  · exact u11143

def b29235 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 262 134 42 152 48 65 193 321), lower := (rows 97 262 134 42 152 48 64 128 256), losses := [] }

theorem u29235 : Upper (D 7) (R 7) [96,260,130,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29235 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29236 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 42 152 96 81 145 273), lower := (rows 97 262 134 42 152 96 64 128 256), losses := [] }

theorem u29236 : Upper (D 7) (R 7) [96,260,130,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29237 : Route 9 := (fun mask => (mask,id))

def c29237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29237 : Upper (D 7) (R 7) [96,260,130,34,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,192,1] 13 (by decide) (choices 1) [1,8,16] r29237 c29237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11144
  · exact u11145
  · exact u11146

def b29238 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 134 42 208 40 81 145 273), lower := (rows 97 262 134 42 208 40 64 128 256), losses := [] }

theorem u29238 : Upper (D 7) (R 7) [96,260,130,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29238 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29239 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 134 42 208 48 73 137 265), lower := (rows 97 262 134 42 208 48 64 128 256), losses := [] }

theorem u29239 : Upper (D 7) (R 7) [96,260,130,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29239 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29240 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 262 134 56 145 33 74 202 330), lower := (rows 97 262 134 56 145 33 64 128 256), losses := [] }

theorem u29240 : Upper (D 7) (R 7) [96,260,130,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29241 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 262 134 56 145 34 73 201 329), lower := (rows 97 262 134 56 145 34 64 128 256), losses := [] }

theorem u29241 : Upper (D 7) (R 7) [96,260,130,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29242 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 262 134 56 145 40 67 195 323), lower := (rows 97 262 134 56 145 40 64 128 256), losses := [] }

theorem u29242 : Upper (D 7) (R 7) [96,260,130,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29242 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29243 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 56 145 96 75 139 267), lower := (rows 97 262 134 56 145 96 64 128 256), losses := [] }

theorem u29243 : Upper (D 7) (R 7) [96,260,130,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29244 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 134 56 208 33 75 139 267), lower := (rows 97 262 134 56 208 33 64 128 256), losses := [] }

theorem u29244 : Upper (D 7) (R 7) [96,260,130,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29245 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 262 134 56 208 34 73 137 265), lower := (rows 97 262 134 56 208 34 64 128 256), losses := [] }

theorem u29245 : Upper (D 7) (R 7) [96,260,130,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29246 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 134 56 208 40 67 131 259), lower := (rows 97 262 134 56 208 40 64 128 256), losses := [] }

theorem u29246 : Upper (D 7) (R 7) [96,260,130,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29246 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29247 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 48, targets := 192 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,6),(4,7)], upper := (rows 97 262 140 11 50 33 208 208 464), lower := (rows 97 262 140 11 50 33 64 128 256), losses := [] }

theorem u29247 : Upper (D 7) (R 7) [96,260,136,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29248 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 140 11 50 48 193 193 449), lower := (rows 97 262 140 11 50 48 64 128 256), losses := [] }

theorem u29248 : Upper (D 7) (R 7) [96,260,136,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29248 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29249 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 11 50 96 209 145 401), lower := (rows 97 262 140 11 50 96 64 128 256), losses := [] }

theorem u29249 : Upper (D 7) (R 7) [96,260,136,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29250 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 73, targets := 128 },{ cop := 4, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,0)], upper := (rows 97 262 140 11 50 160 81 209 337), lower := (rows 97 262 140 11 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 64 128 256), good := (rows 96 310 172 26 50 160 64 160 256) }] }

theorem u29250 : Upper (D 7) (R 7) [96,260,136,3,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29251 : Route 9 := (fun mask => (mask,id))

def c29251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29251 : Upper (D 7) (R 7) [96,260,136,3,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,136,3,129,2] 13 (by decide) (choices 1) [16,32] r29251 c29251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11147
  · exact u11148

theorem m29252_2 : Upper (D 7) (R 7) [96,260,136,3,129,16,2] 13 :=
  permutation_upper _ _ _ [96,260,136,3,129,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11147

def r29252 : Route 9 := (fun mask => (mask,id))

def c29252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29252 : Upper (D 7) (R 7) [96,260,136,3,129,16] 13 := by
  apply FastRouting.sound _ _ [96,260,136,3,129,16] 13 (by decide) (choices 1) [2,32] r29252 c29252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29252_2
  · exact u11149

def b29253 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 11 145 96 114 178 306), lower := (rows 97 262 140 11 145 96 64 128 256), losses := [] }

theorem u29253 : Upper (D 7) (R 7) [96,260,136,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29254 : Route 9 := (fun mask => (mask,id))

def c29254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29254 : Upper (D 7) (R 7) [96,260,136,3,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,136,3,130,1] 13 (by decide) (choices 1) [16,32] r29254 c29254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11150
  · exact u11151

def b29255 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 4, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(3,7)], upper := (rows 97 262 140 11 146 48 97 225 353), lower := (rows 97 262 140 11 146 48 64 128 256), losses := [] }

theorem u29255 : Upper (D 7) (R 7) [96,260,136,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29255 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29256 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 11 146 96 113 177 305), lower := (rows 97 262 140 11 146 96 64 128 256), losses := [] }

theorem u29256 : Upper (D 7) (R 7) [96,260,136,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29257 : PairBound 9 := { available := 82, camps := [{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,6)], upper := (rows 97 262 140 11 176 33 82 210 338), lower := (rows 97 262 140 11 176 33 64 128 256), losses := [{ target := 1, region := (rows 65 0 4 8 20 105 64 128 256), good := (rows 97 276 188 41 176 33 97 128 256) },{ target := 6, region := (rows 1 2 4 8 20 41 0 128 256), good := (rows 33 278 188 43 176 33 0 128 256) }] }

theorem u29257 : Upper (D 7) (R 7) [96,260,136,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29258 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,0),(4,1)], upper := (rows 97 262 140 11 176 34 81 209 337), lower := (rows 97 262 140 11 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 42 64 128 256), good := (rows 96 310 188 42 176 34 64 128 256) }] }

theorem u29258 : Upper (D 7) (R 7) [96,260,136,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29259 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 140 11 176 48 67 195 323), lower := (rows 97 262 140 11 176 48 64 128 256), losses := [] }

theorem u29259 : Upper (D 7) (R 7) [96,260,136,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29259 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29260 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 11 176 96 83 147 275), lower := (rows 97 262 140 11 176 96 64 128 256), losses := [] }

theorem u29260 : Upper (D 7) (R 7) [96,260,136,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29261 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 262 140 25 50 33 194 194 450), lower := (rows 97 262 140 25 50 33 64 128 256), losses := [] }

theorem u29261 : Upper (D 7) (R 7) [96,260,136,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29262 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 97 262 140 25 50 34 193 193 449), lower := (rows 97 262 140 25 50 34 64 128 256), losses := [] }

theorem u29262 : Upper (D 7) (R 7) [96,260,136,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29263 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 25 50 96 195 131 387), lower := (rows 97 262 140 25 50 96 64 128 256), losses := [] }

theorem u29263 : Upper (D 7) (R 7) [96,260,136,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29264 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 73, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,7)], upper := (rows 97 262 140 25 50 160 67 195 323), lower := (rows 97 262 140 25 50 160 64 128 256), losses := [] }

theorem u29264 : Upper (D 7) (R 7) [96,260,136,17,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29265 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 105, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 97 262 140 25 146 33 98 226 354), lower := (rows 97 262 140 25 146 33 64 128 256), losses := [] }

theorem u29265 : Upper (D 7) (R 7) [96,260,136,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29266 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 105, targets := 128 },{ cop := 5, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 97 262 140 25 146 34 97 225 353), lower := (rows 97 262 140 25 146 34 64 128 256), losses := [] }

theorem u29266 : Upper (D 7) (R 7) [96,260,136,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29267 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 25 146 96 99 163 291), lower := (rows 97 262 140 25 146 96 64 128 256), losses := [] }

theorem u29267 : Upper (D 7) (R 7) [96,260,136,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29268 : Route 9 := (fun mask => (mask,id))

def c29268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29268 : Upper (D 7) (R 7) [96,260,136,18,129,1] 13 := by
  apply FastRouting.sound _ _ [96,260,136,18,129,1] 13 (by decide) (choices 1) [2,32] r29268 c29268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11152
  · exact u11153

def b29269 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 262 140 26 145 34 97 225 353), lower := (rows 97 262 140 26 145 34 64 128 256), losses := [] }

theorem u29269 : Upper (D 7) (R 7) [96,260,136,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29270 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 26 145 96 99 163 291), lower := (rows 97 262 140 26 145 96 64 128 256), losses := [] }

theorem u29270 : Upper (D 7) (R 7) [96,260,136,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29271 : Route 9 := (fun mask => (mask,id))

def c29271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29271 : Upper (D 7) (R 7) [96,260,136,18,160,1] 13 := by
  apply FastRouting.sound _ _ [96,260,136,18,160,1] 13 (by decide) (choices 1) [1,2] r29271 c29271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11154
  · exact u11155

def b29272 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 262 140 26 176 34 65 193 321), lower := (rows 97 262 140 26 176 34 64 128 256), losses := [] }

theorem u29272 : Upper (D 7) (R 7) [96,260,136,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29273 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 26 176 96 67 131 259), lower := (rows 97 262 140 26 176 96 64 128 256), losses := [] }

theorem u29273 : Upper (D 7) (R 7) [96,260,136,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29274 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 40, targets := 192 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,6),(3,7)], upper := (rows 97 262 140 42 19 33 208 208 464), lower := (rows 97 262 140 42 19 33 64 128 256), losses := [] }

theorem u29274 : Upper (D 7) (R 7) [96,260,136,34,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29275 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 262 140 42 19 48 193 193 449), lower := (rows 97 262 140 42 19 48 64 128 256), losses := [] }

theorem u29275 : Upper (D 7) (R 7) [96,260,136,34,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29275 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29276 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 140 42 19 96 209 145 401), lower := (rows 97 262 140 42 19 96 64 128 256), losses := [] }

theorem u29276 : Upper (D 7) (R 7) [96,260,136,34,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29277 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 81, targets := 128 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(3,0),(4,7)], upper := (rows 97 262 140 42 19 160 81 209 337), lower := (rows 97 262 140 42 19 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 96 302 172 42 26 160 64 160 256) }] }

theorem u29277 : Upper (D 7) (R 7) [96,260,136,34,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29278 : Route 9 := (fun mask => (mask,id))

def c29278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29278 : Upper (D 7) (R 7) [96,260,136,34,66,1] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,66,1] 13 (by decide) (choices 1) [1,16,128] r29278 c29278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11156
  · exact u11157
  · exact u11158

def b29279 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 140 42 82 48 193 129 385), lower := (rows 97 262 140 42 82 48 64 128 256), losses := [] }

theorem u29279 : Upper (D 7) (R 7) [96,260,136,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29279 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29279
end Delivery.IrregularNine14.P07
