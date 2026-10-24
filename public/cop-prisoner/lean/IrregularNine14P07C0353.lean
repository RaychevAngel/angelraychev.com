import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0102
import IrregularNine14P07C0103

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21180 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 262 44 73 145 96 210 146 402), lower := (rows 35 262 44 73 145 96 64 128 256), losses := [] }

theorem u21180 : Upper (D 7) (R 7) [34,260,40,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21181 : Route 9 := (fun mask => (mask,id))

def c21181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21181 : Upper (D 7) (R 7) [34,260,40,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,129,128] 13 (by decide) (choices 1) [2,16] r21181 c21181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6168
  · exact u6169

def b21182 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 262 44 73 146 33 208 208 464), lower := (rows 35 262 44 73 146 33 64 128 256), losses := [] }

theorem u21182 : Upper (D 7) (R 7) [34,260,40,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21183 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 262 44 73 146 48 193 193 449), lower := (rows 35 262 44 73 146 48 64 128 256), losses := [] }

theorem u21183 : Upper (D 7) (R 7) [34,260,40,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21183 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21184 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 262 44 73 146 96 209 145 401), lower := (rows 35 262 44 73 146 96 64 128 256), losses := [] }

theorem u21184 : Upper (D 7) (R 7) [34,260,40,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21185 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(3,5),(4,5)], upper := (rows 35 262 44 73 146 160 81 209 337), lower := (rows 35 262 44 73 146 160 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 21 0 73 137 265), good := (rows 475 278 478 473 146 128 64 128 256) }] }

theorem u21185 : Upper (D 7) (R 7) [34,260,40,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21186 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 262 44 73 208 33 210 146 402), lower := (rows 35 262 44 73 208 33 64 128 256), losses := [] }

theorem u21186 : Upper (D 7) (R 7) [34,260,40,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21187 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 44 73 208 34 209 145 401), lower := (rows 35 262 44 73 208 34 64 128 256), losses := [] }

theorem u21187 : Upper (D 7) (R 7) [34,260,40,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21188 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 262 44 73 208 48 195 131 387), lower := (rows 35 262 44 73 208 48 64 128 256), losses := [] }

theorem u21188 : Upper (D 7) (R 7) [34,260,40,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21188 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21189 : Route 9 := (fun mask => (mask,id))

def c21189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21189 : Upper (D 7) (R 7) [34,260,40,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,192,128] 13 (by decide) (choices 1) [1,2,16] r21189 c21189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6170
  · exact u6171
  · exact u6172

def b21190 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 35 262 44 74 81 33 208 144 400), lower := (rows 35 262 44 74 81 33 64 128 256), losses := [] }

theorem u21190 : Upper (D 7) (R 7) [34,260,40,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21191 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 262 44 74 81 48 193 129 385), lower := (rows 35 262 44 74 81 48 64 128 256), losses := [] }

theorem u21191 : Upper (D 7) (R 7) [34,260,40,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21191 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21192 : Route 9 := (fun mask => (mask,id))

def c21192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21192 : Upper (D 7) (R 7) [34,260,40,66,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,40,66,65,128] 13 (by decide) (choices 1) [1,16,128] r21192 c21192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6173
  · exact u6174
  · exact u6175

def b21193 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 262 44 74 145 33 208 208 464), lower := (rows 35 262 44 74 145 33 64 128 256), losses := [] }

theorem u21193 : Upper (D 7) (R 7) [34,260,40,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21194 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 35 262 44 74 145 48 193 193 449), lower := (rows 35 262 44 74 145 48 64 128 256), losses := [] }

theorem u21194 : Upper (D 7) (R 7) [34,260,40,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21194 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21195 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,6),(1,6),(3,5),(4,6)], upper := (rows 35 262 44 74 145 96 209 145 401), lower := (rows 35 262 44 74 145 96 64 128 256), losses := [] }

theorem u21195 : Upper (D 7) (R 7) [34,260,40,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21196 : Route 9 := (fun mask => (mask,id))

def c21196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21196 : Upper (D 7) (R 7) [34,260,40,66,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,40,66,129,128] 13 (by decide) (choices 1) [1,16] r21196 c21196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6176
  · exact u6177

def b21197 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 262 44 74 208 33 209 145 401), lower := (rows 35 262 44 74 208 33 64 128 256), losses := [] }

theorem u21197 : Upper (D 7) (R 7) [34,260,40,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21198 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 262 44 74 208 48 193 129 385), lower := (rows 35 262 44 74 208 48 64 128 256), losses := [] }

theorem u21198 : Upper (D 7) (R 7) [34,260,40,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21198 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21199 : Route 9 := (fun mask => (mask,id))

def c21199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21199 : Upper (D 7) (R 7) [34,260,40,66,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,40,66,192,128] 13 (by decide) (choices 1) [1,16] r21199 c21199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6178
  · exact u6179

def b21200 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 44 88 145 33 194 194 450), lower := (rows 35 262 44 88 145 33 64 128 256), losses := [] }

theorem u21200 : Upper (D 7) (R 7) [34,260,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21201 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 44 88 145 34 193 193 449), lower := (rows 35 262 44 88 145 34 64 128 256), losses := [] }

theorem u21201 : Upper (D 7) (R 7) [34,260,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21202 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 262 44 88 145 96 195 131 387), lower := (rows 35 262 44 88 145 96 64 128 256), losses := [] }

theorem u21202 : Upper (D 7) (R 7) [34,260,40,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21203 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 262 44 88 145 160 67 195 323), lower := (rows 35 262 44 88 145 160 64 128 256), losses := [] }

theorem u21203 : Upper (D 7) (R 7) [34,260,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21204 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 44 88 146 33 193 193 449), lower := (rows 35 262 44 88 146 33 64 128 256), losses := [] }

theorem u21204 : Upper (D 7) (R 7) [34,260,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21205 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 262 44 88 146 96 193 129 385), lower := (rows 35 262 44 88 146 96 64 128 256), losses := [] }

theorem u21205 : Upper (D 7) (R 7) [34,260,40,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21206 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 262 44 88 146 160 65 193 321), lower := (rows 35 262 44 88 146 160 64 128 256), losses := [] }

theorem u21206 : Upper (D 7) (R 7) [34,260,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21207 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 44 200 81 33 210 146 402), lower := (rows 35 262 44 200 81 33 64 128 256), losses := [] }

theorem u21207 : Upper (D 7) (R 7) [34,260,40,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21208 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 44 200 81 34 209 145 401), lower := (rows 35 262 44 200 81 34 64 128 256), losses := [] }

theorem u21208 : Upper (D 7) (R 7) [34,260,40,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21209 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 262 44 200 81 48 195 131 387), lower := (rows 35 262 44 200 81 48 64 128 256), losses := [] }

theorem u21209 : Upper (D 7) (R 7) [34,260,40,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21209 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21210 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 262 44 200 81 160 83 147 275), lower := (rows 35 262 44 200 81 160 64 128 256), losses := [] }

theorem u21210 : Upper (D 7) (R 7) [34,260,40,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21211 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 44 200 82 33 209 145 401), lower := (rows 35 262 44 200 82 33 64 128 256), losses := [] }

theorem u21211 : Upper (D 7) (R 7) [34,260,40,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21212 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 262 44 200 82 48 193 129 385), lower := (rows 35 262 44 200 82 48 64 128 256), losses := [] }

theorem u21212 : Upper (D 7) (R 7) [34,260,40,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21212 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21213 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 262 44 200 82 160 81 145 273), lower := (rows 35 262 44 200 82 160 64 128 256), losses := [] }

theorem u21213 : Upper (D 7) (R 7) [34,260,40,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21214 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 262 69 25 82 40 224 160 416), lower := (rows 35 262 69 25 82 40 64 128 256), losses := [] }

theorem u21214 : Upper (D 7) (R 7) [34,260,65,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21214 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21215 : Route 9 := (fun mask => (mask,id))

def c21215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21215 : Upper (D 7) (R 7) [34,260,65,17,66,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,66,128] 13 (by decide) (choices 1) [8,32,128] r21215 c21215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6180
  · exact u6181
  · exact u6182

def b21216 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 25 112 34 200 136 392), lower := (rows 35 262 69 25 112 34 64 128 256), losses := [] }

theorem u21216 : Upper (D 7) (R 7) [34,260,65,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21217 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 56, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 262 69 25 112 40 194 130 386), lower := (rows 35 262 69 25 112 40 64 128 256), losses := [] }

theorem u21217 : Upper (D 7) (R 7) [34,260,65,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21217 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21218 : Route 9 := (fun mask => (mask,id))

def c21218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21218 : Upper (D 7) (R 7) [34,260,65,17,96,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,96,128] 13 (by decide) (choices 1) [2,8,128] r21218 c21218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6183
  · exact u6184
  · exact u6185

def b21219 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 262 69 25 146 40 224 224 480), lower := (rows 35 262 69 25 146 40 64 128 256), losses := [] }

theorem u21219 : Upper (D 7) (R 7) [34,260,65,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21219 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21220 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 3, region := 228, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,6)], upper := (rows 35 262 69 25 146 96 232 168 424), lower := (rows 35 262 69 25 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 13 21 32 0 129 257), good := (rows 443 286 415 409 146 32 0 128 256) }] }

theorem u21220 : Upper (D 7) (R 7) [34,260,65,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21221 : Route 9 := (fun mask => (mask,id))

def c21221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21221 : Upper (D 7) (R 7) [34,260,65,17,130,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,130,128] 13 (by decide) (choices 1) [8,32] r21221 c21221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6186
  · exact u6187

def b21222 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 25 152 34 224 224 480), lower := (rows 35 262 69 25 152 34 64 128 256), losses := [] }

theorem u21222 : Upper (D 7) (R 7) [34,260,65,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21223 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 35 262 69 25 152 96 226 162 418), lower := (rows 35 262 69 25 152 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 111 71 135 263), good := (rows 482 486 486 504 184 96 96 128 256) }] }

theorem u21223 : Upper (D 7) (R 7) [34,260,65,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21224 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 418, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 35 262 69 25 152 160 98 226 354), lower := (rows 35 262 69 25 152 160 64 128 256), losses := [] }

theorem u21224 : Upper (D 7) (R 7) [34,260,65,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21225 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 25 176 34 200 200 456), lower := (rows 35 262 69 25 176 34 64 128 256), losses := [] }

theorem u21225 : Upper (D 7) (R 7) [34,260,65,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21226 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 208, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 35 262 69 25 176 40 194 194 450), lower := (rows 35 262 69 25 176 40 64 128 256), losses := [] }

theorem u21226 : Upper (D 7) (R 7) [34,260,65,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21226 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21227 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(4,6)], upper := (rows 35 262 69 25 176 96 202 138 394), lower := (rows 35 262 69 25 176 96 64 128 256), losses := [] }

theorem u21227 : Upper (D 7) (R 7) [34,260,65,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21228 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 69 25 176 160 74 202 330), lower := (rows 35 262 69 25 176 160 64 128 256), losses := [] }

theorem u21228 : Upper (D 7) (R 7) [34,260,65,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21229 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 25 208 34 232 168 424), lower := (rows 35 262 69 25 208 34 64 128 256), losses := [] }

theorem u21229 : Upper (D 7) (R 7) [34,260,65,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21230 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 208, targets := 1 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 35 262 69 25 208 40 226 162 418), lower := (rows 35 262 69 25 208 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 29 40 65 129 257), good := (rows 498 278 470 504 208 56 64 128 256) },{ target := 6, region := (rows 1 6 4 8 16 40 0 129 257), good := (rows 419 262 391 441 144 40 0 128 256) }] }

theorem u21230 : Upper (D 7) (R 7) [34,260,65,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21230 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21231 : Route 9 := (fun mask => (mask,id))

def c21231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21231 : Upper (D 7) (R 7) [34,260,65,17,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,192,128] 13 (by decide) (choices 1) [2,8,32] r21231 c21231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6188
  · exact u6189
  · exact u6190

def b21232 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 35 262 69 26 88 33 224 160 416), lower := (rows 35 262 69 26 88 33 64 128 256), losses := [] }

theorem u21232 : Upper (D 7) (R 7) [34,260,65,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21233 : Route 9 := (fun mask => (mask,id))

def c21233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21233 : Upper (D 7) (R 7) [34,260,65,18,72,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,72,128] 13 (by decide) (choices 1) [1,32,128] r21233 c21233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6191
  · exact u6192
  · exact u6193

def b21234 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 26 112 33 200 136 392), lower := (rows 35 262 69 26 112 33 64 128 256), losses := [] }

theorem u21234 : Upper (D 7) (R 7) [34,260,65,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21235 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 262 69 26 112 40 193 129 385), lower := (rows 35 262 69 26 112 40 64 128 256), losses := [] }

theorem u21235 : Upper (D 7) (R 7) [34,260,65,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21235 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21236 : Route 9 := (fun mask => (mask,id))

def c21236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21236 : Upper (D 7) (R 7) [34,260,65,18,96,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,96,128] 13 (by decide) (choices 1) [1,8,128] r21236 c21236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6194
  · exact u6195
  · exact u6196

def b21237 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 262 69 26 145 40 224 224 480), lower := (rows 35 262 69 26 145 40 64 128 256), losses := [] }

theorem u21237 : Upper (D 7) (R 7) [34,260,65,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21237 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21238 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 35 262 69 26 145 96 232 168 424), lower := (rows 35 262 69 26 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 15 21 32 0 129 257), good := (rows 443 286 415 26 409 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 101 27 17 96 96 0 256) }] }

theorem u21238 : Upper (D 7) (R 7) [34,260,65,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21239 : Route 9 := (fun mask => (mask,id))

def c21239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21239 : Upper (D 7) (R 7) [34,260,65,18,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,129,128] 13 (by decide) (choices 1) [8,32] r21239 c21239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6197
  · exact u6198

#print axioms u21239
end Delivery.IrregularNine14.P07
