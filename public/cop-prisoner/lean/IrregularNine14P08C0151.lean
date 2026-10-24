import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0036
import IrregularNine14P08C0037

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9060 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 164 25 25 480 480 480 480), lower := (rows 35 70 164 25 25 32 64 128 256), losses := [] }

theorem u9060 : Upper (D 8) (R 8) [34,68,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9061 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 25 49 488 456 456 456), lower := (rows 35 70 164 25 49 32 64 128 256), losses := [] }

theorem u9061 : Upper (D 8) (R 8) [34,68,160,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9062 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 25 56 481 449 449 449), lower := (rows 35 70 164 25 56 32 64 128 256), losses := [] }

theorem u9062 : Upper (D 8) (R 8) [34,68,160,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9063 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 164 25 81 424 488 424 424), lower := (rows 35 70 164 25 81 32 64 128 256), losses := [] }

theorem u9063 : Upper (D 8) (R 8) [34,68,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9064 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 25 88 417 481 417 417), lower := (rows 35 70 164 25 88 32 64 128 256), losses := [] }

theorem u9064 : Upper (D 8) (R 8) [34,68,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9065 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 25 112 425 457 393 393), lower := (rows 35 70 164 25 112 32 64 128 256), losses := [] }

theorem u9065 : Upper (D 8) (R 8) [34,68,160,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9066 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 164 25 145 360 360 488 360), lower := (rows 35 70 164 25 145 32 64 128 256), losses := [] }

theorem u9066 : Upper (D 8) (R 8) [34,68,160,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9067 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 25 152 353 353 481 353), lower := (rows 35 70 164 25 152 32 64 128 256), losses := [] }

theorem u9067 : Upper (D 8) (R 8) [34,68,160,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9068 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 164 25 176 361 329 457 329), lower := (rows 35 70 164 25 176 32 64 128 256), losses := [] }

theorem u9068 : Upper (D 8) (R 8) [34,68,160,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9069 : PairBound 9 := { available := 297, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 25 208 297 361 425 297), lower := (rows 35 70 164 25 208 32 64 128 256), losses := [] }

theorem u9069 : Upper (D 8) (R 8) [34,68,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9070 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 164 25 273 232 232 232 488), lower := (rows 35 70 164 25 273 32 64 128 256), losses := [] }

theorem u9070 : Upper (D 8) (R 8) [34,68,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9071 : Route 9 := (fun mask => (mask,id))

def c9071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9071 : Upper (D 8) (R 8) [34,68,160,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,264] 13 (by decide) (choices 1) [1,64,128] r9071 c9071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2178
  · exact u2179
  · exact u2180

def r9072 : Route 9 := (fun mask => (mask,id))

def c9072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9072 : Upper (D 8) (R 8) [34,68,160,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,288] 13 (by decide) (choices 1) [1,8,64,128] r9072 c9072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2181
  · exact u2182
  · exact u2183
  · exact u2184

def b9073 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 25 336 169 233 169 425), lower := (rows 35 70 164 25 336 32 64 128 256), losses := [] }

theorem u9073 : Upper (D 8) (R 8) [34,68,160,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9074 : Route 9 := (fun mask => (mask,id))

def c9074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9074 : Upper (D 8) (R 8) [34,68,160,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,384] 13 (by decide) (choices 1) [1,8,64] r9074 c9074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2185
  · exact u2186
  · exact u2187

def b9075 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 41 88 433 465 401 401), lower := (rows 35 70 164 41 88 32 64 128 256), losses := [] }

theorem u9075 : Upper (D 8) (R 8) [34,68,160,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9076 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 41 152 369 337 465 337), lower := (rows 35 70 164 41 152 32 64 128 256), losses := [] }

theorem u9076 : Upper (D 8) (R 8) [34,68,160,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9077 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 41 208 313 345 409 281), lower := (rows 35 70 164 41 208 32 64 128 256), losses := [] }

theorem u9077 : Upper (D 8) (R 8) [34,68,160,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9078 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 41 273 248 216 216 472), lower := (rows 35 70 164 41 273 32 64 128 256), losses := [] }

theorem u9078 : Upper (D 8) (R 8) [34,68,160,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9079 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 41 280 241 209 209 465), lower := (rows 35 70 164 41 280 32 64 128 256), losses := [] }

theorem u9079 : Upper (D 8) (R 8) [34,68,160,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9080 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 41 336 185 217 153 409), lower := (rows 35 70 164 41 336 32 64 128 256), losses := [] }

theorem u9080 : Upper (D 8) (R 8) [34,68,160,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9081 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 41 400 121 89 217 345), lower := (rows 35 70 164 41 400 32 64 128 256), losses := [] }

theorem u9081 : Upper (D 8) (R 8) [34,68,160,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9082 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 56 81 425 457 393 393), lower := (rows 35 70 164 56 81 32 64 128 256), losses := [] }

theorem u9082 : Upper (D 8) (R 8) [34,68,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9083 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 56 88 417 449 385 385), lower := (rows 35 70 164 56 88 32 64 128 256), losses := [] }

theorem u9083 : Upper (D 8) (R 8) [34,68,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9084 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 164 56 145 361 329 457 329), lower := (rows 35 70 164 56 145 32 64 128 256), losses := [] }

theorem u9084 : Upper (D 8) (R 8) [34,68,160,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9085 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 164 56 152 353 321 449 321), lower := (rows 35 70 164 56 152 32 64 128 256), losses := [] }

theorem u9085 : Upper (D 8) (R 8) [34,68,160,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9086 : Route 9 := (fun mask => (mask,id))

def c9086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u9086 : Upper (D 8) (R 8) [34,68,160,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,192] 13 (by decide) (choices 1) [1,8,256] r9086 c9086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2188
  · exact u2189
  · exact u2190

def r9087 : Route 9 := (fun mask => (mask,id))

def c9087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9087 : Upper (D 8) (R 8) [34,68,160,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,257] 13 (by decide) (choices 1) [1,8,64,128] r9087 c9087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2191
  · exact u2192
  · exact u2193
  · exact u2194

def r9088 : Route 9 := (fun mask => (mask,id))

def c9088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9088 : Upper (D 8) (R 8) [34,68,160,48,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,264] 13 (by decide) (choices 1) [1,64,128] r9088 c9088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2195
  · exact u2196
  · exact u2197

def r9089 : Route 9 := (fun mask => (mask,id))

def c9089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9089 : Upper (D 8) (R 8) [34,68,160,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,320] 13 (by decide) (choices 1) [1,8,128] r9089 c9089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2198
  · exact u2199
  · exact u2200

def r9090 : Route 9 := (fun mask => (mask,id))

def c9090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9090 : Upper (D 8) (R 8) [34,68,160,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,384] 13 (by decide) (choices 1) [1,8,64] r9090 c9090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2201
  · exact u2202
  · exact u2203

def b9091 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 73 152 305 369 433 305), lower := (rows 35 70 164 73 152 32 64 128 256), losses := [] }

theorem u9091 : Upper (D 8) (R 8) [34,68,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9092 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 73 273 184 248 184 440), lower := (rows 35 70 164 73 273 32 64 128 256), losses := [] }

theorem u9092 : Upper (D 8) (R 8) [34,68,160,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9093 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 73 280 177 241 177 433), lower := (rows 35 70 164 73 280 32 64 128 256), losses := [] }

theorem u9093 : Upper (D 8) (R 8) [34,68,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9094 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 73 304 185 217 153 409), lower := (rows 35 70 164 73 304 32 64 128 256), losses := [] }

theorem u9094 : Upper (D 8) (R 8) [34,68,160,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9095 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 73 400 57 121 185 313), lower := (rows 35 70 164 73 400 32 64 128 256), losses := [] }

theorem u9095 : Upper (D 8) (R 8) [34,68,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9096 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 164 88 145 297 361 425 297), lower := (rows 35 70 164 88 145 32 64 128 256), losses := [] }

theorem u9096 : Upper (D 8) (R 8) [34,68,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9097 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 152 289 353 417 289), lower := (rows 35 70 164 88 152 32 64 128 256), losses := [] }

theorem u9097 : Upper (D 8) (R 8) [34,68,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9098 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 164 88 176 297 329 393 265), lower := (rows 35 70 164 88 176 32 64 128 256), losses := [] }

theorem u9098 : Upper (D 8) (R 8) [34,68,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9099 : Route 9 := (fun mask => (mask,id))

def c9099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9099 : Upper (D 8) (R 8) [34,68,160,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,257] 13 (by decide) (choices 1) [1,8,128] r9099 c9099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2204
  · exact u2205
  · exact u2206

def b9100 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 280 161 225 161 417), lower := (rows 35 70 164 88 280 32 64 128 256), losses := [] }

theorem u9100 : Upper (D 8) (R 8) [34,68,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9101 : Route 9 := (fun mask => (mask,id))

def c9101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9101 : Upper (D 8) (R 8) [34,68,160,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,288] 13 (by decide) (choices 1) [1,8,128] r9101 c9101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2207
  · exact u2208
  · exact u2209

def r9102 : Route 9 := (fun mask => (mask,id))

def c9102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9102 : Upper (D 8) (R 8) [34,68,160,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,384] 13 (by decide) (choices 1) [1,8] r9102 c9102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2210
  · exact u2211

def b9103 : PairBound 9 := { available := 281, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 164 104 145 313 345 409 281), lower := (rows 35 70 164 104 145 32 64 128 256), losses := [] }

theorem u9103 : Upper (D 8) (R 8) [34,68,160,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9104 : Route 9 := (fun mask => (mask,id))

def c9104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u9104 : Upper (D 8) (R 8) [34,68,160,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,136] 13 (by decide) (choices 1) [1,16,256] r9104 c9104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2212
  · exact u2213
  · exact u2214

def r9105 : Route 9 := (fun mask => (mask,id))

def c9105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9105 : Upper (D 8) (R 8) [34,68,160,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,257] 13 (by decide) (choices 1) [1,8,16,128] r9105 c9105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2215
  · exact u2216
  · exact u2217
  · exact u2218

def r9106 : Route 9 := (fun mask => (mask,id))

def c9106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9106 : Upper (D 8) (R 8) [34,68,160,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,264] 13 (by decide) (choices 1) [1,16,128] r9106 c9106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2219
  · exact u2220
  · exact u2221

def r9107 : Route 9 := (fun mask => (mask,id))

def c9107 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9107 : Upper (D 8) (R 8) [34,68,160,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,384] 13 (by decide) (choices 1) [1,8,16] r9107 c9107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2222
  · exact u2223
  · exact u2224

def b9108 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 164 137 273 120 120 248 376), lower := (rows 35 70 164 137 273 32 64 128 256), losses := [] }

theorem u9108 : Upper (D 8) (R 8) [34,68,160,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9109 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 164 137 280 113 113 241 369), lower := (rows 35 70 164 137 280 32 64 128 256), losses := [] }

theorem u9109 : Upper (D 8) (R 8) [34,68,160,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9110 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 164 137 304 121 89 217 345), lower := (rows 35 70 164 137 304 32 64 128 256), losses := [] }

theorem u9110 : Upper (D 8) (R 8) [34,68,160,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9111 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 164 137 336 57 121 185 313), lower := (rows 35 70 164 137 336 32 64 128 256), losses := [] }

theorem u9111 : Upper (D 8) (R 8) [34,68,160,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9112 : Route 9 := (fun mask => (mask,id))

def c9112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9112 : Upper (D 8) (R 8) [34,68,160,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,257] 13 (by decide) (choices 1) [1,8,64] r9112 c9112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2225
  · exact u2226
  · exact u2227

def b9113 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 152 280 97 97 225 353), lower := (rows 35 70 164 152 280 32 64 128 256), losses := [] }

theorem u9113 : Upper (D 8) (R 8) [34,68,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9114 : Route 9 := (fun mask => (mask,id))

def c9114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9114 : Upper (D 8) (R 8) [34,68,160,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,288] 13 (by decide) (choices 1) [1,8,64] r9114 c9114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2228
  · exact u2229
  · exact u2230

def r9115 : Route 9 := (fun mask => (mask,id))

def c9115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9115 : Upper (D 8) (R 8) [34,68,160,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,320] 13 (by decide) (choices 1) [1,8] r9115 c9115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2231
  · exact u2232

def b9116 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 164 168 273 121 89 217 345), lower := (rows 35 70 164 168 273 32 64 128 256), losses := [] }

theorem u9116 : Upper (D 8) (R 8) [34,68,160,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9117 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 164 168 280 113 81 209 337), lower := (rows 35 70 164 168 280 32 64 128 256), losses := [] }

theorem u9117 : Upper (D 8) (R 8) [34,68,160,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9118 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 164 168 336 57 89 153 281), lower := (rows 35 70 164 168 336 32 64 128 256), losses := [] }

theorem u9118 : Upper (D 8) (R 8) [34,68,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9119 : Route 9 := (fun mask => (mask,id))

def c9119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9119 : Upper (D 8) (R 8) [34,68,160,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257] 13 (by decide) (choices 1) [1,8,16] r9119 c9119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2233
  · exact u2234
  · exact u2235

#print axioms u9119
end Delivery.IrregularNine14.P08
