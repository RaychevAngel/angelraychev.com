import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0037

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9120 : Route 9 := (fun mask => (mask,id))

def c9120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9120 : Upper (D 8) (R 8) [34,68,160,192,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,264] 13 (by decide) (choices 1) [1,16] r9120 c9120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2236
  · exact u2237

def r9121 : Route 9 := (fun mask => (mask,id))

def c9121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9121 : Upper (D 8) (R 8) [34,68,160,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,288] 13 (by decide) (choices 1) [1,8,16] r9121 c9121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2238
  · exact u2239
  · exact u2240

def b9122 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 25 56 224 224 224 480), lower := (rows 35 70 261 25 56 32 64 128 256), losses := [] }

theorem u9122 : Upper (D 8) (R 8) [34,68,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9123 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 25 88 160 224 160 416), lower := (rows 35 70 261 25 88 32 64 128 256), losses := [] }

theorem u9123 : Upper (D 8) (R 8) [34,68,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9124 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 25 112 168 232 168 424), lower := (rows 35 70 261 25 112 32 64 128 256), losses := [] }

theorem u9124 : Upper (D 8) (R 8) [34,68,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9125 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 261 25 152 224 224 224 480), lower := (rows 35 70 261 25 152 32 64 128 256), losses := [] }

theorem u9125 : Upper (D 8) (R 8) [34,68,257,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9126 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 25 176 232 232 232 488), lower := (rows 35 70 261 25 176 32 64 128 256), losses := [] }

theorem u9126 : Upper (D 8) (R 8) [34,68,257,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9127 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 25 208 168 232 168 424), lower := (rows 35 70 261 25 208 32 64 128 256), losses := [] }

theorem u9127 : Upper (D 8) (R 8) [34,68,257,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9128 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 41 56 240 208 208 464), lower := (rows 35 70 261 41 56 32 64 128 256), losses := [] }

theorem u9128 : Upper (D 8) (R 8) [34,68,257,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9129 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 41 88 176 240 176 432), lower := (rows 35 70 261 41 88 32 64 128 256), losses := [] }

theorem u9129 : Upper (D 8) (R 8) [34,68,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9130 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 41 112 184 216 152 408), lower := (rows 35 70 261 41 112 32 64 128 256), losses := [] }

theorem u9130 : Upper (D 8) (R 8) [34,68,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9131 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 41 152 240 240 240 496), lower := (rows 35 70 261 41 152 32 64 128 256), losses := [] }

theorem u9131 : Upper (D 8) (R 8) [34,68,257,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9132 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 41 176 248 216 216 472), lower := (rows 35 70 261 41 176 32 64 128 256), losses := [] }

theorem u9132 : Upper (D 8) (R 8) [34,68,257,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9133 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 41 208 184 248 184 440), lower := (rows 35 70 261 41 208 32 64 128 256), losses := [] }

theorem u9133 : Upper (D 8) (R 8) [34,68,257,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9134 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 56 56 225 193 193 449), lower := (rows 35 70 261 56 56 32 64 128 256), losses := [] }

theorem u9134 : Upper (D 8) (R 8) [34,68,257,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9135 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 56 81 168 232 168 424), lower := (rows 35 70 261 56 81 32 64 128 256), losses := [] }

theorem u9135 : Upper (D 8) (R 8) [34,68,257,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9136 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 56 88 161 225 161 417), lower := (rows 35 70 261 56 88 32 64 128 256), losses := [] }

theorem u9136 : Upper (D 8) (R 8) [34,68,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9137 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 56 112 169 201 137 393), lower := (rows 35 70 261 56 112 32 64 128 256), losses := [] }

theorem u9137 : Upper (D 8) (R 8) [34,68,257,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9138 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 56 145 232 232 232 488), lower := (rows 35 70 261 56 145 32 64 128 256), losses := [] }

theorem u9138 : Upper (D 8) (R 8) [34,68,257,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9139 : Route 9 := (fun mask => (mask,id))

def c9139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9139 : Upper (D 8) (R 8) [34,68,257,48,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,136] 13 (by decide) (choices 1) [1,64,128] r9139 c9139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2241
  · exact u2242
  · exact u2243

def b9140 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 56 176 233 201 201 457), lower := (rows 35 70 261 56 176 32 64 128 256), losses := [] }

theorem u9140 : Upper (D 8) (R 8) [34,68,257,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9141 : Route 9 := (fun mask => (mask,id))

def c9141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9141 : Upper (D 8) (R 8) [34,68,257,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,192] 13 (by decide) (choices 1) [1,8,128] r9141 c9141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2244
  · exact u2245
  · exact u2246

def b9142 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 73 152 176 240 176 432), lower := (rows 35 70 261 73 152 32 64 128 256), losses := [] }

theorem u9142 : Upper (D 8) (R 8) [34,68,257,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9143 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 73 176 184 248 184 440), lower := (rows 35 70 261 73 176 32 64 128 256), losses := [] }

theorem u9143 : Upper (D 8) (R 8) [34,68,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9144 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 88 145 168 232 168 424), lower := (rows 35 70 261 88 145 32 64 128 256), losses := [] }

theorem u9144 : Upper (D 8) (R 8) [34,68,257,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9145 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 88 152 161 225 161 417), lower := (rows 35 70 261 88 152 32 64 128 256), losses := [] }

theorem u9145 : Upper (D 8) (R 8) [34,68,257,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9146 : Route 9 := (fun mask => (mask,id))

def c9146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9146 : Upper (D 8) (R 8) [34,68,257,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,160] 13 (by decide) (choices 1) [1,8,128] r9146 c9146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2247
  · exact u2248
  · exact u2249

def b9147 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 104 145 184 248 184 440), lower := (rows 35 70 261 104 145 32 64 128 256), losses := [] }

theorem u9147 : Upper (D 8) (R 8) [34,68,257,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9148 : Route 9 := (fun mask => (mask,id))

def c9148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9148 : Upper (D 8) (R 8) [34,68,257,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,136] 13 (by decide) (choices 1) [1,16,128] r9148 c9148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2250
  · exact u2251
  · exact u2252

def r9149 : Route 9 := (fun mask => (mask,id))

def c9149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9149 : Upper (D 8) (R 8) [34,68,257,96,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,160] 13 (by decide) (choices 1) [1,8,16,128] r9149 c9149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2253
  · exact u2254
  · exact u2255
  · exact u2256

def b9150 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 137 152 112 112 240 368), lower := (rows 35 70 261 137 152 32 64 128 256), losses := [] }

theorem u9150 : Upper (D 8) (R 8) [34,68,257,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9151 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 137 176 120 120 248 376), lower := (rows 35 70 261 137 176 32 64 128 256), losses := [] }

theorem u9151 : Upper (D 8) (R 8) [34,68,257,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9152 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 137 208 56 120 184 312), lower := (rows 35 70 261 137 208 32 64 128 256), losses := [] }

theorem u9152 : Upper (D 8) (R 8) [34,68,257,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9153 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 152 152 97 97 225 353), lower := (rows 35 70 261 152 152 32 64 128 256), losses := [] }

theorem u9153 : Upper (D 8) (R 8) [34,68,257,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9154 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 152 176 105 105 233 361), lower := (rows 35 70 261 152 176 32 64 128 256), losses := [] }

theorem u9154 : Upper (D 8) (R 8) [34,68,257,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9155 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 152 208 41 105 169 297), lower := (rows 35 70 261 152 208 32 64 128 256), losses := [] }

theorem u9155 : Upper (D 8) (R 8) [34,68,257,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9156 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 168 176 121 89 217 345), lower := (rows 35 70 261 168 176 32 64 128 256), losses := [] }

theorem u9156 : Upper (D 8) (R 8) [34,68,257,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9157 : Route 9 := (fun mask => (mask,id))

def c9157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9157 : Upper (D 8) (R 8) [34,68,257,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,160,192] 13 (by decide) (choices 1) [1,8,16] r9157 c9157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2257
  · exact u2258
  · exact u2259

def b9158 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 268 25 49 224 224 224 480), lower := (rows 35 70 268 25 49 32 64 128 256), losses := [] }

theorem u9158 : Upper (D 8) (R 8) [34,68,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9159 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 268 25 81 160 224 160 416), lower := (rows 35 70 268 25 81 32 64 128 256), losses := [] }

theorem u9159 : Upper (D 8) (R 8) [34,68,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9160 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 25 112 161 225 161 417), lower := (rows 35 70 268 25 112 32 64 128 256), losses := [] }

theorem u9160 : Upper (D 8) (R 8) [34,68,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9161 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 268 25 145 224 224 224 480), lower := (rows 35 70 268 25 145 32 64 128 256), losses := [] }

theorem u9161 : Upper (D 8) (R 8) [34,68,264,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9162 : Route 9 := (fun mask => (mask,id))

def c9162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9162 : Upper (D 8) (R 8) [34,68,264,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,17,160] 13 (by decide) (choices 1) [1,64,128] r9162 c9162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2260
  · exact u2261
  · exact u2262

def b9163 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 25 208 161 225 161 417), lower := (rows 35 70 268 25 208 32 64 128 256), losses := [] }

theorem u9163 : Upper (D 8) (R 8) [34,68,264,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9164 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 268 56 49 225 193 193 449), lower := (rows 35 70 268 56 49 32 64 128 256), losses := [] }

theorem u9164 : Upper (D 8) (R 8) [34,68,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9165 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 56 81 161 225 161 417), lower := (rows 35 70 268 56 81 32 64 128 256), losses := [] }

theorem u9165 : Upper (D 8) (R 8) [34,68,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9166 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 268 56 112 161 193 129 385), lower := (rows 35 70 268 56 112 32 64 128 256), losses := [] }

theorem u9166 : Upper (D 8) (R 8) [34,68,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9167 : Route 9 := (fun mask => (mask,id))

def c9167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9167 : Upper (D 8) (R 8) [34,68,264,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,48,129] 13 (by decide) (choices 1) [1,64,128] r9167 c9167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2263
  · exact u2264
  · exact u2265

def b9168 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 268 56 176 225 193 193 449), lower := (rows 35 70 268 56 176 32 64 128 256), losses := [] }

theorem u9168 : Upper (D 8) (R 8) [34,68,264,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9169 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 56 208 161 225 161 417), lower := (rows 35 70 268 56 208 32 64 128 256), losses := [] }

theorem u9169 : Upper (D 8) (R 8) [34,68,264,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9170 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 268 137 49 240 240 240 496), lower := (rows 35 70 268 137 49 32 64 128 256), losses := [] }

theorem u9170 : Upper (D 8) (R 8) [34,68,264,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9171 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 137 81 176 240 176 432), lower := (rows 35 70 268 137 81 32 64 128 256), losses := [] }

theorem u9171 : Upper (D 8) (R 8) [34,68,264,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9172 : Route 9 := (fun mask => (mask,id))

def c9172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9172 : Upper (D 8) (R 8) [34,68,264,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,96] 13 (by decide) (choices 1) [1,16,128] r9172 c9172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2266
  · exact u2267
  · exact u2268

def b9173 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 268 137 145 112 112 240 368), lower := (rows 35 70 268 137 145 32 64 128 256), losses := [] }

theorem u9173 : Upper (D 8) (R 8) [34,68,264,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9174 : Route 9 := (fun mask => (mask,id))

def c9174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9174 : Upper (D 8) (R 8) [34,68,264,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,160] 13 (by decide) (choices 1) [1,16,64] r9174 c9174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2269
  · exact u2270
  · exact u2271

def r9175 : Route 9 := (fun mask => (mask,id))

def c9175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9175 : Upper (D 8) (R 8) [34,68,264,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,192] 13 (by decide) (choices 1) [1,16] r9175 c9175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2272
  · exact u2273

def b9176 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 268 152 49 225 225 225 481), lower := (rows 35 70 268 152 49 32 64 128 256), losses := [] }

theorem u9176 : Upper (D 8) (R 8) [34,68,264,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9177 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 152 81 161 225 161 417), lower := (rows 35 70 268 152 81 32 64 128 256), losses := [] }

theorem u9177 : Upper (D 8) (R 8) [34,68,264,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9178 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 152 112 161 225 161 417), lower := (rows 35 70 268 152 112 32 64 128 256), losses := [] }

theorem u9178 : Upper (D 8) (R 8) [34,68,264,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9179 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 152 145 97 97 225 353), lower := (rows 35 70 268 152 145 32 64 128 256), losses := [] }

theorem u9179 : Upper (D 8) (R 8) [34,68,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9179
end Delivery.IrregularNine14.P08
