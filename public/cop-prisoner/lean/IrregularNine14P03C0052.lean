import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0017

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3120 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 208 293 325 389 261), lower := (rows 35 67 28 168 208 32 64 128 256), losses := [] }

theorem u3120 : Upper (D 3) (R 3) [34,65,24,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3120
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3121 : Route 9 := (fun mask => (mask,id))

def c3121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3121 : Upper (D 3) (R 3) [34,65,24,160,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,257] 13 (by decide) (choices 1) [1,4,64,128] r3121 c3121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1022
  · exact u1023
  · exact u1024
  · exact u1025

def b3122 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 168 276 225 193 193 449), lower := (rows 35 67 28 168 276 32 64 128 256), losses := [] }

theorem u3122 : Upper (D 3) (R 3) [34,65,24,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3122
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3123 : Route 9 := (fun mask => (mask,id))

def c3123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3123 : Upper (D 3) (R 3) [34,65,24,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,320] 13 (by decide) (choices 1) [1,4,128] r3123 c3123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1026
  · exact u1027
  · exact u1028

def b3124 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 400 101 69 197 325), lower := (rows 35 67 28 168 400 32 64 128 256), losses := [] }

theorem u3124 : Upper (D 3) (R 3) [34,65,24,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3124
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3125 : Route 9 := (fun mask => (mask,id))

def c3125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3125 : Upper (D 3) (R 3) [34,65,24,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,257] 13 (by decide) (choices 1) [1,4,128] r3125 c3125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1029
  · exact u1030
  · exact u1031

def b3126 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 200 276 161 225 161 417), lower := (rows 35 67 28 200 276 32 64 128 256), losses := [] }

theorem u3126 : Upper (D 3) (R 3) [34,65,24,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3126
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3127 : Route 9 := (fun mask => (mask,id))

def c3127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3127 : Upper (D 3) (R 3) [34,65,24,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,288] 13 (by decide) (choices 1) [1,4,128] r3127 c3127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1032
  · exact u1033
  · exact u1034

def b3128 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 200 400 37 101 165 293), lower := (rows 35 67 28 200 400 32 64 128 256), losses := [] }

theorem u3128 : Upper (D 3) (R 3) [34,65,24,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3128
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3129 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 76 145 440 472 408 408), lower := (rows 35 67 37 76 145 32 64 128 256), losses := [] }

theorem u3129 : Upper (D 3) (R 3) [34,65,33,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3129
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3130 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 76 152 433 465 401 401), lower := (rows 35 67 37 76 152 32 64 128 256), losses := [] }

theorem u3130 : Upper (D 3) (R 3) [34,65,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3130
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3131 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 76 273 184 216 152 408), lower := (rows 35 67 37 76 273 32 64 128 256), losses := [] }

theorem u3131 : Upper (D 3) (R 3) [34,65,33,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3131
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3132 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 76 280 177 209 145 401), lower := (rows 35 67 37 76 280 32 64 128 256), losses := [] }

theorem u3132 : Upper (D 3) (R 3) [34,65,33,68,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3132
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3133 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 76 400 185 217 153 409), lower := (rows 35 67 37 76 400 32 64 128 256), losses := [] }

theorem u3133 : Upper (D 3) (R 3) [34,65,33,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3133
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3134 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 88 145 428 460 396 396), lower := (rows 35 67 37 88 145 32 64 128 256), losses := [] }

theorem u3134 : Upper (D 3) (R 3) [34,65,33,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3134
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3135 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 88 148 425 457 393 393), lower := (rows 35 67 37 88 148 32 64 128 256), losses := [] }

theorem u3135 : Upper (D 3) (R 3) [34,65,33,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3135
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3136 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 88 273 172 204 140 396), lower := (rows 35 67 37 88 273 32 64 128 256), losses := [] }

theorem u3136 : Upper (D 3) (R 3) [34,65,33,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3136
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3137 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 88 276 169 201 137 393), lower := (rows 35 67 37 88 276 32 64 128 256), losses := [] }

theorem u3137 : Upper (D 3) (R 3) [34,65,33,80,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3137
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3138 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 88 400 173 205 141 397), lower := (rows 35 67 37 88 400 32 64 128 256), losses := [] }

theorem u3138 : Upper (D 3) (R 3) [34,65,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3138
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3139 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 137 148 376 344 472 344), lower := (rows 35 67 37 137 148 32 64 128 256), losses := [] }

theorem u3139 : Upper (D 3) (R 3) [34,65,33,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3139
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3140 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 137 208 316 348 412 284), lower := (rows 35 67 37 137 208 32 64 128 256), losses := [] }

theorem u3140 : Upper (D 3) (R 3) [34,65,33,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3140
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3141 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 137 276 248 216 216 472), lower := (rows 35 67 37 137 276 32 64 128 256), losses := [] }

theorem u3141 : Upper (D 3) (R 3) [34,65,33,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3141
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3142 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 137 280 244 212 212 468), lower := (rows 35 67 37 137 280 32 64 128 256), losses := [] }

theorem u3142 : Upper (D 3) (R 3) [34,65,33,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3142
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3143 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 137 336 188 220 156 412), lower := (rows 35 67 37 137 336 32 64 128 256), losses := [] }

theorem u3143 : Upper (D 3) (R 3) [34,65,33,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3143
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3144 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 137 400 124 92 220 348), lower := (rows 35 67 37 137 400 32 64 128 256), losses := [] }

theorem u3144 : Upper (D 3) (R 3) [34,65,33,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3144
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3145 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 140 208 313 345 409 281), lower := (rows 35 67 37 140 208 32 64 128 256), losses := [] }

theorem u3145 : Upper (D 3) (R 3) [34,65,33,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3145
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3146 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 140 273 248 216 216 472), lower := (rows 35 67 37 140 273 32 64 128 256), losses := [] }

theorem u3146 : Upper (D 3) (R 3) [34,65,33,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3146
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3147 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 140 280 241 209 209 465), lower := (rows 35 67 37 140 280 32 64 128 256), losses := [] }

theorem u3147 : Upper (D 3) (R 3) [34,65,33,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3147
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3148 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 140 336 185 217 153 409), lower := (rows 35 67 37 140 336 32 64 128 256), losses := [] }

theorem u3148 : Upper (D 3) (R 3) [34,65,33,132,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3148
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3149 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 140 400 121 89 217 345), lower := (rows 35 67 37 140 400 32 64 128 256), losses := [] }

theorem u3149 : Upper (D 3) (R 3) [34,65,33,132,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3149
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3150 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 152 273 236 204 204 460), lower := (rows 35 67 37 152 273 32 64 128 256), losses := [] }

theorem u3150 : Upper (D 3) (R 3) [34,65,33,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3150
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3151 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 152 276 233 201 201 457), lower := (rows 35 67 37 152 276 32 64 128 256), losses := [] }

theorem u3151 : Upper (D 3) (R 3) [34,65,33,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3151
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3152 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 152 280 229 197 197 453), lower := (rows 35 67 37 152 280 32 64 128 256), losses := [] }

theorem u3152 : Upper (D 3) (R 3) [34,65,33,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3152
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3153 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 152 336 173 205 141 397), lower := (rows 35 67 37 152 336 32 64 128 256), losses := [] }

theorem u3153 : Upper (D 3) (R 3) [34,65,33,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3153
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3154 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 200 273 188 220 156 412), lower := (rows 35 67 37 200 273 32 64 128 256), losses := [] }

theorem u3154 : Upper (D 3) (R 3) [34,65,33,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3154
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3155 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 200 276 185 217 153 409), lower := (rows 35 67 37 200 276 32 64 128 256), losses := [] }

theorem u3155 : Upper (D 3) (R 3) [34,65,33,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3155
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3156 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 200 280 181 213 149 405), lower := (rows 35 67 37 200 280 32 64 128 256), losses := [] }

theorem u3156 : Upper (D 3) (R 3) [34,65,33,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3156
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3157 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 200 400 61 93 157 285), lower := (rows 35 67 37 200 400 32 64 128 256), losses := [] }

theorem u3157 : Upper (D 3) (R 3) [34,65,33,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3157
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3158 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 145 436 468 404 404), lower := (rows 35 67 44 73 145 32 64 128 256), losses := [] }

theorem u3158 : Upper (D 3) (R 3) [34,65,40,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3158
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3159 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 148 433 465 401 401), lower := (rows 35 67 44 73 148 32 64 128 256), losses := [] }

theorem u3159 : Upper (D 3) (R 3) [34,65,40,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3159
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3160 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 273 180 212 148 404), lower := (rows 35 67 44 73 273 32 64 128 256), losses := [] }

theorem u3160 : Upper (D 3) (R 3) [34,65,40,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3160
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3161 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 276 177 209 145 401), lower := (rows 35 67 44 73 276 32 64 128 256), losses := [] }

theorem u3161 : Upper (D 3) (R 3) [34,65,40,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3161
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3162 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 400 181 213 149 405), lower := (rows 35 67 44 73 400 32 64 128 256), losses := [] }

theorem u3162 : Upper (D 3) (R 3) [34,65,40,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3162
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3163 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 76 145 433 465 401 401), lower := (rows 35 67 44 76 145 32 64 128 256), losses := [] }

theorem u3163 : Upper (D 3) (R 3) [34,65,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3163
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3164 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 76 273 177 209 145 401), lower := (rows 35 67 44 76 273 32 64 128 256), losses := [] }

theorem u3164 : Upper (D 3) (R 3) [34,65,40,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3164
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3165 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 76 400 177 209 145 401), lower := (rows 35 67 44 76 400 32 64 128 256), losses := [] }

theorem u3165 : Upper (D 3) (R 3) [34,65,40,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3165
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3166 : Route 9 := (fun mask => (mask,id))

def c3166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u3166 : Upper (D 3) (R 3) [34,65,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,129] 13 (by decide) (choices 1) [1,4,128,256] r3166 c3166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1035
  · exact u1036
  · exact u1037
  · exact u1038

def b3167 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 88 148 417 449 385 385), lower := (rows 35 67 44 88 148 32 64 128 256), losses := [] }

theorem u3167 : Upper (D 3) (R 3) [34,65,40,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3167
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3168 : Route 9 := (fun mask => (mask,id))

def c3168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3168 : Upper (D 3) (R 3) [34,65,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,257] 13 (by decide) (choices 1) [1,4,128] r3168 c3168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1039
  · exact u1040
  · exact u1041

def b3169 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 88 276 161 193 129 385), lower := (rows 35 67 44 88 276 32 64 128 256), losses := [] }

theorem u3169 : Upper (D 3) (R 3) [34,65,40,80,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3169
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3170 : Route 9 := (fun mask => (mask,id))

def c3170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3170 : Upper (D 3) (R 3) [34,65,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,384] 13 (by decide) (choices 1) [1,4,128] r3170 c3170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1042
  · exact u1043
  · exact u1044

def b3171 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 137 81 436 468 404 404), lower := (rows 35 67 44 137 81 32 64 128 256), losses := [] }

theorem u3171 : Upper (D 3) (R 3) [34,65,40,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3171
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3172 : Route 9 := (fun mask => (mask,id))

def c3172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u3172 : Upper (D 3) (R 3) [34,65,40,129,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,68] 13 (by decide) (choices 1) [1,16,128,256] r3172 c3172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1045
  · exact u1046
  · exact u1047
  · exact u1048

def b3173 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 137 145 372 340 468 340), lower := (rows 35 67 44 137 145 32 64 128 256), losses := [] }

theorem u3173 : Upper (D 3) (R 3) [34,65,40,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3173
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3174 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 137 148 369 337 465 337), lower := (rows 35 67 44 137 148 32 64 128 256), losses := [] }

theorem u3174 : Upper (D 3) (R 3) [34,65,40,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3174
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3175 : Route 9 := (fun mask => (mask,id))

def c3175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u3175 : Upper (D 3) (R 3) [34,65,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,192] 13 (by decide) (choices 1) [1,4,16,256] r3175 c3175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1049
  · exact u1050
  · exact u1051
  · exact u1052

def r3176 : Route 9 := (fun mask => (mask,id))

def c3176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3176 : Upper (D 3) (R 3) [34,65,40,129,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,257] 13 (by decide) (choices 1) [4,16,64,128] r3176 c3176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1053
  · exact u1054
  · exact u1055
  · exact u1056

def r3177 : Route 9 := (fun mask => (mask,id))

def c3177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3177 : Upper (D 3) (R 3) [34,65,40,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,260] 13 (by decide) (choices 1) [1,16,64,128] r3177 c3177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1057
  · exact u1058
  · exact u1059
  · exact u1060

def r3178 : Route 9 := (fun mask => (mask,id))

def c3178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3178 : Upper (D 3) (R 3) [34,65,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,320] 13 (by decide) (choices 1) [1,4,16,128] r3178 c3178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1061
  · exact u1062
  · exact u1063
  · exact u1064

def r3179 : Route 9 := (fun mask => (mask,id))

def c3179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3179 : Upper (D 3) (R 3) [34,65,40,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,384] 13 (by decide) (choices 1) [1,4,16,64] r3179 c3179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1065
  · exact u1066
  · exact u1067
  · exact u1068

#print axioms u3179
end Delivery.IrregularNine14.P03
