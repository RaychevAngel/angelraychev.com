import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0006

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2160 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 324 168 18 248 216 216 472), lower := (rows 23 35 324 168 18 32 64 128 256), losses := [] }

theorem u2160 : Upper (D 1) (R 1) [22,33,320,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2160
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2161 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 35 324 168 24 242 210 210 466), lower := (rows 23 35 324 168 24 32 64 128 256), losses := [] }

theorem u2161 : Upper (D 1) (R 1) [22,33,320,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2161
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2162 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 168 80 186 218 154 410), lower := (rows 23 35 324 168 80 32 64 128 256), losses := [] }

theorem u2162 : Upper (D 1) (R 1) [22,33,320,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2163 : Route 9 := (fun mask => (mask,id))

def c2163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2163 : Upper (D 1) (R 1) [22,33,320,160,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,160,128] 13 (by decide) (choices 1) [2,8,16,64] r2163 c2163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u401
  · exact u402
  · exact u403
  · exact u404

def b2164 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 324 200 18 184 248 184 440), lower := (rows 23 35 324 200 18 32 64 128 256), losses := [] }

theorem u2164 : Upper (D 1) (R 1) [22,33,320,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2164
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 23 35 324 200 24 178 242 178 434), lower := (rows 23 35 324 200 24 32 64 128 256), losses := [] }

theorem u2165 : Upper (D 1) (R 1) [22,33,320,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2165
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2166 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 324 200 48 186 218 154 410), lower := (rows 23 35 324 200 48 32 64 128 256), losses := [] }

theorem u2166 : Upper (D 1) (R 1) [22,33,320,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2166
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2167 : Route 9 := (fun mask => (mask,id))

def c2167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2167 : Upper (D 1) (R 1) [22,33,320,192,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,192,128] 13 (by decide) (choices 1) [2,8,16] r2167 c2167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u405
  · exact u406
  · exact u407

def b2168 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 69 392 18 240 240 240 496), lower := (rows 23 42 69 392 18 32 64 128 256), losses := [] }

theorem u2168 : Upper (D 1) (R 1) [22,40,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2168
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2169 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 69 392 48 242 210 210 466), lower := (rows 23 42 69 392 48 32 64 128 256), losses := [] }

theorem u2169 : Upper (D 1) (R 1) [22,40,65,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2170 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 69 392 80 178 242 178 434), lower := (rows 23 42 69 392 80 32 64 128 256), losses := [] }

theorem u2170 : Upper (D 1) (R 1) [22,40,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2170
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2171 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 23 42 69 392 144 114 114 242 370), lower := (rows 23 42 69 392 144 32 64 128 256), losses := [] }

theorem u2171 : Upper (D 1) (R 1) [22,40,65,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2172 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 196 265 18 240 240 240 496), lower := (rows 23 42 196 265 18 32 64 128 256), losses := [] }

theorem u2172 : Upper (D 1) (R 1) [22,40,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2172
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2173 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 196 265 48 242 210 210 466), lower := (rows 23 42 196 265 48 32 64 128 256), losses := [] }

theorem u2173 : Upper (D 1) (R 1) [22,40,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2174 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 196 265 80 178 242 178 434), lower := (rows 23 42 196 265 80 32 64 128 256), losses := [] }

theorem u2174 : Upper (D 1) (R 1) [22,40,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2174
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 23 42 196 328 17 178 242 178 434), lower := (rows 23 42 196 328 17 32 64 128 256), losses := [] }

theorem u2175 : Upper (D 1) (R 1) [22,40,192,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2175
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2176 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 196 328 18 177 241 177 433), lower := (rows 23 42 196 328 18 32 64 128 256), losses := [] }

theorem u2176 : Upper (D 1) (R 1) [22,40,192,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2176
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2177 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 196 328 48 179 211 147 403), lower := (rows 23 42 196 328 48 32 64 128 256), losses := [] }

theorem u2177 : Upper (D 1) (R 1) [22,40,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2177
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2178 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 42 196 328 144 51 115 179 307), lower := (rows 23 42 196 328 144 32 64 128 256), losses := [] }

theorem u2178 : Upper (D 1) (R 1) [22,40,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2179 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 261 200 18 240 240 240 496), lower := (rows 23 42 261 200 18 32 64 128 256), losses := [] }

theorem u2179 : Upper (D 1) (R 1) [22,40,257,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2179
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2180 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 261 200 48 242 210 210 466), lower := (rows 23 42 261 200 48 32 64 128 256), losses := [] }

theorem u2180 : Upper (D 1) (R 1) [22,40,257,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2180
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2181 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 23 42 261 200 80 178 242 178 434), lower := (rows 23 42 261 200 80 32 64 128 256), losses := [] }

theorem u2181 : Upper (D 1) (R 1) [22,40,257,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2181
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2182 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 324 137 18 240 240 240 496), lower := (rows 23 42 324 137 18 32 64 128 256), losses := [] }

theorem u2182 : Upper (D 1) (R 1) [22,40,320,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2182
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2183 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 324 137 48 242 210 210 466), lower := (rows 23 42 324 137 48 32 64 128 256), losses := [] }

theorem u2183 : Upper (D 1) (R 1) [22,40,320,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2183
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2184 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 324 137 80 178 242 178 434), lower := (rows 23 42 324 137 80 32 64 128 256), losses := [] }

theorem u2184 : Upper (D 1) (R 1) [22,40,320,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2184
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2185 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 23 42 324 137 144 114 114 242 370), lower := (rows 23 42 324 137 144 32 64 128 256), losses := [] }

theorem u2185 : Upper (D 1) (R 1) [22,40,320,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2185
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2186 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 23 42 324 200 17 178 242 178 434), lower := (rows 23 42 324 200 17 32 64 128 256), losses := [] }

theorem u2186 : Upper (D 1) (R 1) [22,40,320,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2186
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2187 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 324 200 18 177 241 177 433), lower := (rows 23 42 324 200 18 32 64 128 256), losses := [] }

theorem u2187 : Upper (D 1) (R 1) [22,40,320,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2187
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2188 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 324 200 48 179 211 147 403), lower := (rows 23 42 324 200 48 32 64 128 256), losses := [] }

theorem u2188 : Upper (D 1) (R 1) [22,40,320,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2188
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2189 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 23 42 324 200 144 51 115 179 307), lower := (rows 23 42 324 200 144 32 64 128 256), losses := [] }

theorem u2189 : Upper (D 1) (R 1) [22,40,320,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2189
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2190 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 13 138 48 496 464 464 464), lower := (rows 23 98 13 138 48 32 64 128 256), losses := [] }

theorem u2190 : Upper (D 1) (R 1) [22,96,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2191 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 21, targets := 32 }], pairs := [(0,5)], upper := (rows 23 98 13 138 144 368 368 496 368), lower := (rows 23 98 13 138 144 32 64 128 256), losses := [] }

theorem u2191 : Upper (D 1) (R 1) [22,96,9,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2191
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2192 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 23 98 13 138 272 240 240 240 496), lower := (rows 23 98 13 138 272 32 64 128 256), losses := [] }

theorem u2192 : Upper (D 1) (R 1) [22,96,9,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2192
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2193 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 13 168 18 496 464 464 464), lower := (rows 23 98 13 168 18 32 64 128 256), losses := [] }

theorem u2193 : Upper (D 1) (R 1) [22,96,9,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2193
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2194 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 13 168 80 434 466 402 402), lower := (rows 23 98 13 168 80 32 64 128 256), losses := [] }

theorem u2194 : Upper (D 1) (R 1) [22,96,9,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2194
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2195 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 13 168 144 370 338 466 338), lower := (rows 23 98 13 168 144 32 64 128 256), losses := [] }

theorem u2195 : Upper (D 1) (R 1) [22,96,9,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2195
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2196 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 98 13 168 272 242 210 210 466), lower := (rows 23 98 13 168 272 32 64 128 256), losses := [] }

theorem u2196 : Upper (D 1) (R 1) [22,96,9,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2196
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2197 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 13 266 48 240 208 208 464), lower := (rows 23 98 13 266 48 32 64 128 256), losses := [] }

theorem u2197 : Upper (D 1) (R 1) [22,96,9,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2197
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2198 : Route 9 := (fun mask => (mask,id))

def c2198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2198 : Upper (D 1) (R 1) [22,96,9,258,128] 13 := by
  apply FastRouting.sound _ _ [22,96,9,258,128] 13 (by decide) (choices 1) [16,64,128] r2198 c2198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u408
  · exact u409
  · exact u410

def b2199 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 13 296 18 240 208 208 464), lower := (rows 23 98 13 296 18 32 64 128 256), losses := [] }

theorem u2199 : Upper (D 1) (R 1) [22,96,9,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2199
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2200 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 13 296 80 178 210 146 402), lower := (rows 23 98 13 296 80 32 64 128 256), losses := [] }

theorem u2200 : Upper (D 1) (R 1) [22,96,9,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2200
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2201 : Route 9 := (fun mask => (mask,id))

def c2201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2201 : Upper (D 1) (R 1) [22,96,9,288,128] 13 := by
  apply FastRouting.sound _ _ [22,96,9,288,128] 13 (by decide) (choices 1) [2,16,64,128] r2201 c2201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u411
  · exact u412
  · exact u413
  · exact u414

def b2202 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 13 392 18 240 240 240 496), lower := (rows 23 98 13 392 18 32 64 128 256), losses := [] }

theorem u2202 : Upper (D 1) (R 1) [22,96,9,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2202
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2203 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 13 392 48 242 210 210 466), lower := (rows 23 98 13 392 48 32 64 128 256), losses := [] }

theorem u2203 : Upper (D 1) (R 1) [22,96,9,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2203
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2204 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 13 392 144 114 114 242 370), lower := (rows 23 98 13 392 144 32 64 128 256), losses := [] }

theorem u2204 : Upper (D 1) (R 1) [22,96,9,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2205 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 23 98 133 266 24 240 240 240 496), lower := (rows 23 98 133 266 24 32 64 128 256), losses := [] }

theorem u2205 : Upper (D 1) (R 1) [22,96,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2205
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2206 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 133 266 48 248 216 216 472), lower := (rows 23 98 133 266 48 32 64 128 256), losses := [] }

theorem u2206 : Upper (D 1) (R 1) [22,96,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2206
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2207 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 133 266 144 120 120 248 376), lower := (rows 23 98 133 266 144 32 64 128 256), losses := [] }

theorem u2207 : Upper (D 1) (R 1) [22,96,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2207
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2208 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 133 296 18 248 216 216 472), lower := (rows 23 98 133 296 18 32 64 128 256), losses := [] }

theorem u2208 : Upper (D 1) (R 1) [22,96,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2209 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 98 133 296 24 242 210 210 466), lower := (rows 23 98 133 296 24 32 64 128 256), losses := [] }

theorem u2209 : Upper (D 1) (R 1) [22,96,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2209
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2210 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 133 296 80 186 218 154 410), lower := (rows 23 98 133 296 80 32 64 128 256), losses := [] }

theorem u2210 : Upper (D 1) (R 1) [22,96,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2210
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 133 296 144 122 90 218 346), lower := (rows 23 98 133 296 144 32 64 128 256), losses := [] }

theorem u2211 : Upper (D 1) (R 1) [22,96,129,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2211
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2212 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 140 265 18 240 240 240 496), lower := (rows 23 98 140 265 18 32 64 128 256), losses := [] }

theorem u2212 : Upper (D 1) (R 1) [22,96,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2212
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2213 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 140 265 48 242 210 210 466), lower := (rows 23 98 140 265 48 32 64 128 256), losses := [] }

theorem u2213 : Upper (D 1) (R 1) [22,96,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2213
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2214 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 140 265 144 114 114 242 370), lower := (rows 23 98 140 265 144 32 64 128 256), losses := [] }

theorem u2214 : Upper (D 1) (R 1) [22,96,136,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2214
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2215 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 23 98 140 266 17 240 240 240 496), lower := (rows 23 98 140 266 17 32 64 128 256), losses := [] }

theorem u2215 : Upper (D 1) (R 1) [22,96,136,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2215
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2216 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 140 266 48 241 209 209 465), lower := (rows 23 98 140 266 48 32 64 128 256), losses := [] }

theorem u2216 : Upper (D 1) (R 1) [22,96,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2216
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2217 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 140 266 144 113 113 241 369), lower := (rows 23 98 140 266 144 32 64 128 256), losses := [] }

theorem u2217 : Upper (D 1) (R 1) [22,96,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2217
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 98 140 296 17 242 210 210 466), lower := (rows 23 98 140 296 17 32 64 128 256), losses := [] }

theorem u2218 : Upper (D 1) (R 1) [22,96,136,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2218
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2219 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 140 296 18 241 209 209 465), lower := (rows 23 98 140 296 18 32 64 128 256), losses := [] }

theorem u2219 : Upper (D 1) (R 1) [22,96,136,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2219
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2219
end Delivery.IrregularNine14.P01
