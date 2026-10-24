import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0006

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2160 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 56 145 34 332 396 268), lower := (rows 7 35 76 56 145 34 64 128 256), losses := [] }

theorem u2160 : Upper (D 5) (R 5) [6,33,72,48,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2160
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2161 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 56 145 36 330 394 266), lower := (rows 7 35 76 56 145 36 64 128 256), losses := [] }

theorem u2161 : Upper (D 5) (R 5) [6,33,72,48,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2161
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2162 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 400, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 76 56 145 40 326 390 262), lower := (rows 7 35 76 56 145 40 64 128 256), losses := [] }

theorem u2162 : Upper (D 5) (R 5) [6,33,72,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2162
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2163 : Route 9 := (fun mask => (mask,id))

def c2163 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2163 : Upper (D 5) (R 5) [6,33,72,48,129,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,129,256] 13 (by decide) (choices 1) [2,4,8] r2163 c2163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u384
  · exact u385
  · exact u386

def b2164 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 56 146 33 332 396 268), lower := (rows 7 35 76 56 146 33 64 128 256), losses := [] }

theorem u2164 : Upper (D 5) (R 5) [6,33,72,48,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2164
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 56 146 36 329 393 265), lower := (rows 7 35 76 56 146 36 64 128 256), losses := [] }

theorem u2165 : Upper (D 5) (R 5) [6,33,72,48,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2166 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 76 56 146 40 325 389 261), lower := (rows 7 35 76 56 146 40 64 128 256), losses := [] }

theorem u2166 : Upper (D 5) (R 5) [6,33,72,48,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2166
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2167 : Route 9 := (fun mask => (mask,id))

def c2167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2167 : Upper (D 5) (R 5) [6,33,72,48,130,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,130,256] 13 (by decide) (choices 1) [1,4,8] r2167 c2167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u387
  · exact u388
  · exact u389

def b2168 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 56 148 33 330 394 266), lower := (rows 7 35 76 56 148 33 64 128 256), losses := [] }

theorem u2168 : Upper (D 5) (R 5) [6,33,72,48,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2168
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2169 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 56 148 34 329 393 265), lower := (rows 7 35 76 56 148 34 64 128 256), losses := [] }

theorem u2169 : Upper (D 5) (R 5) [6,33,72,48,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2169
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2170 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 76 56 148 40 323 387 259), lower := (rows 7 35 76 56 148 40 64 128 256), losses := [] }

theorem u2170 : Upper (D 5) (R 5) [6,33,72,48,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2170
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2171 : Route 9 := (fun mask => (mask,id))

def c2171 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2171 : Upper (D 5) (R 5) [6,33,72,48,132,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,132,256] 13 (by decide) (choices 1) [1,2,8] r2171 c2171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u390
  · exact u391
  · exact u392

def b2172 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 56 400 33 78 142 270), lower := (rows 7 35 76 56 400 33 64 128 256), losses := [] }

theorem u2172 : Upper (D 5) (R 5) [6,33,72,48,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2172
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2173 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 56 400 34 77 141 269), lower := (rows 7 35 76 56 400 34 64 128 256), losses := [] }

theorem u2173 : Upper (D 5) (R 5) [6,33,72,48,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2173
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2174 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 56 400 36 75 139 267), lower := (rows 7 35 76 56 400 36 64 128 256), losses := [] }

theorem u2174 : Upper (D 5) (R 5) [6,33,72,48,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2174
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 76 56 400 40 71 135 263), lower := (rows 7 35 76 56 400 40 64 128 256), losses := [] }

theorem u2175 : Upper (D 5) (R 5) [6,33,72,48,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2175
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2176 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 137 56 34 340 404 276), lower := (rows 7 35 76 137 56 34 64 128 256), losses := [] }

theorem u2176 : Upper (D 5) (R 5) [6,33,72,129,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2177 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 137 56 36 338 402 274), lower := (rows 7 35 76 137 56 36 64 128 256), losses := [] }

theorem u2177 : Upper (D 5) (R 5) [6,33,72,129,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2177
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2178 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 76 137 56 48 326 390 262), lower := (rows 7 35 76 137 56 48 64 128 256), losses := [] }

theorem u2178 : Upper (D 5) (R 5) [6,33,72,129,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2178
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2179 : PairBound 9 := { available := 22, camps := [], pairs := [(2,0)], upper := (rows 7 35 76 137 56 288 86 150 278), lower := (rows 7 35 76 137 56 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 28 299 65 129 257), good := (rows 502 482 124 508 60 288 64 128 288) }] }

theorem u2179 : Upper (D 5) (R 5) [6,33,72,129,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2179
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2180 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 137 274 36 120 184 312), lower := (rows 7 35 76 137 274 36 64 128 256), losses := [] }

theorem u2180 : Upper (D 5) (R 5) [6,33,72,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2180
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2181 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 35 76 137 274 40 116 180 308), lower := (rows 7 35 76 137 274 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 8 19 44 75 139 267), good := (rows 502 502 492 508 466 492 64 128 256) }] }

theorem u2181 : Upper (D 5) (R 5) [6,33,72,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2181
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2182 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 7 35 76 137 274 48 108 172 300), lower := (rows 7 35 76 137 274 48 64 128 256), losses := [] }

theorem u2182 : Upper (D 5) (R 5) [6,33,72,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2182
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2183 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 137 276 34 120 184 312), lower := (rows 7 35 76 137 276 34 64 128 256), losses := [] }

theorem u2183 : Upper (D 5) (R 5) [6,33,72,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2183
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2184 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 35 76 137 276 40 114 178 306), lower := (rows 7 35 76 137 276 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 44 67 131 259), good := (rows 502 498 124 508 308 60 64 128 256) }] }

theorem u2184 : Upper (D 5) (R 5) [6,33,72,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2184
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2185 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 137 276 48 106 170 298), lower := (rows 7 35 76 137 276 48 64 128 256), losses := [] }

theorem u2185 : Upper (D 5) (R 5) [6,33,72,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2185
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2186 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 137 280 34 116 180 308), lower := (rows 7 35 76 137 280 34 64 128 256), losses := [] }

theorem u2186 : Upper (D 5) (R 5) [6,33,72,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2186
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2187 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 137 280 36 114 178 306), lower := (rows 7 35 76 137 280 36 64 128 256), losses := [] }

theorem u2187 : Upper (D 5) (R 5) [6,33,72,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2187
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2188 : PairBound 9 := { available := 38, camps := [], pairs := [(2,0)], upper := (rows 7 35 76 137 280 48 102 166 294), lower := (rows 7 35 76 137 280 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 65 129 257), good := (rows 486 482 124 508 316 48 64 128 256) }] }

theorem u2188 : Upper (D 5) (R 5) [6,33,72,129,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2189 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 137 304 34 92 156 284), lower := (rows 7 35 76 137 304 34 64 128 256), losses := [] }

theorem u2189 : Upper (D 5) (R 5) [6,33,72,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2189
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2190 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 137 304 36 90 154 282), lower := (rows 7 35 76 137 304 36 64 128 256), losses := [] }

theorem u2190 : Upper (D 5) (R 5) [6,33,72,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2190
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2191 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 35 76 137 304 40 86 150 278), lower := (rows 7 35 76 137 304 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 44 65 129 257), good := (rows 502 498 124 508 304 60 64 128 256) }] }

theorem u2191 : Upper (D 5) (R 5) [6,33,72,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2192 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 137 304 48 78 142 270), lower := (rows 7 35 76 137 304 48 64 128 256), losses := [] }

theorem u2192 : Upper (D 5) (R 5) [6,33,72,129,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2192
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2193 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 138 56 33 340 404 276), lower := (rows 7 35 76 138 56 33 64 128 256), losses := [] }

theorem u2193 : Upper (D 5) (R 5) [6,33,72,130,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2193
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2194 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 138 56 36 337 401 273), lower := (rows 7 35 76 138 56 36 64 128 256), losses := [] }

theorem u2194 : Upper (D 5) (R 5) [6,33,72,130,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2194
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2195 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 76 138 56 48 325 389 261), lower := (rows 7 35 76 138 56 48 64 128 256), losses := [] }

theorem u2195 : Upper (D 5) (R 5) [6,33,72,130,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2195
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2196 : Route 9 := (fun mask => (mask,id))

def c2196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2196 : Upper (D 5) (R 5) [6,33,72,130,40,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,40,256] 13 (by decide) (choices 1) [1,4,16] r2196 c2196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u393
  · exact u394
  · exact u395

def b2197 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 138 273 36 120 184 312), lower := (rows 7 35 76 138 273 36 64 128 256), losses := [] }

theorem u2197 : Upper (D 5) (R 5) [6,33,72,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2198 : PairBound 9 := { available := 52, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 35 76 138 273 40 116 180 308), lower := (rows 7 35 76 138 273 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 8 19 44 75 139 267), good := (rows 501 501 492 508 465 492 64 128 256) }] }

theorem u2198 : Upper (D 5) (R 5) [6,33,72,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2198
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2199 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 138 273 48 108 172 300), lower := (rows 7 35 76 138 273 48 64 128 256), losses := [] }

theorem u2199 : Upper (D 5) (R 5) [6,33,72,130,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2199
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2200 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 138 276 33 120 184 312), lower := (rows 7 35 76 138 276 33 64 128 256), losses := [] }

theorem u2200 : Upper (D 5) (R 5) [6,33,72,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2200
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2201 : PairBound 9 := { available := 49, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 35 76 138 276 40 113 177 305), lower := (rows 7 35 76 138 276 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 44 67 131 259), good := (rows 501 497 124 508 308 60 64 128 256) }] }

theorem u2201 : Upper (D 5) (R 5) [6,33,72,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2202 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 138 276 48 105 169 297), lower := (rows 7 35 76 138 276 48 64 128 256), losses := [] }

theorem u2202 : Upper (D 5) (R 5) [6,33,72,130,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2203 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 138 280 33 116 180 308), lower := (rows 7 35 76 138 280 33 64 128 256), losses := [] }

theorem u2203 : Upper (D 5) (R 5) [6,33,72,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2204 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 138 280 36 113 177 305), lower := (rows 7 35 76 138 280 36 64 128 256), losses := [] }

theorem u2204 : Upper (D 5) (R 5) [6,33,72,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2205 : Route 9 := (fun mask => (mask,id))

def c2205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2205 : Upper (D 5) (R 5) [6,33,72,130,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,264,16] 13 (by decide) (choices 1) [1,4,32] r2205 c2205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u396
  · exact u397
  · exact u398

def b2206 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 138 304 33 92 156 284), lower := (rows 7 35 76 138 304 33 64 128 256), losses := [] }

theorem u2206 : Upper (D 5) (R 5) [6,33,72,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2206
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2207 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 138 304 36 89 153 281), lower := (rows 7 35 76 138 304 36 64 128 256), losses := [] }

theorem u2207 : Upper (D 5) (R 5) [6,33,72,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2207
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2208 : PairBound 9 := { available := 21, camps := [], pairs := [(1,2),(4,1)], upper := (rows 7 35 76 138 304 40 85 149 277), lower := (rows 7 35 76 138 304 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 19 44 65 129 257), good := (rows 501 497 108 184 304 40 64 128 256) },{ target := 2, region := (rows 1 3 0 8 16 44 64 128 256), good := (rows 35 35 104 170 304 40 64 128 256) }] }

theorem u2208 : Upper (D 5) (R 5) [6,33,72,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2208
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2209 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 138 304 48 77 141 269), lower := (rows 7 35 76 138 304 48 64 128 256), losses := [] }

theorem u2209 : Upper (D 5) (R 5) [6,33,72,130,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2209
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2210 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 140 26 33 368 432 304), lower := (rows 7 35 76 140 26 33 64 128 256), losses := [] }

theorem u2210 : Upper (D 5) (R 5) [6,33,72,132,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 7 35 76 140 26 48 353 417 289), lower := (rows 7 35 76 140 26 48 64 128 256), losses := [] }

theorem u2211 : Upper (D 5) (R 5) [6,33,72,132,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2211
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2212 : Route 9 := (fun mask => (mask,id))

def c2212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2212 : Upper (D 5) (R 5) [6,33,72,132,10,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,10,256] 13 (by decide) (choices 1) [1,16,32] r2212 c2212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u399
  · exact u400
  · exact u401

def b2213 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 140 56 33 338 402 274), lower := (rows 7 35 76 140 56 33 64 128 256), losses := [] }

theorem u2213 : Upper (D 5) (R 5) [6,33,72,132,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2213
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2214 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 140 56 34 337 401 273), lower := (rows 7 35 76 140 56 34 64 128 256), losses := [] }

theorem u2214 : Upper (D 5) (R 5) [6,33,72,132,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2215 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 76 140 56 48 323 387 259), lower := (rows 7 35 76 140 56 48 64 128 256), losses := [] }

theorem u2215 : Upper (D 5) (R 5) [6,33,72,132,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2216 : Route 9 := (fun mask => (mask,id))

def c2216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2216 : Upper (D 5) (R 5) [6,33,72,132,40,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,40,256] 13 (by decide) (choices 1) [1,2,16] r2216 c2216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u402
  · exact u403
  · exact u404

def b2217 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 140 273 34 120 184 312), lower := (rows 7 35 76 140 273 34 64 128 256), losses := [] }

theorem u2217 : Upper (D 5) (R 5) [6,33,72,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2217
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 272, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 140 273 40 114 178 306), lower := (rows 7 35 76 140 273 40 64 128 256), losses := [] }

theorem u2218 : Upper (D 5) (R 5) [6,33,72,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2219 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 140 273 48 106 170 298), lower := (rows 7 35 76 140 273 48 64 128 256), losses := [] }

theorem u2219 : Upper (D 5) (R 5) [6,33,72,132,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2219
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2219
end Delivery.IrregularNine14.P05
