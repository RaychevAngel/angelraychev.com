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

def b2220 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 140 274 33 120 184 312), lower := (rows 7 35 76 140 274 33 64 128 256), losses := [] }

theorem u2220 : Upper (D 5) (R 5) [6,33,72,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2220
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2221 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 272, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 140 274 40 113 177 305), lower := (rows 7 35 76 140 274 40 64 128 256), losses := [] }

theorem u2221 : Upper (D 5) (R 5) [6,33,72,132,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2221
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2222 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 7 35 76 140 274 48 105 169 297), lower := (rows 7 35 76 140 274 48 64 128 256), losses := [] }

theorem u2222 : Upper (D 5) (R 5) [6,33,72,132,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2222
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 140 280 33 114 178 306), lower := (rows 7 35 76 140 280 33 64 128 256), losses := [] }

theorem u2223 : Upper (D 5) (R 5) [6,33,72,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2223
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2224 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 140 280 34 113 177 305), lower := (rows 7 35 76 140 280 34 64 128 256), losses := [] }

theorem u2224 : Upper (D 5) (R 5) [6,33,72,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2224
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2225 : Route 9 := (fun mask => (mask,id))

def c2225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2225 : Upper (D 5) (R 5) [6,33,72,132,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,264,16] 13 (by decide) (choices 1) [1,2,32] r2225 c2225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u405
  · exact u406
  · exact u407

def b2226 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 140 304 33 90 154 282), lower := (rows 7 35 76 140 304 33 64 128 256), losses := [] }

theorem u2226 : Upper (D 5) (R 5) [6,33,72,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2226
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2227 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 140 304 34 89 153 281), lower := (rows 7 35 76 140 304 34 64 128 256), losses := [] }

theorem u2227 : Upper (D 5) (R 5) [6,33,72,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2228 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 272, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 140 304 40 83 147 275), lower := (rows 7 35 76 140 304 40 64 128 256), losses := [] }

theorem u2228 : Upper (D 5) (R 5) [6,33,72,132,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2228
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2229 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 140 304 48 75 139 267), lower := (rows 7 35 76 140 304 48 64 128 256), losses := [] }

theorem u2229 : Upper (D 5) (R 5) [6,33,72,132,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2229
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2230 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 152 273 34 108 172 300), lower := (rows 7 35 76 152 273 34 64 128 256), losses := [] }

theorem u2230 : Upper (D 5) (R 5) [6,33,72,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2231 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 152 273 36 106 170 298), lower := (rows 7 35 76 152 273 36 64 128 256), losses := [] }

theorem u2231 : Upper (D 5) (R 5) [6,33,72,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2231
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2232 : PairBound 9 := { available := 38, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 152 273 40 102 166 294), lower := (rows 7 35 76 152 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 60 65 129 257), good := (rows 486 482 108 188 508 40 64 128 256) }] }

theorem u2232 : Upper (D 5) (R 5) [6,33,72,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2232
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2233 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 152 274 33 108 172 300), lower := (rows 7 35 76 152 274 33 64 128 256), losses := [] }

theorem u2233 : Upper (D 5) (R 5) [6,33,72,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2233
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2234 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 152 274 36 105 169 297), lower := (rows 7 35 76 152 274 36 64 128 256), losses := [] }

theorem u2234 : Upper (D 5) (R 5) [6,33,72,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2234
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2235 : Route 9 := (fun mask => (mask,id))

def c2235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2235 : Upper (D 5) (R 5) [6,33,72,144,258,8] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,258,8] 13 (by decide) (choices 1) [1,4,32] r2235 c2235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u408
  · exact u409
  · exact u410

def b2236 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 152 276 33 106 170 298), lower := (rows 7 35 76 152 276 33 64 128 256), losses := [] }

theorem u2236 : Upper (D 5) (R 5) [6,33,72,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2236
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2237 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 152 276 34 105 169 297), lower := (rows 7 35 76 152 276 34 64 128 256), losses := [] }

theorem u2237 : Upper (D 5) (R 5) [6,33,72,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2238 : PairBound 9 := { available := 35, camps := [], pairs := [(1,2),(4,3)], upper := (rows 7 35 76 152 276 40 99 163 291), lower := (rows 7 35 76 152 276 40 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 44 67 131 259), good := (rows 483 483 104 184 304 40 64 128 256) },{ target := 3, region := (rows 1 2 4 0 17 32 66 130 258), good := (rows 471 499 68 144 276 32 64 128 256) }] }

theorem u2238 : Upper (D 5) (R 5) [6,33,72,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2238
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2239 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 152 304 33 78 142 270), lower := (rows 7 35 76 152 304 33 64 128 256), losses := [] }

theorem u2239 : Upper (D 5) (R 5) [6,33,72,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2239
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2240 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 152 304 34 77 141 269), lower := (rows 7 35 76 152 304 34 64 128 256), losses := [] }

theorem u2240 : Upper (D 5) (R 5) [6,33,72,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2240
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2241 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 152 304 36 75 139 267), lower := (rows 7 35 76 152 304 36 64 128 256), losses := [] }

theorem u2241 : Upper (D 5) (R 5) [6,33,72,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2241
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2242 : PairBound 9 := { available := 7, camps := [], pairs := [(1,2),(4,3)], upper := (rows 7 35 76 152 304 40 71 135 263), lower := (rows 7 35 76 152 304 40 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 44 64 128 256), good := (rows 35 35 104 184 304 40 64 128 256) },{ target := 3, region := (rows 1 2 4 0 18 32 65 129 257), good := (rows 471 499 68 144 304 32 64 128 256) }] }

theorem u2242 : Upper (D 5) (R 5) [6,33,72,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2242
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2243 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 168 25 34 340 404 276), lower := (rows 7 35 76 168 25 34 64 128 256), losses := [] }

theorem u2243 : Upper (D 5) (R 5) [6,33,72,160,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2243
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2244 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 168 25 36 338 402 274), lower := (rows 7 35 76 168 25 36 64 128 256), losses := [] }

theorem u2244 : Upper (D 5) (R 5) [6,33,72,160,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2244
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2245 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 168 25 48 326 390 262), lower := (rows 7 35 76 168 25 48 64 128 256), losses := [] }

theorem u2245 : Upper (D 5) (R 5) [6,33,72,160,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2245
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2246 : Route 9 := (fun mask => (mask,id))

def c2246 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2246 : Upper (D 5) (R 5) [6,33,72,160,9,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,9,256] 13 (by decide) (choices 1) [2,4,16] r2246 c2246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u411
  · exact u412
  · exact u413

def b2247 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 168 273 34 92 156 284), lower := (rows 7 35 76 168 273 34 64 128 256), losses := [] }

theorem u2247 : Upper (D 5) (R 5) [6,33,72,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2247
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2248 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 168 273 36 90 154 282), lower := (rows 7 35 76 168 273 36 64 128 256), losses := [] }

theorem u2248 : Upper (D 5) (R 5) [6,33,72,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2248
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2249 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 76 168 273 40 86 150 278), lower := (rows 7 35 76 168 273 40 64 128 256), losses := [] }

theorem u2249 : Upper (D 5) (R 5) [6,33,72,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2249
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2250 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 168 273 48 78 142 270), lower := (rows 7 35 76 168 273 48 64 128 256), losses := [] }

theorem u2250 : Upper (D 5) (R 5) [6,33,72,160,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2250
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2251 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 168 274 33 92 156 284), lower := (rows 7 35 76 168 274 33 64 128 256), losses := [] }

theorem u2251 : Upper (D 5) (R 5) [6,33,72,160,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2251
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2252 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 168 274 36 89 153 281), lower := (rows 7 35 76 168 274 36 64 128 256), losses := [] }

theorem u2252 : Upper (D 5) (R 5) [6,33,72,160,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2252
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2253 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 76 168 274 40 85 149 277), lower := (rows 7 35 76 168 274 40 64 128 256), losses := [] }

theorem u2253 : Upper (D 5) (R 5) [6,33,72,160,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2253
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2254 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 7 35 76 168 274 48 77 141 269), lower := (rows 7 35 76 168 274 48 64 128 256), losses := [] }

theorem u2254 : Upper (D 5) (R 5) [6,33,72,160,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2254
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2255 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 168 276 33 90 154 282), lower := (rows 7 35 76 168 276 33 64 128 256), losses := [] }

theorem u2255 : Upper (D 5) (R 5) [6,33,72,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2255
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2256 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 168 276 34 89 153 281), lower := (rows 7 35 76 168 276 34 64 128 256), losses := [] }

theorem u2256 : Upper (D 5) (R 5) [6,33,72,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2256
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2257 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 76 168 276 40 83 147 275), lower := (rows 7 35 76 168 276 40 64 128 256), losses := [] }

theorem u2257 : Upper (D 5) (R 5) [6,33,72,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2257
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2258 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 168 276 48 75 139 267), lower := (rows 7 35 76 168 276 48 64 128 256), losses := [] }

theorem u2258 : Upper (D 5) (R 5) [6,33,72,160,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2258
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2259 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 168 280 33 86 150 278), lower := (rows 7 35 76 168 280 33 64 128 256), losses := [] }

theorem u2259 : Upper (D 5) (R 5) [6,33,72,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2259
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2260 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 168 280 34 85 149 277), lower := (rows 7 35 76 168 280 34 64 128 256), losses := [] }

theorem u2260 : Upper (D 5) (R 5) [6,33,72,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2260
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2261 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 168 280 36 83 147 275), lower := (rows 7 35 76 168 280 36 64 128 256), losses := [] }

theorem u2261 : Upper (D 5) (R 5) [6,33,72,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2262 : Route 9 := (fun mask => (mask,id))

def c2262 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2262 : Upper (D 5) (R 5) [6,33,72,160,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,264,16] 13 (by decide) (choices 1) [1,2,4] r2262 c2262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u414
  · exact u415
  · exact u416

def b2263 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 392 25 34 116 180 308), lower := (rows 7 35 76 392 25 34 64 128 256), losses := [] }

theorem u2263 : Upper (D 5) (R 5) [6,33,72,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2263
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 392 25 36 114 178 306), lower := (rows 7 35 76 392 25 36 64 128 256), losses := [] }

theorem u2264 : Upper (D 5) (R 5) [6,33,72,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2265 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 392 25 48 102 166 294), lower := (rows 7 35 76 392 25 48 64 128 256), losses := [] }

theorem u2265 : Upper (D 5) (R 5) [6,33,72,384,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2265
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2266 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 392 26 33 116 180 308), lower := (rows 7 35 76 392 26 33 64 128 256), losses := [] }

theorem u2266 : Upper (D 5) (R 5) [6,33,72,384,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2266
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2267 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 392 26 36 113 177 305), lower := (rows 7 35 76 392 26 36 64 128 256), losses := [] }

theorem u2267 : Upper (D 5) (R 5) [6,33,72,384,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2268 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 7 35 76 392 26 48 101 165 293), lower := (rows 7 35 76 392 26 48 64 128 256), losses := [] }

theorem u2268 : Upper (D 5) (R 5) [6,33,72,384,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 392 56 33 86 150 278), lower := (rows 7 35 76 392 56 33 64 128 256), losses := [] }

theorem u2269 : Upper (D 5) (R 5) [6,33,72,384,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2270 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 392 56 34 85 149 277), lower := (rows 7 35 76 392 56 34 64 128 256), losses := [] }

theorem u2270 : Upper (D 5) (R 5) [6,33,72,384,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2271 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 392 56 36 83 147 275), lower := (rows 7 35 76 392 56 36 64 128 256), losses := [] }

theorem u2271 : Upper (D 5) (R 5) [6,33,72,384,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2272 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 76 392 56 48 71 135 263), lower := (rows 7 35 76 392 56 48 64 128 256), losses := [] }

theorem u2272 : Upper (D 5) (R 5) [6,33,72,384,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2272
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2273 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 137 56 34 332 396 268), lower := (rows 7 35 84 137 56 34 64 128 256), losses := [] }

theorem u2273 : Upper (D 5) (R 5) [6,33,80,129,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2273
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2274 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 84 137 56 36 330 394 266), lower := (rows 7 35 84 137 56 36 64 128 256), losses := [] }

theorem u2274 : Upper (D 5) (R 5) [6,33,80,129,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2275 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 327, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 84 137 56 40 326 390 262), lower := (rows 7 35 84 137 56 40 64 128 256), losses := [] }

theorem u2275 : Upper (D 5) (R 5) [6,33,80,129,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2275
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2276 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 84 137 56 288 78 142 270), lower := (rows 7 35 84 137 56 288 64 128 256), losses := [] }

theorem u2276 : Upper (D 5) (R 5) [6,33,80,129,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2276
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2277 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 137 280 34 108 172 300), lower := (rows 7 35 84 137 280 34 64 128 256), losses := [] }

theorem u2277 : Upper (D 5) (R 5) [6,33,80,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2277
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 84 137 280 36 106 170 298), lower := (rows 7 35 84 137 280 36 64 128 256), losses := [] }

theorem u2278 : Upper (D 5) (R 5) [6,33,80,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2278
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2279 : Route 9 := (fun mask => (mask,id))

def c2279 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2279 : Upper (D 5) (R 5) [6,33,80,129,264,8] 13 := by
  apply FastRouting.sound _ _ [6,33,80,129,264,8] 13 (by decide) (choices 1) [2,4,32] r2279 c2279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u417
  · exact u418
  · exact u419

#print axioms u2279
end Delivery.IrregularNine14.P05
