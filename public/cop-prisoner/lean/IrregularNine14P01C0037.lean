import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0006
import IrregularNine14P01C0007

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2220 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 140 296 80 179 211 147 403), lower := (rows 23 98 140 296 80 32 64 128 256), losses := [] }

theorem u2220 : Upper (D 1) (R 1) [22,96,136,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2220
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2221 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 140 296 144 115 83 211 339), lower := (rows 23 98 140 296 144 32 64 128 256), losses := [] }

theorem u2221 : Upper (D 1) (R 1) [22,96,136,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2222 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 23 98 261 138 24 240 240 240 496), lower := (rows 23 98 261 138 24 32 64 128 256), losses := [] }

theorem u2222 : Upper (D 1) (R 1) [22,96,257,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2222
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 261 138 48 248 216 216 472), lower := (rows 23 98 261 138 48 32 64 128 256), losses := [] }

theorem u2223 : Upper (D 1) (R 1) [22,96,257,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2223
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2224 : Route 9 := (fun mask => (mask,id))

def c2224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2224 : Upper (D 1) (R 1) [22,96,257,130,128] 13 := by
  apply FastRouting.sound _ _ [22,96,257,130,128] 13 (by decide) (choices 1) [8,16,64] r2224 c2224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u415
  · exact u416
  · exact u417

def b2225 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 261 168 18 248 216 216 472), lower := (rows 23 98 261 168 18 32 64 128 256), losses := [] }

theorem u2225 : Upper (D 1) (R 1) [22,96,257,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2225
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2226 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 98 261 168 24 242 210 210 466), lower := (rows 23 98 261 168 24 32 64 128 256), losses := [] }

theorem u2226 : Upper (D 1) (R 1) [22,96,257,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2226
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2227 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 261 168 80 186 218 154 410), lower := (rows 23 98 261 168 80 32 64 128 256), losses := [] }

theorem u2227 : Upper (D 1) (R 1) [22,96,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2227
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2228 : Route 9 := (fun mask => (mask,id))

def c2228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2228 : Upper (D 1) (R 1) [22,96,257,160,128] 13 := by
  apply FastRouting.sound _ _ [22,96,257,160,128] 13 (by decide) (choices 1) [2,8,16,64] r2228 c2228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u418
  · exact u419
  · exact u420
  · exact u421

def b2229 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 268 137 18 240 240 240 496), lower := (rows 23 98 268 137 18 32 64 128 256), losses := [] }

theorem u2229 : Upper (D 1) (R 1) [22,96,264,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2229
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2230 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 268 137 48 242 210 210 466), lower := (rows 23 98 268 137 48 32 64 128 256), losses := [] }

theorem u2230 : Upper (D 1) (R 1) [22,96,264,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2230
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2231 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 268 137 144 114 114 242 370), lower := (rows 23 98 268 137 144 32 64 128 256), losses := [] }

theorem u2231 : Upper (D 1) (R 1) [22,96,264,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2231
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2232 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 23 98 268 138 17 240 240 240 496), lower := (rows 23 98 268 138 17 32 64 128 256), losses := [] }

theorem u2232 : Upper (D 1) (R 1) [22,96,264,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2232
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2233 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 268 138 48 241 209 209 465), lower := (rows 23 98 268 138 48 32 64 128 256), losses := [] }

theorem u2233 : Upper (D 1) (R 1) [22,96,264,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2233
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2234 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 268 138 144 113 113 241 369), lower := (rows 23 98 268 138 144 32 64 128 256), losses := [] }

theorem u2234 : Upper (D 1) (R 1) [22,96,264,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2234
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2235 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 98 268 168 17 242 210 210 466), lower := (rows 23 98 268 168 17 32 64 128 256), losses := [] }

theorem u2235 : Upper (D 1) (R 1) [22,96,264,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2235
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2236 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 268 168 18 241 209 209 465), lower := (rows 23 98 268 168 18 32 64 128 256), losses := [] }

theorem u2236 : Upper (D 1) (R 1) [22,96,264,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2236
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2237 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 268 168 80 179 211 147 403), lower := (rows 23 98 268 168 80 32 64 128 256), losses := [] }

theorem u2237 : Upper (D 1) (R 1) [22,96,264,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2237
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2238 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 268 168 144 115 83 211 339), lower := (rows 23 98 268 168 144 32 64 128 256), losses := [] }

theorem u2238 : Upper (D 1) (R 1) [22,96,264,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2239 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 388 41 18 248 216 216 472), lower := (rows 23 98 388 41 18 32 64 128 256), losses := [] }

theorem u2239 : Upper (D 1) (R 1) [22,96,384,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2239
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2240 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 98 388 41 24 242 210 210 466), lower := (rows 23 98 388 41 24 32 64 128 256), losses := [] }

theorem u2240 : Upper (D 1) (R 1) [22,96,384,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2241 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 388 41 80 186 218 154 410), lower := (rows 23 98 388 41 80 32 64 128 256), losses := [] }

theorem u2241 : Upper (D 1) (R 1) [22,96,384,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2241
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2242 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 388 41 144 122 90 218 346), lower := (rows 23 98 388 41 144 32 64 128 256), losses := [] }

theorem u2242 : Upper (D 1) (R 1) [22,96,384,33,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2242
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2243 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 23 98 388 56 17 234 202 202 458), lower := (rows 23 98 388 56 17 32 64 128 256), losses := [] }

theorem u2243 : Upper (D 1) (R 1) [22,96,384,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2244 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 388 56 18 233 201 201 457), lower := (rows 23 98 388 56 18 32 64 128 256), losses := [] }

theorem u2244 : Upper (D 1) (R 1) [22,96,384,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2245 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 23 98 388 56 24 227 195 195 451), lower := (rows 23 98 388 56 24 32 64 128 256), losses := [] }

theorem u2245 : Upper (D 1) (R 1) [22,96,384,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2245
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2246 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 388 56 80 171 203 139 395), lower := (rows 23 98 388 56 80 32 64 128 256), losses := [] }

theorem u2246 : Upper (D 1) (R 1) [22,96,384,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2246
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2247 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 388 56 144 107 75 203 331), lower := (rows 23 98 388 56 144 32 64 128 256), losses := [] }

theorem u2247 : Upper (D 1) (R 1) [22,96,384,48,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2247
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2248 : PairBound 9 := { available := 120, camps := [], pairs := [], upper := (rows 23 98 388 138 17 120 120 248 376), lower := (rows 23 98 388 138 17 32 64 128 256), losses := [] }

theorem u2248 : Upper (D 1) (R 1) [22,96,384,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2248
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2249 : PairBound 9 := { available := 113, camps := [], pairs := [], upper := (rows 23 98 388 138 24 113 113 241 369), lower := (rows 23 98 388 138 24 32 64 128 256), losses := [] }

theorem u2249 : Upper (D 1) (R 1) [22,96,384,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2249
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2250 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 388 138 48 121 89 217 345), lower := (rows 23 98 388 138 48 32 64 128 256), losses := [] }

theorem u2250 : Upper (D 1) (R 1) [22,96,384,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2250
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2251 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 23 98 388 152 17 106 106 234 362), lower := (rows 23 98 388 152 17 32 64 128 256), losses := [] }

theorem u2251 : Upper (D 1) (R 1) [22,96,384,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2251
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2252 : PairBound 9 := { available := 105, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 388 152 18 105 105 233 361), lower := (rows 23 98 388 152 18 32 64 128 256), losses := [] }

theorem u2252 : Upper (D 1) (R 1) [22,96,384,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2253 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 23 98 388 152 24 99 99 227 355), lower := (rows 23 98 388 152 24 32 64 128 256), losses := [] }

theorem u2253 : Upper (D 1) (R 1) [22,96,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2254 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 388 152 48 107 75 203 331), lower := (rows 23 98 388 152 48 32 64 128 256), losses := [] }

theorem u2254 : Upper (D 1) (R 1) [22,96,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2255 : PairBound 9 := { available := 90, camps := [], pairs := [], upper := (rows 23 98 388 168 17 122 90 218 346), lower := (rows 23 98 388 168 17 32 64 128 256), losses := [] }

theorem u2255 : Upper (D 1) (R 1) [22,96,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2255
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2256 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 388 168 18 121 89 217 345), lower := (rows 23 98 388 168 18 32 64 128 256), losses := [] }

theorem u2256 : Upper (D 1) (R 1) [22,96,384,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2256
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2257 : PairBound 9 := { available := 83, camps := [], pairs := [], upper := (rows 23 98 388 168 24 115 83 211 339), lower := (rows 23 98 388 168 24 32 64 128 256), losses := [] }

theorem u2257 : Upper (D 1) (R 1) [22,96,384,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2257
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2258 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 388 168 80 59 91 155 283), lower := (rows 23 98 388 168 80 32 64 128 256), losses := [] }

theorem u2258 : Upper (D 1) (R 1) [22,96,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2258
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2259 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 44 200 18 240 240 240 496), lower := (rows 23 259 44 200 18 32 64 128 256), losses := [] }

theorem u2259 : Upper (D 1) (R 1) [22,257,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2259
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2260 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 23 259 44 200 48 242 210 210 466), lower := (rows 23 259 44 200 48 32 64 128 256), losses := [] }

theorem u2260 : Upper (D 1) (R 1) [22,257,40,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2260
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2261 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 259 44 200 80 178 242 178 434), lower := (rows 23 259 44 200 80 32 64 128 256), losses := [] }

theorem u2261 : Upper (D 1) (R 1) [22,257,40,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2261
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2262 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 100 56 18 232 200 200 456), lower := (rows 23 259 100 56 18 32 64 128 256), losses := [] }

theorem u2262 : Upper (D 1) (R 1) [22,257,96,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2262
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2263 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 23 259 100 56 24 226 194 194 450), lower := (rows 23 259 100 56 24 32 64 128 256), losses := [] }

theorem u2263 : Upper (D 1) (R 1) [22,257,96,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 259 100 56 80 170 202 138 394), lower := (rows 23 259 100 56 80 32 64 128 256), losses := [] }

theorem u2264 : Upper (D 1) (R 1) [22,257,96,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2265 : Route 9 := (fun mask => (mask,id))

def c2265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2265 : Upper (D 1) (R 1) [22,257,96,48,128] 13 := by
  apply FastRouting.sound _ _ [22,257,96,48,128] 13 (by decide) (choices 1) [2,8,64,128] r2265 c2265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u422
  · exact u423
  · exact u424
  · exact u425

def b2266 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 100 152 18 232 232 232 488), lower := (rows 23 259 100 152 18 32 64 128 256), losses := [] }

theorem u2266 : Upper (D 1) (R 1) [22,257,96,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2266
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2267 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 23 259 100 152 24 226 226 226 482), lower := (rows 23 259 100 152 24 32 64 128 256), losses := [] }

theorem u2267 : Upper (D 1) (R 1) [22,257,96,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2267
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2268 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 23 259 100 152 48 234 202 202 458), lower := (rows 23 259 100 152 48 32 64 128 256), losses := [] }

theorem u2268 : Upper (D 1) (R 1) [22,257,96,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2268
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 23 259 100 152 144 106 106 234 362), lower := (rows 23 259 100 152 144 32 64 128 256), losses := [] }

theorem u2269 : Upper (D 1) (R 1) [22,257,96,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2269
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2270 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 100 168 18 248 216 216 472), lower := (rows 23 259 100 168 18 32 64 128 256), losses := [] }

theorem u2270 : Upper (D 1) (R 1) [22,257,96,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2270
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2271 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 259 100 168 24 242 210 210 466), lower := (rows 23 259 100 168 24 32 64 128 256), losses := [] }

theorem u2271 : Upper (D 1) (R 1) [22,257,96,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2271
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2272 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 259 100 168 80 186 218 154 410), lower := (rows 23 259 100 168 80 32 64 128 256), losses := [] }

theorem u2272 : Upper (D 1) (R 1) [22,257,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2272
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2273 : Route 9 := (fun mask => (mask,id))

def c2273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2273 : Upper (D 1) (R 1) [22,257,96,160,128] 13 := by
  apply FastRouting.sound _ _ [22,257,96,160,128] 13 (by decide) (choices 1) [2,8,16,64] r2273 c2273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u426
  · exact u427
  · exact u428
  · exact u429

def b2274 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 266 37 200 18 240 240 240 496), lower := (rows 23 266 37 200 18 32 64 128 256), losses := [] }

theorem u2274 : Upper (D 1) (R 1) [22,264,33,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2275 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 23 266 37 200 48 242 210 210 466), lower := (rows 23 266 37 200 48 32 64 128 256), losses := [] }

theorem u2275 : Upper (D 1) (R 1) [22,264,33,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2275
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2276 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 23 266 37 200 80 178 242 178 434), lower := (rows 23 266 37 200 80 32 64 128 256), losses := [] }

theorem u2276 : Upper (D 1) (R 1) [22,264,33,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2276
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2277 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 266 100 137 18 240 240 240 496), lower := (rows 23 266 100 137 18 32 64 128 256), losses := [] }

theorem u2277 : Upper (D 1) (R 1) [22,264,96,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2277
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 23 266 100 137 48 242 210 210 466), lower := (rows 23 266 100 137 48 32 64 128 256), losses := [] }

theorem u2278 : Upper (D 1) (R 1) [22,264,96,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2278
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2279 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 23 266 100 137 144 114 114 242 370), lower := (rows 23 266 100 137 144 32 64 128 256), losses := [] }

theorem u2279 : Upper (D 1) (R 1) [22,264,96,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2279
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2279
end Delivery.IrregularNine14.P01
