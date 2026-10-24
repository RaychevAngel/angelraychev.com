import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0016
import IrregularNine14P00C0017

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2220 : Route 9 := (fun mask => (mask,id))

def c2220 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2220 : Upper (D 0) (R 0) [304,65,72,144,1] 13 := by
  apply FastRouting.sound _ _ [304,65,72,144,1] 13 (by decide) (choices 1) [2,4,128] r2220 c2220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u976
  · exact u977
  · exact u978

def b2221 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 305 67 76 152 18 165 229 165 421), lower := (rows 305 67 76 152 18 32 64 128 256), losses := [] }

theorem u2221 : Upper (D 0) (R 0) [304,65,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2221
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2222 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 67 76 152 20 163 227 163 419), lower := (rows 305 67 76 152 20 32 64 128 256), losses := [] }

theorem u2222 : Upper (D 0) (R 0) [304,65,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2222
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 76 152 48 167 199 135 391), lower := (rows 305 67 76 152 48 32 64 128 256), losses := [] }

theorem u2223 : Upper (D 0) (R 0) [304,65,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2223
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2224 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 67 76 152 144 39 103 167 295), lower := (rows 305 67 76 152 144 32 64 128 256), losses := [] }

theorem u2224 : Upper (D 0) (R 0) [304,65,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2224
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2225 : PairBound 9 := { available := 172, camps := [], pairs := [], upper := (rows 305 67 84 137 18 172 236 172 428), lower := (rows 305 67 84 137 18 32 64 128 256), losses := [] }

theorem u2225 : Upper (D 0) (R 0) [304,65,80,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2225
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2226 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 67 84 137 20 170 234 170 426), lower := (rows 305 67 84 137 20 32 64 128 256), losses := [] }

theorem u2226 : Upper (D 0) (R 0) [304,65,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2226
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2227 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 305 67 84 137 24 166 230 166 422), lower := (rows 305 67 84 137 24 32 64 128 256), losses := [] }

theorem u2227 : Upper (D 0) (R 0) [304,65,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2227
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2228 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 84 137 48 174 206 142 398), lower := (rows 305 67 84 137 48 32 64 128 256), losses := [] }

theorem u2228 : Upper (D 0) (R 0) [304,65,80,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2228
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2229 : Route 9 := (fun mask => (mask,id))

def c2229 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2229 : Upper (D 0) (R 0) [304,65,80,129,128] 13 := by
  apply FastRouting.sound _ _ [304,65,80,129,128] 13 (by decide) (choices 1) [2,4,8] r2229 c2229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u979
  · exact u980
  · exact u981

def b2230 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 84 138 17 172 236 172 428), lower := (rows 305 67 84 138 17 32 64 128 256), losses := [] }

theorem u2230 : Upper (D 0) (R 0) [304,65,80,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2230
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2231 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 305 67 84 138 20 169 233 169 425), lower := (rows 305 67 84 138 20 32 64 128 256), losses := [] }

theorem u2231 : Upper (D 0) (R 0) [304,65,80,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2231
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2232 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 305 67 84 138 24 165 229 165 421), lower := (rows 305 67 84 138 24 32 64 128 256), losses := [] }

theorem u2232 : Upper (D 0) (R 0) [304,65,80,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2232
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2233 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 84 138 48 173 205 141 397), lower := (rows 305 67 84 138 48 32 64 128 256), losses := [] }

theorem u2233 : Upper (D 0) (R 0) [304,65,80,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2233
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2234 : Route 9 := (fun mask => (mask,id))

def c2234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2234 : Upper (D 0) (R 0) [304,65,80,130,128] 13 := by
  apply FastRouting.sound _ _ [304,65,80,130,128] 13 (by decide) (choices 1) [1,4,8] r2234 c2234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u982
  · exact u983
  · exact u984

def b2235 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 84 140 17 170 234 170 426), lower := (rows 305 67 84 140 17 32 64 128 256), losses := [] }

theorem u2235 : Upper (D 0) (R 0) [304,65,80,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2235
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2236 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 305 67 84 140 18 169 233 169 425), lower := (rows 305 67 84 140 18 32 64 128 256), losses := [] }

theorem u2236 : Upper (D 0) (R 0) [304,65,80,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2236
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2237 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 67 84 140 24 163 227 163 419), lower := (rows 305 67 84 140 24 32 64 128 256), losses := [] }

theorem u2237 : Upper (D 0) (R 0) [304,65,80,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2237
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2238 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 84 140 48 171 203 139 395), lower := (rows 305 67 84 140 48 32 64 128 256), losses := [] }

theorem u2238 : Upper (D 0) (R 0) [304,65,80,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2238
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2239 : Route 9 := (fun mask => (mask,id))

def c2239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2239 : Upper (D 0) (R 0) [304,65,80,132,128] 13 := by
  apply FastRouting.sound _ _ [304,65,80,132,128] 13 (by decide) (choices 1) [1,2,8] r2239 c2239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u985
  · exact u986
  · exact u987

def b2240 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 84 168 17 174 206 142 398), lower := (rows 305 67 84 168 17 32 64 128 256), losses := [] }

theorem u2240 : Upper (D 0) (R 0) [304,65,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2240
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2241 : PairBound 9 := { available := 141, camps := [], pairs := [], upper := (rows 305 67 84 168 18 173 205 141 397), lower := (rows 305 67 84 168 18 32 64 128 256), losses := [] }

theorem u2241 : Upper (D 0) (R 0) [304,65,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2241
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2242 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 305 67 84 168 20 171 203 139 395), lower := (rows 305 67 84 168 20 32 64 128 256), losses := [] }

theorem u2242 : Upper (D 0) (R 0) [304,65,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2242
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2243 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 305 67 84 168 24 167 199 135 391), lower := (rows 305 67 84 168 24 32 64 128 256), losses := [] }

theorem u2243 : Upper (D 0) (R 0) [304,65,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2243
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2244 : Route 9 := (fun mask => (mask,id))

def c2244 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2244 : Upper (D 0) (R 0) [304,65,80,160,128] 13 := by
  apply FastRouting.sound _ _ [304,65,80,160,128] 13 (by decide) (choices 1) [1,2,4,8] r2244 c2244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u988
  · exact u989
  · exact u990
  · exact u991

def b2245 : PairBound 9 := { available := 60, camps := [], pairs := [], upper := (rows 305 67 133 200 18 60 124 188 316), lower := (rows 305 67 133 200 18 32 64 128 256), losses := [] }

theorem u2245 : Upper (D 0) (R 0) [304,65,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2245
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2246 : PairBound 9 := { available := 54, camps := [], pairs := [], upper := (rows 305 67 133 200 24 54 118 182 310), lower := (rows 305 67 133 200 24 32 64 128 256), losses := [] }

theorem u2246 : Upper (D 0) (R 0) [304,65,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2246
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2247 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 133 200 48 62 94 158 286), lower := (rows 305 67 133 200 48 32 64 128 256), losses := [] }

theorem u2247 : Upper (D 0) (R 0) [304,65,129,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2247
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2248 : PairBound 9 := { available := 108, camps := [], pairs := [(3,5)], upper := (rows 305 67 134 152 17 108 108 236 364), lower := (rows 305 67 134 152 17 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 19 0 64 128 256), good := (rows 273 83 158 152 17 0 64 128 256) }] }

theorem u2248 : Upper (D 0) (R 0) [304,65,130,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2248
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2249 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 305 67 134 152 20 105 105 233 361), lower := (rows 305 67 134 152 20 32 64 128 256), losses := [] }

theorem u2249 : Upper (D 0) (R 0) [304,65,130,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2249
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2250 : PairBound 9 := { available := 101, camps := [], pairs := [], upper := (rows 305 67 134 152 24 101 101 229 357), lower := (rows 305 67 134 152 24 32 64 128 256), losses := [] }

theorem u2250 : Upper (D 0) (R 0) [304,65,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2250
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2251 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 134 152 48 109 77 205 333), lower := (rows 305 67 134 152 48 32 64 128 256), losses := [] }

theorem u2251 : Upper (D 0) (R 0) [304,65,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2251
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2252 : PairBound 9 := { available := 45, camps := [], pairs := [(3,0)], upper := (rows 305 67 134 152 80 45 109 173 301), lower := (rows 305 67 134 152 80 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 82 32 64 128 256), good := (rows 304 82 158 152 80 32 80 128 256) }] }

theorem u2252 : Upper (D 0) (R 0) [304,65,130,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2252
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2253 : Route 9 := (fun mask => (mask,id))

def c2253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2253 : Upper (D 0) (R 0) [304,65,130,192,1] 13 := by
  apply FastRouting.sound _ _ [304,65,130,192,1] 13 (by decide) (choices 1) [4,8,16] r2253 c2253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u992
  · exact u993
  · exact u994

def b2254 : PairBound 9 := { available := 57, camps := [], pairs := [], upper := (rows 305 67 134 200 20 57 121 185 313), lower := (rows 305 67 134 200 20 32 64 128 256), losses := [] }

theorem u2254 : Upper (D 0) (R 0) [304,65,130,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2254
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2255 : PairBound 9 := { available := 53, camps := [], pairs := [], upper := (rows 305 67 134 200 24 53 117 181 309), lower := (rows 305 67 134 200 24 32 64 128 256), losses := [] }

theorem u2255 : Upper (D 0) (R 0) [304,65,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2255
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2256 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 134 200 48 61 93 157 285), lower := (rows 305 67 134 200 48 32 64 128 256), losses := [] }

theorem u2256 : Upper (D 0) (R 0) [304,65,130,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2256
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2257 : Route 9 := (fun mask => (mask,id))

def c2257 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2257 : Upper (D 0) (R 0) [304,65,144,160,1] 13 := by
  apply FastRouting.sound _ _ [304,65,144,160,1] 13 (by decide) (choices 1) [2,4,8,64] r2257 c2257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u995
  · exact u996
  · exact u997
  · exact u998

def b2258 : PairBound 9 := { available := 77, camps := [], pairs := [], upper := (rows 305 67 148 168 18 109 77 205 333), lower := (rows 305 67 148 168 18 32 64 128 256), losses := [] }

theorem u2258 : Upper (D 0) (R 0) [304,65,144,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2258
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2259 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 305 67 148 168 20 107 75 203 331), lower := (rows 305 67 148 168 20 32 64 128 256), losses := [] }

theorem u2259 : Upper (D 0) (R 0) [304,65,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2259
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2260 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 305 67 148 168 24 103 71 199 327), lower := (rows 305 67 148 168 24 32 64 128 256), losses := [] }

theorem u2260 : Upper (D 0) (R 0) [304,65,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2260
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m2261_1 : Upper (D 0) (R 0) [304,65,144,160,64,1] 13 :=
  permutation_upper _ _ _ [304,65,144,160,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u998

theorem m2261_2 : Upper (D 0) (R 0) [304,65,144,160,64,2] 13 :=
  permutation_upper _ _ _ [304,65,144,160,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u999

theorem m2261_4 : Upper (D 0) (R 0) [304,65,144,160,64,4] 13 :=
  permutation_upper _ _ _ [304,65,144,160,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1001

theorem m2261_8 : Upper (D 0) (R 0) [304,65,144,160,64,8] 13 :=
  permutation_upper _ _ _ [304,65,144,160,4,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1000

def r2261 : Route 9 := (fun mask => (mask,id))

def c2261 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2261 : Upper (D 0) (R 0) [304,65,144,160,64] 13 := by
  apply FastRouting.sound _ _ [304,65,144,160,64] 13 (by decide) (choices 1) [1,2,4,8] r2261 c2261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2261_1
  · exact m2261_2
  · exact m2261_4
  · exact m2261_8

def r2262 : Route 9 := (fun mask => (mask,id))

def c2262 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2262 : Upper (D 0) (R 0) [304,65,144,192,1] 13 := by
  apply FastRouting.sound _ _ [304,65,144,192,1] 13 (by decide) (choices 1) [2,4,8] r2262 c2262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1002
  · exact u1003
  · exact u1004

def b2263 : PairBound 9 := { available := 45, camps := [], pairs := [], upper := (rows 305 67 148 200 18 45 109 173 301), lower := (rows 305 67 148 200 18 32 64 128 256), losses := [] }

theorem u2263 : Upper (D 0) (R 0) [304,65,144,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2263
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 43, camps := [], pairs := [], upper := (rows 305 67 148 200 20 43 107 171 299), lower := (rows 305 67 148 200 20 32 64 128 256), losses := [] }

theorem u2264 : Upper (D 0) (R 0) [304,65,144,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2264
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2265 : PairBound 9 := { available := 39, camps := [], pairs := [], upper := (rows 305 67 148 200 24 39 103 167 295), lower := (rows 305 67 148 200 24 32 64 128 256), losses := [] }

theorem u2265 : Upper (D 0) (R 0) [304,65,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2265
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2266 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 148 200 48 47 79 143 271), lower := (rows 305 67 148 200 48 32 64 128 256), losses := [] }

theorem u2266 : Upper (D 0) (R 0) [304,65,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2266
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2267 : Route 9 := (fun mask => (mask,id))

def c2267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2267 : Upper (D 0) (R 0) [304,68,144,96,1] 13 := by
  apply FastRouting.sound _ _ [304,68,144,96,1] 13 (by decide) (choices 1) [1,2,8,128] r2267 c2267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1005
  · exact u1006
  · exact u1007
  · exact u1008

def b2268 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 70 148 104 18 169 201 137 393), lower := (rows 305 70 148 104 18 32 64 128 256), losses := [] }

theorem u2268 : Upper (D 0) (R 0) [304,68,144,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2268
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 70 148 104 24 163 195 131 387), lower := (rows 305 70 148 104 24 32 64 128 256), losses := [] }

theorem u2269 : Upper (D 0) (R 0) [304,68,144,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2269
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2270 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 104 144 43 75 139 267), lower := (rows 305 70 148 104 144 32 64 128 256), losses := [] }

theorem u2270 : Upper (D 0) (R 0) [304,68,144,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2270
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2271 : Route 9 := (fun mask => (mask,id))

def c2271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2271 : Upper (D 0) (R 0) [304,68,144,160,1] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160,1] 13 (by decide) (choices 1) [1,2,8,64] r2271 c2271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1009
  · exact u1010
  · exact u1011
  · exact u1012

def b2272 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 305 70 148 168 18 105 73 201 329), lower := (rows 305 70 148 168 18 32 64 128 256), losses := [] }

theorem u2272 : Upper (D 0) (R 0) [304,68,144,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2272
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2273 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 70 148 168 24 99 67 195 323), lower := (rows 305 70 148 168 24 32 64 128 256), losses := [] }

theorem u2273 : Upper (D 0) (R 0) [304,68,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2273
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2274 : Route 9 := (fun mask => (mask,id))

def c2274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2274 : Upper (D 0) (R 0) [304,68,144,160,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160,64] 13 (by decide) (choices 1) [1,2,8] r2274 c2274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1013
  · exact u1014
  · exact u1015

def r2275 : Route 9 := (fun mask => (mask,id))

def c2275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2275 : Upper (D 0) (R 0) [304,68,144,192,1] 13 := by
  apply FastRouting.sound _ _ [304,68,144,192,1] 13 (by decide) (choices 1) [1,2,8] r2275 c2275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1016
  · exact u1017
  · exact u1018

def b2276 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 305 70 148 200 18 41 105 169 297), lower := (rows 305 70 148 200 18 32 64 128 256), losses := [] }

theorem u2276 : Upper (D 0) (R 0) [304,68,144,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2276
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2277 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 305 70 148 200 24 35 99 163 291), lower := (rows 305 70 148 200 24 32 64 128 256), losses := [] }

theorem u2277 : Upper (D 0) (R 0) [304,68,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2277
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 148 200 48 43 75 139 267), lower := (rows 305 70 148 200 48 32 64 128 256), losses := [] }

theorem u2278 : Upper (D 0) (R 0) [304,68,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2278
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2279 : Route 9 := (fun mask => (mask,id))

def c2279 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2279 : Upper (D 0) (R 0) [304,80,160,192,1] 13 := by
  apply FastRouting.sound _ _ [304,80,160,192,1] 13 (by decide) (choices 1) [1,2,4,8] r2279 c2279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1019
  · exact u1020
  · exact u1021
  · exact u1022

#print axioms u2279
end Delivery.IrregularNine14.P00
