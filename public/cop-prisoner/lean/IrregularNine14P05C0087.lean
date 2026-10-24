import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0032

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5220 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 138 49 300 332 396 268), lower := (rows 7 19 100 138 49 32 64 128 256), losses := [] }

theorem u5220 : Upper (D 5) (R 5) [6,17,96,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5220
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5221 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 138 52 297 329 393 265), lower := (rows 7 19 100 138 52 32 64 128 256), losses := [] }

theorem u5221 : Upper (D 5) (R 5) [6,17,96,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5221
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5222 : Route 9 := (fun mask => (mask,id))

def c5222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5222 : Upper (D 5) (R 5) [6,17,96,130,40] 13 := by
  apply FastRouting.sound _ _ [6,17,96,130,40] 13 (by decide) (choices 1) [1,4,8,256] r5222 c5222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1933
  · exact u1934
  · exact u1935
  · exact u1936

def b5223 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 138 273 44 108 172 300), lower := (rows 7 19 100 138 273 32 64 128 256), losses := [] }

theorem u5223 : Upper (D 5) (R 5) [6,17,96,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5223
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5224 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 138 276 41 105 169 297), lower := (rows 7 19 100 138 276 32 64 128 256), losses := [] }

theorem u5224 : Upper (D 5) (R 5) [6,17,96,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5224
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5225 : Route 9 := (fun mask => (mask,id))

def c5225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5225 : Upper (D 5) (R 5) [6,17,96,130,264] 13 := by
  apply FastRouting.sound _ _ [6,17,96,130,264] 13 (by decide) (choices 1) [1,4,8] r5225 c5225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1937
  · exact u1938
  · exact u1939

def r5226 : Route 9 := (fun mask => (mask,id))

def c5226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5226 : Upper (D 5) (R 5) [6,17,96,130,288] 13 := by
  apply FastRouting.sound _ _ [6,17,96,130,288] 13 (by decide) (choices 1) [1,4,8] r5226 c5226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1940
  · exact u1941
  · exact u1942

def b5227 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 140 19 296 360 424 296), lower := (rows 7 19 100 140 19 32 64 128 256), losses := [] }

theorem u5227 : Upper (D 5) (R 5) [6,17,96,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5228 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 100 140 25 298 362 426 298), lower := (rows 7 19 100 140 25 32 64 128 256), losses := [] }

theorem u5228 : Upper (D 5) (R 5) [6,17,96,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5228
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5229 : PairBound 9 := { available := 297, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 100 140 26 297 361 425 297), lower := (rows 7 19 100 140 26 32 64 128 256), losses := [] }

theorem u5229 : Upper (D 5) (R 5) [6,17,96,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5229
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5230 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 140 49 298 330 394 266), lower := (rows 7 19 100 140 49 32 64 128 256), losses := [] }

theorem u5230 : Upper (D 5) (R 5) [6,17,96,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5231 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 140 50 297 329 393 265), lower := (rows 7 19 100 140 50 32 64 128 256), losses := [] }

theorem u5231 : Upper (D 5) (R 5) [6,17,96,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5231
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5232 : Route 9 := (fun mask => (mask,id))

def c5232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5232 : Upper (D 5) (R 5) [6,17,96,132,40] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,40] 13 (by decide) (choices 1) [1,2,8,256] r5232 c5232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1943
  · exact u1944
  · exact u1945
  · exact u1946

def b5233 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 140 273 42 106 170 298), lower := (rows 7 19 100 140 273 32 64 128 256), losses := [] }

theorem u5233 : Upper (D 5) (R 5) [6,17,96,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5233
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5234 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 100 140 274 41 105 169 297), lower := (rows 7 19 100 140 274 32 64 128 256), losses := [] }

theorem u5234 : Upper (D 5) (R 5) [6,17,96,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5234
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5235 : Route 9 := (fun mask => (mask,id))

def c5235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5235 : Upper (D 5) (R 5) [6,17,96,132,264] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,264] 13 (by decide) (choices 1) [1,2,8] r5235 c5235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1947
  · exact u1948
  · exact u1949

def r5236 : Route 9 := (fun mask => (mask,id))

def c5236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5236 : Upper (D 5) (R 5) [6,17,96,132,288] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,288] 13 (by decide) (choices 1) [1,2,8] r5236 c5236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1950
  · exact u1951
  · exact u1952

def b5237 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 168 19 300 332 396 268), lower := (rows 7 19 100 168 19 32 64 128 256), losses := [] }

theorem u5237 : Upper (D 5) (R 5) [6,17,96,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5238 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 168 21 298 330 394 266), lower := (rows 7 19 100 168 21 32 64 128 256), losses := [] }

theorem u5238 : Upper (D 5) (R 5) [6,17,96,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5238
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5239 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 168 22 297 329 393 265), lower := (rows 7 19 100 168 22 32 64 128 256), losses := [] }

theorem u5239 : Upper (D 5) (R 5) [6,17,96,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5239
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5240 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 168 25 302 334 398 270), lower := (rows 7 19 100 168 25 32 64 128 256), losses := [] }

theorem u5240 : Upper (D 5) (R 5) [6,17,96,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5240
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5241 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 100 168 26 301 333 397 269), lower := (rows 7 19 100 168 26 32 64 128 256), losses := [] }

theorem u5241 : Upper (D 5) (R 5) [6,17,96,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5241
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5242 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 168 28 299 331 395 267), lower := (rows 7 19 100 168 28 32 64 128 256), losses := [] }

theorem u5242 : Upper (D 5) (R 5) [6,17,96,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5242
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5243 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 168 273 46 78 142 270), lower := (rows 7 19 100 168 273 32 64 128 256), losses := [] }

theorem u5243 : Upper (D 5) (R 5) [6,17,96,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5243
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5244 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 100 168 274 45 77 141 269), lower := (rows 7 19 100 168 274 32 64 128 256), losses := [] }

theorem u5244 : Upper (D 5) (R 5) [6,17,96,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5244
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5245 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 168 276 43 75 139 267), lower := (rows 7 19 100 168 276 32 64 128 256), losses := [] }

theorem u5245 : Upper (D 5) (R 5) [6,17,96,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5245
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5246 : Route 9 := (fun mask => (mask,id))

def c5246 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5246 : Upper (D 5) (R 5) [6,17,96,160,264] 13 := by
  apply FastRouting.sound _ _ [6,17,96,160,264] 13 (by decide) (choices 1) [1,2,4,8] r5246 c5246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1953
  · exact u1954
  · exact u1955
  · exact u1956

def b5247 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 392 19 44 108 172 300), lower := (rows 7 19 100 392 19 32 64 128 256), losses := [] }

theorem u5247 : Upper (D 5) (R 5) [6,17,96,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5247
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5248 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 392 21 42 106 170 298), lower := (rows 7 19 100 392 21 32 64 128 256), losses := [] }

theorem u5248 : Upper (D 5) (R 5) [6,17,96,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5248
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5249 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 392 22 41 105 169 297), lower := (rows 7 19 100 392 22 32 64 128 256), losses := [] }

theorem u5249 : Upper (D 5) (R 5) [6,17,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5249
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5250 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 392 25 46 110 174 302), lower := (rows 7 19 100 392 25 32 64 128 256), losses := [] }

theorem u5250 : Upper (D 5) (R 5) [6,17,96,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5250
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5251 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 100 392 26 45 109 173 301), lower := (rows 7 19 100 392 26 32 64 128 256), losses := [] }

theorem u5251 : Upper (D 5) (R 5) [6,17,96,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5251
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5252 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 392 28 43 107 171 299), lower := (rows 7 19 100 392 28 32 64 128 256), losses := [] }

theorem u5252 : Upper (D 5) (R 5) [6,17,96,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5252
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5253 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 392 49 46 78 142 270), lower := (rows 7 19 100 392 49 32 64 128 256), losses := [] }

theorem u5253 : Upper (D 5) (R 5) [6,17,96,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5253
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5254 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 392 50 45 77 141 269), lower := (rows 7 19 100 392 50 32 64 128 256), losses := [] }

theorem u5254 : Upper (D 5) (R 5) [6,17,96,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5254
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5255 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 392 52 43 75 139 267), lower := (rows 7 19 100 392 52 32 64 128 256), losses := [] }

theorem u5255 : Upper (D 5) (R 5) [6,17,96,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5255
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5256 : Route 9 := (fun mask => (mask,id))

def c5256 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5256 : Upper (D 5) (R 5) [6,17,96,384,40] 13 := by
  apply FastRouting.sound _ _ [6,17,96,384,40] 13 (by decide) (choices 1) [1,2,4,8] r5256 c5256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1957
  · exact u1958
  · exact u1959
  · exact u1960

def b5257 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 41 22 296 360 424 296), lower := (rows 7 19 196 41 22 32 64 128 256), losses := [] }

theorem u5257 : Upper (D 5) (R 5) [6,17,192,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5257
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5258 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 196 41 26 300 364 428 300), lower := (rows 7 19 196 41 26 32 64 128 256), losses := [] }

theorem u5258 : Upper (D 5) (R 5) [6,17,192,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5258
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5259 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 41 28 298 362 426 298), lower := (rows 7 19 196 41 28 32 64 128 256), losses := [] }

theorem u5259 : Upper (D 5) (R 5) [6,17,192,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5259
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5260 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 196 41 50 300 332 396 268), lower := (rows 7 19 196 41 50 32 64 128 256), losses := [] }

theorem u5260 : Upper (D 5) (R 5) [6,17,192,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5260
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5261 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 41 52 298 330 394 266), lower := (rows 7 19 196 41 52 32 64 128 256), losses := [] }

theorem u5261 : Upper (D 5) (R 5) [6,17,192,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5262 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 41 56 302 334 398 270), lower := (rows 7 19 196 41 56 32 64 128 256), losses := [] }

theorem u5262 : Upper (D 5) (R 5) [6,17,192,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5262
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5263 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 196 41 274 44 108 172 300), lower := (rows 7 19 196 41 274 32 64 128 256), losses := [] }

theorem u5263 : Upper (D 5) (R 5) [6,17,192,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5263
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5264 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 41 276 42 106 170 298), lower := (rows 7 19 196 41 276 32 64 128 256), losses := [] }

theorem u5264 : Upper (D 5) (R 5) [6,17,192,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5265 : Route 9 := (fun mask => (mask,id))

def c5265 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5265 : Upper (D 5) (R 5) [6,17,192,33,264] 13 := by
  apply FastRouting.sound _ _ [6,17,192,33,264] 13 (by decide) (choices 1) [2,4,8] r5265 c5265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1961
  · exact u1962
  · exact u1963

def r5266 : Route 9 := (fun mask => (mask,id))

def c5266 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5266 : Upper (D 5) (R 5) [6,17,192,33,288] 13 := by
  apply FastRouting.sound _ _ [6,17,192,33,288] 13 (by decide) (choices 1) [2,4,8] r5266 c5266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1964
  · exact u1965
  · exact u1966

def b5267 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 42 21 296 360 424 296), lower := (rows 7 19 196 42 21 32 64 128 256), losses := [] }

theorem u5267 : Upper (D 5) (R 5) [6,17,192,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5268 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 42 25 300 364 428 300), lower := (rows 7 19 196 42 25 32 64 128 256), losses := [] }

theorem u5268 : Upper (D 5) (R 5) [6,17,192,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5269 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 42 28 297 361 425 297), lower := (rows 7 19 196 42 28 32 64 128 256), losses := [] }

theorem u5269 : Upper (D 5) (R 5) [6,17,192,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5270 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 19 196 42 49 300 332 396 268), lower := (rows 7 19 196 42 49 32 64 128 256), losses := [] }

theorem u5270 : Upper (D 5) (R 5) [6,17,192,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5271 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 42 52 297 329 393 265), lower := (rows 7 19 196 42 52 32 64 128 256), losses := [] }

theorem u5271 : Upper (D 5) (R 5) [6,17,192,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5272 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 42 56 301 333 397 269), lower := (rows 7 19 196 42 56 32 64 128 256), losses := [] }

theorem u5272 : Upper (D 5) (R 5) [6,17,192,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5272
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5273 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 42 273 44 108 172 300), lower := (rows 7 19 196 42 273 32 64 128 256), losses := [] }

theorem u5273 : Upper (D 5) (R 5) [6,17,192,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5273
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5274 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 42 276 41 105 169 297), lower := (rows 7 19 196 42 276 32 64 128 256), losses := [] }

theorem u5274 : Upper (D 5) (R 5) [6,17,192,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5275 : Route 9 := (fun mask => (mask,id))

def c5275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5275 : Upper (D 5) (R 5) [6,17,192,34,264] 13 := by
  apply FastRouting.sound _ _ [6,17,192,34,264] 13 (by decide) (choices 1) [1,4,8] r5275 c5275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1967
  · exact u1968
  · exact u1969

def b5276 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 19 196 42 304 45 77 141 269), lower := (rows 7 19 196 42 304 32 64 128 256), losses := [] }

theorem u5276 : Upper (D 5) (R 5) [6,17,192,34,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5276
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5277 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 44 19 296 360 424 296), lower := (rows 7 19 196 44 19 32 64 128 256), losses := [] }

theorem u5277 : Upper (D 5) (R 5) [6,17,192,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5277
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5278 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 44 25 298 362 426 298), lower := (rows 7 19 196 44 25 32 64 128 256), losses := [] }

theorem u5278 : Upper (D 5) (R 5) [6,17,192,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5278
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5279 : PairBound 9 := { available := 297, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 44 26 297 361 425 297), lower := (rows 7 19 196 44 26 32 64 128 256), losses := [] }

theorem u5279 : Upper (D 5) (R 5) [6,17,192,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5279
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5279
end Delivery.IrregularNine14.P05
