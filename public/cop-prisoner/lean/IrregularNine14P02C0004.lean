import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0000

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 133 200 24 288 368 432 304), lower := (rows 51 70 133 200 24 288 64 128 256), losses := [] }

theorem u240 : Upper (D 2) (R 2) [50,68,129,192,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b240
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 200 48 288 344 408 280), lower := (rows 51 70 133 200 48 288 64 128 256), losses := [] }

theorem u241 : Upper (D 2) (R 2) [50,68,129,192,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b241
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 133 200 272 288 120 184 312), lower := (rows 51 70 133 200 272 288 64 128 256), losses := [] }

theorem u242 : Upper (D 2) (R 2) [50,68,129,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b242
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 70 133 328 24 288 240 176 432), lower := (rows 51 70 133 328 24 288 64 128 256), losses := [] }

theorem u243 : Upper (D 2) (R 2) [50,68,129,320,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b243
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 328 48 288 216 152 408), lower := (rows 51 70 133 328 48 288 64 128 256), losses := [] }

theorem u244 : Upper (D 2) (R 2) [50,68,129,320,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b244
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 51 70 133 328 144 288 120 184 312), lower := (rows 51 70 133 328 144 288 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 29 16 317 81 0 273), good := (rows 379 110 367 360 376 288 64 0 288) }] }

theorem u245 : Upper (D 2) (R 2) [50,68,129,320,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b245
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 70 133 392 24 288 112 240 368), lower := (rows 51 70 133 392 24 288 64 128 256), losses := [] }

theorem u246 : Upper (D 2) (R 2) [50,68,129,384,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b246
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 133 392 48 288 88 216 344), lower := (rows 51 70 133 392 48 288 64 128 256), losses := [] }

theorem u247 : Upper (D 2) (R 2) [50,68,129,384,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b247
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 133 392 80 288 120 184 312), lower := (rows 51 70 133 392 80 288 64 128 256), losses := [] }

theorem u248 : Upper (D 2) (R 2) [50,68,129,384,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b248
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 88 272 33 480 416 416), lower := (rows 51 70 140 88 272 33 64 128 256), losses := [] }

theorem u249 : Upper (D 2) (R 2) [50,68,136,80,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b249
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7)], upper := (rows 51 70 140 88 272 160 353 417 289), lower := (rows 51 70 140 88 272 160 64 128 256), losses := [] }

theorem u250 : Upper (D 2) (R 2) [50,68,136,80,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b250
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 140 88 272 288 225 161 417), lower := (rows 51 70 140 88 272 288 64 128 256), losses := [] }

theorem u251 : Upper (D 2) (R 2) [50,68,136,80,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b251
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 140 265 48 160 336 464 336), lower := (rows 51 70 140 265 48 160 64 128 256), losses := [] }

theorem u252 : Upper (D 2) (R 2) [50,68,136,257,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b252
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 140 265 80 160 368 432 304), lower := (rows 51 70 140 265 80 160 64 128 256), losses := [] }

theorem u253 : Upper (D 2) (R 2) [50,68,136,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b253
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(1,8),(3,7)], upper := (rows 51 70 140 265 144 288 112 240 368), lower := (rows 51 70 140 265 144 288 64 128 256), losses := [{ target := 8, region := (rows 1 10 12 8 189 32 97 161 0), good := (rows 243 86 158 223 144 240 64 144 0) }] }

theorem u254 : Upper (D 2) (R 2) [50,68,136,257,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b254
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 140 280 144 33 352 480 352), lower := (rows 51 70 140 280 144 33 64 128 256), losses := [] }

theorem u255 : Upper (D 2) (R 2) [50,68,136,272,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b255
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 140 280 144 96 353 417 289), lower := (rows 51 70 140 280 144 96 64 128 256), losses := [] }

theorem u256 : Upper (D 2) (R 2) [50,68,136,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b256
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r257 : Route 9 := (fun mask => (mask,id))

def c257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u257 : Upper (D 2) (R 2) [50,68,136,272,128,256] 13 := by
  apply FastRouting.sound _ _ [50,68,136,272,128,256] 13 (by decide) (choices 1) [1,32] r257 c257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u45
  · exact u46

def b258 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 70 140 328 17 288 240 176 432), lower := (rows 51 70 140 328 17 288 64 128 256), losses := [] }

theorem u258 : Upper (D 2) (R 2) [50,68,136,320,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b258
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 140 328 48 288 209 145 401), lower := (rows 51 70 140 328 48 288 64 128 256), losses := [] }

theorem u259 : Upper (D 2) (R 2) [50,68,136,320,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b259
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7)], upper := (rows 51 70 140 328 144 288 113 177 305), lower := (rows 51 70 140 328 144 288 64 128 256), losses := [] }

theorem u260 : Upper (D 2) (R 2) [50,68,136,320,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b260
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 392, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 148 104 272 33 456 392 392), lower := (rows 51 70 148 104 272 33 64 128 256), losses := [] }

theorem u261 : Upper (D 2) (R 2) [50,68,144,96,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b261
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 104 272 40 449 385 385), lower := (rows 51 70 148 104 272 40 64 128 256), losses := [] }

theorem u262 : Upper (D 2) (R 2) [50,68,144,96,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b262
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 328, targets := 16 },{ cop := 0, region := 328, targets := 128 }], pairs := [(3,4),(3,7)], upper := (rows 51 70 148 104 272 160 329 393 265), lower := (rows 51 70 148 104 272 160 64 128 256), losses := [] }

theorem u263 : Upper (D 2) (R 2) [50,68,144,96,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b263
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 148 104 272 288 201 137 393), lower := (rows 51 70 148 104 272 288 64 128 256), losses := [] }

theorem u264 : Upper (D 2) (R 2) [50,68,144,96,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b264
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 137 272 40 352 480 352), lower := (rows 51 70 148 137 272 40 64 128 256), losses := [] }

theorem u265 : Upper (D 2) (R 2) [50,68,144,129,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b265
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 137 272 96 360 424 296), lower := (rows 51 70 148 137 272 96 64 128 256), losses := [] }

theorem u266 : Upper (D 2) (R 2) [50,68,144,129,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b266
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 148 137 272 288 104 232 360), lower := (rows 51 70 148 137 272 288 64 128 256), losses := [] }

theorem u267 : Upper (D 2) (R 2) [50,68,144,129,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b267
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 342, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 148 168 272 33 328 456 328), lower := (rows 51 70 148 168 272 33 64 128 256), losses := [] }

theorem u268 : Upper (D 2) (R 2) [50,68,144,160,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b268
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 168 272 40 321 449 321), lower := (rows 51 70 148 168 272 40 64 128 256), losses := [] }

theorem u269 : Upper (D 2) (R 2) [50,68,144,160,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b269
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 168 272 96 329 393 265), lower := (rows 51 70 148 168 272 96 64 128 256), losses := [] }

theorem u270 : Upper (D 2) (R 2) [50,68,144,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b270
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 148 168 272 288 73 201 329), lower := (rows 51 70 148 168 272 288 64 128 256), losses := [] }

theorem u271 : Upper (D 2) (R 2) [50,68,144,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b271
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 200 272 33 360 424 296), lower := (rows 51 70 148 200 272 33 64 128 256), losses := [] }

theorem u272 : Upper (D 2) (R 2) [50,68,144,192,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b272
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 200 272 40 353 417 289), lower := (rows 51 70 148 200 272 40 64 128 256), losses := [] }

theorem u273 : Upper (D 2) (R 2) [50,68,144,192,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b273
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 70 148 200 272 288 105 169 297), lower := (rows 51 70 148 200 272 288 64 128 256), losses := [] }

theorem u274 : Upper (D 2) (R 2) [50,68,144,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b274
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 70 148 265 272 40 224 224 480), lower := (rows 51 70 148 265 272 40 64 128 256), losses := [] }

theorem u275 : Upper (D 2) (R 2) [50,68,144,257,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b275
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 265 272 96 232 168 424), lower := (rows 51 70 148 265 272 96 64 128 256), losses := [] }

theorem u276 : Upper (D 2) (R 2) [50,68,144,257,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b276
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 328, targets := 16 },{ cop := 0, region := 328, targets := 128 }], pairs := [(3,4),(3,7)], upper := (rows 51 70 148 265 272 160 104 232 360), lower := (rows 51 70 148 265 272 160 64 128 256), losses := [] }

theorem u277 : Upper (D 2) (R 2) [50,68,144,257,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b277
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 148 296 272 33 200 200 456), lower := (rows 51 70 148 296 272 33 64 128 256), losses := [] }

theorem u278 : Upper (D 2) (R 2) [50,68,144,288,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b278
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 148 296 272 40 193 193 449), lower := (rows 51 70 148 296 272 40 64 128 256), losses := [] }

theorem u279 : Upper (D 2) (R 2) [50,68,144,288,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b279
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 148 296 272 96 201 137 393), lower := (rows 51 70 148 296 272 96 64 128 256), losses := [] }

theorem u280 : Upper (D 2) (R 2) [50,68,144,288,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b280
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 328, targets := 16 },{ cop := 0, region := 328, targets := 128 }], pairs := [(3,4),(3,7)], upper := (rows 51 70 148 296 272 160 73 201 329), lower := (rows 51 70 148 296 272 160 64 128 256), losses := [] }

theorem u281 : Upper (D 2) (R 2) [50,68,144,288,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b281
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 328 272 33 232 168 424), lower := (rows 51 70 148 328 272 33 64 128 256), losses := [] }

theorem u282 : Upper (D 2) (R 2) [50,68,144,320,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b282
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 70 148 328 272 40 225 161 417), lower := (rows 51 70 148 328 272 40 64 128 256), losses := [] }

theorem u283 : Upper (D 2) (R 2) [50,68,144,320,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b283
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 328, targets := 16 },{ cop := 0, region := 328, targets := 128 }], pairs := [(3,4),(3,7)], upper := (rows 51 70 148 328 272 160 105 169 297), lower := (rows 51 70 148 328 272 160 64 128 256), losses := [] }

theorem u284 : Upper (D 2) (R 2) [50,68,144,320,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b284
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 454, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 388 137 24 48 352 480 352), lower := (rows 51 70 388 137 24 48 64 128 256), losses := [] }

theorem u285 : Upper (D 2) (R 2) [50,68,384,129,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b285
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 137 24 96 368 432 304), lower := (rows 51 70 388 137 24 96 64 128 256), losses := [] }

theorem u286 : Upper (D 2) (R 2) [50,68,384,129,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b286
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 200, targets := 256 }], pairs := [(3,8)], upper := (rows 51 70 388 137 24 288 112 240 368), lower := (rows 51 70 388 137 24 288 64 128 256), losses := [] }

theorem u287 : Upper (D 2) (R 2) [50,68,384,129,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b287
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 388 137 48 288 88 216 344), lower := (rows 51 70 388 137 48 288 64 128 256), losses := [] }

theorem u288 : Upper (D 2) (R 2) [50,68,384,129,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b288
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 70 388 137 80 288 120 184 312), lower := (rows 51 70 388 137 80 288 64 128 256), losses := [] }

theorem u289 : Upper (D 2) (R 2) [50,68,384,129,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b289
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 304, camps := [], pairs := [], upper := (rows 51 70 388 200 17 40 368 432 304), lower := (rows 51 70 388 200 17 40 64 128 256), losses := [] }

theorem u290 : Upper (D 2) (R 2) [50,68,384,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b290
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 388 200 17 48 360 424 296), lower := (rows 51 70 388 200 17 48 64 128 256), losses := [] }

theorem u291 : Upper (D 2) (R 2) [50,68,384,192,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b291
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 200, targets := 256 }], pairs := [(3,8)], upper := (rows 51 70 388 200 17 288 120 184 312), lower := (rows 51 70 388 200 17 288 64 128 256), losses := [] }

theorem u292 : Upper (D 2) (R 2) [50,68,384,192,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b292
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 200 24 288 113 177 305), lower := (rows 51 70 388 200 24 288 64 128 256), losses := [] }

theorem u293 : Upper (D 2) (R 2) [50,68,384,192,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b293
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 70 388 200 48 288 89 153 281), lower := (rows 51 70 388 200 48 288 64 128 256), losses := [] }

theorem u294 : Upper (D 2) (R 2) [50,68,384,192,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b294
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 13 76 48 288 464 400 400), lower := (rows 51 194 13 76 48 288 64 128 256), losses := [] }

theorem u295 : Upper (D 2) (R 2) [50,192,9,68,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b295
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 13 76 144 288 368 432 304), lower := (rows 51 194 13 76 144 288 64 128 256), losses := [] }

theorem u296 : Upper (D 2) (R 2) [50,192,9,68,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b296
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 194 13 76 272 288 240 176 432), lower := (rows 51 194 13 76 272 288 64 128 256), losses := [] }

theorem u297 : Upper (D 2) (R 2) [50,192,9,68,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b297
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 88 272 36 480 416 416), lower := (rows 51 194 13 88 272 36 64 128 256), losses := [] }

theorem u298 : Upper (D 2) (R 2) [50,192,9,80,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b298
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 13 88 272 160 356 420 292), lower := (rows 51 194 13 88 272 160 64 128 256), losses := [] }

theorem u299 : Upper (D 2) (R 2) [50,192,9,80,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b299
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P02
