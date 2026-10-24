import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0000

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b300 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 388 168 17 96 89 153 281), lower := (rows 23 98 388 168 17 96 64 128 256), losses := [] }

theorem u300 : Upper (D 0) (R 0) [22,96,384,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b300
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 280 144 33 224 224 480), lower := (rows 51 7 76 280 144 33 64 128 256), losses := [] }

theorem u301 : Upper (D 0) (R 0) [50,5,72,272,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b301
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 280 144 96 225 161 417), lower := (rows 51 7 76 280 144 96 64 128 256), losses := [] }

theorem u302 : Upper (D 0) (R 0) [50,5,72,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b302
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 7 76 280 144 160 97 225 353), lower := (rows 51 7 76 280 144 160 64 128 256), losses := [] }

theorem u303 : Upper (D 0) (R 0) [50,5,72,272,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b303
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 392 17 160 112 240 368), lower := (rows 51 7 76 392 17 160 64 128 256), losses := [] }

theorem u304 : Upper (D 0) (R 0) [50,5,72,384,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b304
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 76 392 48 160 81 209 337), lower := (rows 51 7 76 392 48 160 64 128 256), losses := [] }

theorem u305 : Upper (D 0) (R 0) [50,5,72,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b305
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 392 80 160 113 177 305), lower := (rows 51 7 76 392 80 160 64 128 256), losses := [] }

theorem u306 : Upper (D 0) (R 0) [50,5,72,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b306
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 268 88 144 33 224 224 480), lower := (rows 51 7 268 88 144 33 64 128 256), losses := [] }

theorem u307 : Upper (D 0) (R 0) [50,5,264,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b307
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r308 : Route 9 := (fun mask => (mask,id))

def c308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u308 : Upper (D 0) (R 0) [50,5,264,80,128,64] 13 := by
  apply FastRouting.sound _ _ [50,5,264,80,128,64] 13 (by decide) (choices 1) [1,32,128] r308 c308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25
  · exact u26
  · exact u27

def b309 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 7 268 88 144 160 97 225 353), lower := (rows 51 7 268 88 144 160 64 128 256), losses := [] }

theorem u309 : Upper (D 0) (R 0) [50,5,264,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b309
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 268 200 17 96 240 176 432), lower := (rows 51 7 268 200 17 96 64 128 256), losses := [] }

theorem u310 : Upper (D 0) (R 0) [50,5,264,192,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b310
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 268 200 48 96 209 145 401), lower := (rows 51 7 268 200 48 96 64 128 256), losses := [] }

theorem u311 : Upper (D 0) (R 0) [50,5,264,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b311
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r312 : Route 9 := (fun mask => (mask,id))

def c312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u312 : Upper (D 0) (R 0) [50,5,264,192,64,128] 13 := by
  apply FastRouting.sound _ _ [50,5,264,192,64,128] 13 (by decide) (choices 1) [1,16,32] r312 c312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28
  · exact u29
  · exact u30

def b313 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 324 88 144 33 232 168 424), lower := (rows 51 7 324 88 144 33 64 128 256), losses := [] }

theorem u313 : Upper (D 0) (R 0) [50,5,320,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b313
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 7 324 88 144 40 225 161 417), lower := (rows 51 7 324 88 144 40 64 128 256), losses := [] }

theorem u314 : Upper (D 0) (R 0) [50,5,320,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b314
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 7 324 88 144 160 105 169 297), lower := (rows 51 7 324 88 144 160 64 128 256), losses := [] }

theorem u315 : Upper (D 0) (R 0) [50,5,320,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b315
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 324 200 17 160 120 184 312), lower := (rows 51 7 324 200 17 160 64 128 256), losses := [] }

theorem u316 : Upper (D 0) (R 0) [50,5,320,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b316
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 7 324 200 24 160 113 177 305), lower := (rows 51 7 324 200 24 160 64 128 256), losses := [] }

theorem u317 : Upper (D 0) (R 0) [50,5,320,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b317
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 324 200 48 160 89 153 281), lower := (rows 51 7 324 200 48 160 64 128 256), losses := [] }

theorem u318 : Upper (D 0) (R 0) [50,5,320,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b318
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 14 69 265 48 160 208 208 464), lower := (rows 51 14 69 265 48 160 64 128 256), losses := [] }

theorem u319 : Upper (D 0) (R 0) [50,12,65,257,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b319
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 14 69 265 80 160 240 176 432), lower := (rows 51 14 69 265 80 160 64 128 256), losses := [] }

theorem u320 : Upper (D 0) (R 0) [50,12,65,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b320
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 14 69 265 144 160 112 240 368), lower := (rows 51 14 69 265 144 160 64 128 256), losses := [] }

theorem u321 : Upper (D 0) (R 0) [50,12,65,257,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b321
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 104 144 33 452 388 388), lower := (rows 51 67 28 104 144 33 64 128 256), losses := [] }

theorem u322 : Upper (D 0) (R 0) [50,65,24,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b322
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 51 67 28 104 144 36 449 385 385), lower := (rows 51 67 28 104 144 36 64 128 256), losses := [] }

theorem u323 : Upper (D 0) (R 0) [50,65,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b323
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 28 104 144 160 325 389 261), lower := (rows 51 67 28 104 144 160 64 128 256), losses := [] }

theorem u324 : Upper (D 0) (R 0) [50,65,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b324
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 67 28 104 144 288 197 133 389), lower := (rows 51 67 28 104 144 288 64 128 256), losses := [] }

theorem u325 : Upper (D 0) (R 0) [50,65,24,96,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b325
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 296 144 33 196 196 452), lower := (rows 51 67 28 296 144 33 64 128 256), losses := [] }

theorem u326 : Upper (D 0) (R 0) [50,65,24,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b326
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 51 67 28 296 144 36 193 193 449), lower := (rows 51 67 28 296 144 36 64 128 256), losses := [] }

theorem u327 : Upper (D 0) (R 0) [50,65,24,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b327
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 296 144 96 197 133 389), lower := (rows 51 67 28 296 144 96 64 128 256), losses := [] }

theorem u328 : Upper (D 0) (R 0) [50,65,24,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b328
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 28 296 144 160 69 197 325), lower := (rows 51 67 28 296 144 160 64 128 256), losses := [] }

theorem u329 : Upper (D 0) (R 0) [50,65,24,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b329
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b330 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 328 144 33 228 164 420), lower := (rows 51 67 28 328 144 33 64 128 256), losses := [] }

theorem u330 : Upper (D 0) (R 0) [50,65,24,320,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b330
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 67 28 328 144 36 225 161 417), lower := (rows 51 67 28 328 144 36 64 128 256), losses := [] }

theorem u331 : Upper (D 0) (R 0) [50,65,24,320,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b331
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 28 328 144 160 101 165 293), lower := (rows 51 67 28 328 144 160 64 128 256), losses := [] }

theorem u332 : Upper (D 0) (R 0) [50,65,24,320,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b332
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 76 280 144 33 228 164 420), lower := (rows 51 67 76 280 144 33 64 128 256), losses := [] }

theorem u333 : Upper (D 0) (R 0) [50,65,72,272,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b333
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 67 76 280 144 36 225 161 417), lower := (rows 51 67 76 280 144 36 64 128 256), losses := [] }

theorem u334 : Upper (D 0) (R 0) [50,65,72,272,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b334
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 76 280 144 160 101 165 293), lower := (rows 51 67 76 280 144 160 64 128 256), losses := [] }

theorem u335 : Upper (D 0) (R 0) [50,65,72,272,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b335
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 76 392 17 160 116 180 308), lower := (rows 51 67 76 392 17 160 64 128 256), losses := [] }

theorem u336 : Upper (D 0) (R 0) [50,65,72,384,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b336
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 67 76 392 20 160 113 177 305), lower := (rows 51 67 76 392 20 160 64 128 256), losses := [] }

theorem u337 : Upper (D 0) (R 0) [50,65,72,384,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b337
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 76 392 48 160 85 149 277), lower := (rows 51 67 76 392 48 160 64 128 256), losses := [] }

theorem u338 : Upper (D 0) (R 0) [50,65,72,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b338
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 140 144 33 360 424 296), lower := (rows 51 67 84 140 144 33 64 128 256), losses := [] }

theorem u339 : Upper (D 0) (R 0) [50,65,80,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b339
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 51 67 84 140 144 40 353 417 289), lower := (rows 51 67 84 140 144 40 64 128 256), losses := [] }

theorem u340 : Upper (D 0) (R 0) [50,65,80,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b340
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 67 84 140 144 288 105 169 297), lower := (rows 51 67 84 140 144 288 64 128 256), losses := [] }

theorem u341 : Upper (D 0) (R 0) [50,65,80,132,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b341
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 168 144 33 332 396 268), lower := (rows 51 67 84 168 144 33 64 128 256), losses := [] }

theorem u342 : Upper (D 0) (R 0) [50,65,80,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b342
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 51 67 84 168 144 36 329 393 265), lower := (rows 51 67 84 168 144 36 64 128 256), losses := [] }

theorem u343 : Upper (D 0) (R 0) [50,65,80,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b343
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 51 67 84 168 144 40 325 389 261), lower := (rows 51 67 84 168 144 40 64 128 256), losses := [] }

theorem u344 : Upper (D 0) (R 0) [50,65,80,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b344
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 51 67 84 168 144 288 77 141 269), lower := (rows 51 67 84 168 144 288 64 128 256), losses := [] }

theorem u345 : Upper (D 0) (R 0) [50,65,80,160,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b345
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 268 144 33 232 168 424), lower := (rows 51 67 84 268 144 33 64 128 256), losses := [] }

theorem u346 : Upper (D 0) (R 0) [50,65,80,260,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b346
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 67 84 268 144 40 225 161 417), lower := (rows 51 67 84 268 144 40 64 128 256), losses := [] }

theorem u347 : Upper (D 0) (R 0) [50,65,80,260,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b347
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 84 268 144 160 105 169 297), lower := (rows 51 67 84 268 144 160 64 128 256), losses := [] }

theorem u348 : Upper (D 0) (R 0) [50,65,80,260,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b348
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 296 144 33 204 140 396), lower := (rows 51 67 84 296 144 33 64 128 256), losses := [] }

theorem u349 : Upper (D 0) (R 0) [50,65,80,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b349
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 67 84 296 144 36 201 137 393), lower := (rows 51 67 84 296 144 36 64 128 256), losses := [] }

theorem u350 : Upper (D 0) (R 0) [50,65,80,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b350
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 67 84 296 144 40 197 133 389), lower := (rows 51 67 84 296 144 40 64 128 256), losses := [] }

theorem u351 : Upper (D 0) (R 0) [50,65,80,288,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b351
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 84 296 144 160 77 141 269), lower := (rows 51 67 84 296 144 160 64 128 256), losses := [] }

theorem u352 : Upper (D 0) (R 0) [50,65,80,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b352
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 392 144 33 108 172 300), lower := (rows 51 67 84 392 144 33 64 128 256), losses := [] }

theorem u353 : Upper (D 0) (R 0) [50,65,80,384,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b353
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 67 84 392 144 36 105 169 297), lower := (rows 51 67 84 392 144 36 64 128 256), losses := [] }

theorem u354 : Upper (D 0) (R 0) [50,65,80,384,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b354
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 67 84 392 144 40 101 165 293), lower := (rows 51 67 84 392 144 40 64 128 256), losses := [] }

theorem u355 : Upper (D 0) (R 0) [50,65,80,384,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b355
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 280 144 33 100 228 356), lower := (rows 51 67 140 280 144 33 64 128 256), losses := [] }

theorem u356 : Upper (D 0) (R 0) [50,65,136,272,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b356
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 51 67 140 280 144 36 97 225 353), lower := (rows 51 67 140 280 144 36 64 128 256), losses := [] }

theorem u357 : Upper (D 0) (R 0) [50,65,136,272,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b357
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 140 280 144 96 101 165 293), lower := (rows 51 67 140 280 144 96 64 128 256), losses := [] }

theorem u358 : Upper (D 0) (R 0) [50,65,136,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b358
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 328 17 160 116 180 308), lower := (rows 51 67 140 328 17 160 64 128 256), losses := [] }

theorem u359 : Upper (D 0) (R 0) [50,65,136,320,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b359
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P00
