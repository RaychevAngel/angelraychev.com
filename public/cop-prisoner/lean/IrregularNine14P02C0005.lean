import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0000
import IrregularNine14P02C0001

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b300 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 194 13 88 272 288 228 164 420), lower := (rows 51 194 13 88 272 288 64 128 256), losses := [] }

theorem u300 : Upper (D 2) (R 2) [50,192,9,80,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b300
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 328 20 48 480 416 416), lower := (rows 51 194 13 328 20 48 64 128 256), losses := [] }

theorem u301 : Upper (D 2) (R 2) [50,192,9,320,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b301
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 13 328 20 160 368 432 304), lower := (rows 51 194 13 328 20 160 64 128 256), losses := [] }

theorem u302 : Upper (D 2) (R 2) [50,192,9,320,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b302
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 194, targets := 256 }], pairs := [(1,8)], upper := (rows 51 194 13 328 20 288 240 176 432), lower := (rows 51 194 13 328 20 288 64 128 256), losses := [] }

theorem u303 : Upper (D 2) (R 2) [50,192,9,320,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b303
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 13 328 48 288 212 148 404), lower := (rows 51 194 13 328 48 288 64 128 256), losses := [] }

theorem u304 : Upper (D 2) (R 2) [50,192,9,320,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b304
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 13 328 144 288 116 180 308), lower := (rows 51 194 13 328 144 288 64 128 256), losses := [] }

theorem u305 : Upper (D 2) (R 2) [50,192,9,320,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b305
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 28 104 272 33 452 388 388), lower := (rows 51 194 28 104 272 33 64 128 256), losses := [] }

theorem u306 : Upper (D 2) (R 2) [50,192,24,96,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b306
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 104 272 36 449 385 385), lower := (rows 51 194 28 104 272 36 64 128 256), losses := [] }

theorem u307 : Upper (D 2) (R 2) [50,192,24,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b307
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 28 104 272 160 325 389 261), lower := (rows 51 194 28 104 272 160 64 128 256), losses := [] }

theorem u308 : Upper (D 2) (R 2) [50,192,24,96,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b308
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 194 28 104 272 288 197 133 389), lower := (rows 51 194 28 104 272 288 64 128 256), losses := [] }

theorem u309 : Upper (D 2) (R 2) [50,192,24,96,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b309
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 324, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 69 140 24 288 368 432 304), lower := (rows 51 194 69 140 24 288 64 128 256), losses := [] }

theorem u310 : Upper (D 2) (R 2) [50,192,65,132,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b310
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 69 140 48 288 344 408 280), lower := (rows 51 194 69 140 48 288 64 128 256), losses := [] }

theorem u311 : Upper (D 2) (R 2) [50,192,65,132,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b311
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 194 69 140 272 288 120 184 312), lower := (rows 51 194 69 140 272 288 64 128 256), losses := [] }

theorem u312 : Upper (D 2) (R 2) [50,192,65,132,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b312
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 152 272 36 360 424 296), lower := (rows 51 194 69 152 272 36 64 128 256), losses := [] }

theorem u313 : Upper (D 2) (R 2) [50,192,65,144,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b313
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 454, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 69 152 272 40 356 420 292), lower := (rows 51 194 69 152 272 40 64 128 256), losses := [] }

theorem u314 : Upper (D 2) (R 2) [50,192,65,144,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b314
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 194 69 152 272 288 108 172 300), lower := (rows 51 194 69 152 272 288 64 128 256), losses := [] }

theorem u315 : Upper (D 2) (R 2) [50,192,65,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b315
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 194, targets := 256 }], pairs := [(1,8)], upper := (rows 51 194 69 268 24 288 240 176 432), lower := (rows 51 194 69 268 24 288 64 128 256), losses := [] }

theorem u316 : Upper (D 2) (R 2) [50,192,65,260,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b316
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 69 268 48 288 216 152 408), lower := (rows 51 194 69 268 48 288 64 128 256), losses := [] }

theorem u317 : Upper (D 2) (R 2) [50,192,65,260,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b317
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 69 268 144 288 120 184 312), lower := (rows 51 194 69 268 144 288 64 128 256), losses := [] }

theorem u318 : Upper (D 2) (R 2) [50,192,65,260,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b318
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 392 20 288 120 184 312), lower := (rows 51 194 69 392 20 288 64 128 256), losses := [] }

theorem u319 : Upper (D 2) (R 2) [50,192,65,384,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b319
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 194 69 392 24 288 116 180 308), lower := (rows 51 194 69 392 24 288 64 128 256), losses := [] }

theorem u320 : Upper (D 2) (R 2) [50,192,65,384,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b320
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 69 392 48 288 92 156 284), lower := (rows 51 194 69 392 48 288 64 128 256), losses := [] }

theorem u321 : Upper (D 2) (R 2) [50,192,65,384,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b321
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r322 : Route 9 := (fun mask => (mask,id))

def c322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u322 : Upper (D 2) (R 2) [50,192,72,144,256,1] 13 := by
  apply FastRouting.sound _ _ [50,192,72,144,256,1] 13 (by decide) (choices 1) [4,32,256] r322 c322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u47
  · exact u48
  · exact u49

def b323 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 152 272 36 353 417 289), lower := (rows 51 194 76 152 272 36 64 128 256), losses := [] }

theorem u323 : Upper (D 2) (R 2) [50,192,72,144,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b323
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 194 76 152 272 288 101 165 293), lower := (rows 51 194 76 152 272 288 64 128 256), losses := [] }

theorem u324 : Upper (D 2) (R 2) [50,192,72,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b324
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 76 265 20 288 240 176 432), lower := (rows 51 194 76 265 20 288 64 128 256), losses := [] }

theorem u325 : Upper (D 2) (R 2) [50,192,72,257,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b325
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 76 265 48 288 212 148 404), lower := (rows 51 194 76 265 48 288 64 128 256), losses := [] }

theorem u326 : Upper (D 2) (R 2) [50,192,72,257,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b326
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 76 265 144 288 116 180 308), lower := (rows 51 194 76 265 144 288 64 128 256), losses := [] }

theorem u327 : Upper (D 2) (R 2) [50,192,72,257,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b327
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 304, camps := [], pairs := [], upper := (rows 51 194 76 392 17 36 368 432 304), lower := (rows 51 194 76 392 17 36 64 128 256), losses := [] }

theorem u328 : Upper (D 2) (R 2) [50,192,72,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b328
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 392 17 48 356 420 292), lower := (rows 51 194 76 392 17 48 64 128 256), losses := [] }

theorem u329 : Upper (D 2) (R 2) [50,192,72,384,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b329
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r330 : Route 9 := (fun mask => (mask,id))

def c330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u330 : Upper (D 2) (R 2) [50,192,72,384,1,256] 13 := by
  apply FastRouting.sound _ _ [50,192,72,384,1,256] 13 (by decide) (choices 1) [4,16,32] r330 c330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u50
  · exact u51
  · exact u52

def b331 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 76 392 20 288 113 177 305), lower := (rows 51 194 76 392 20 288 64 128 256), losses := [] }

theorem u331 : Upper (D 2) (R 2) [50,192,72,384,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b331
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 76 392 48 288 85 149 277), lower := (rows 51 194 76 392 48 288 64 128 256), losses := [] }

theorem u332 : Upper (D 2) (R 2) [50,192,72,384,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b332
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 426, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 168 17 288 332 396 268), lower := (rows 51 194 84 168 17 288 64 128 256), losses := [] }

theorem u333 : Upper (D 2) (R 2) [50,192,80,160,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b333
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 84 168 20 288 329 393 265), lower := (rows 51 194 84 168 20 288 64 128 256), losses := [] }

theorem u334 : Upper (D 2) (R 2) [50,192,80,160,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b334
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 168 24 288 325 389 261), lower := (rows 51 194 84 168 24 288 64 128 256), losses := [] }

theorem u335 : Upper (D 2) (R 2) [50,192,80,160,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b335
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 206, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 51 194 84 168 272 288 77 141 269), lower := (rows 51 194 84 168 272 288 64 128 256), losses := [] }

theorem u336 : Upper (D 2) (R 2) [50,192,80,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b336
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 265 272 36 232 168 424), lower := (rows 51 194 84 265 272 36 64 128 256), losses := [] }

theorem u337 : Upper (D 2) (R 2) [50,192,80,257,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b337
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 194 84 265 272 40 228 164 420), lower := (rows 51 194 84 265 272 40 64 128 256), losses := [] }

theorem u338 : Upper (D 2) (R 2) [50,192,80,257,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b338
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 84 265 272 160 108 172 300), lower := (rows 51 194 84 265 272 160 64 128 256), losses := [] }

theorem u339 : Upper (D 2) (R 2) [50,192,80,257,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b339
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r340 : Route 9 := (fun mask => (mask,id))

def c340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u340 : Upper (D 2) (R 2) [50,192,80,260,256,1] 13 := by
  apply FastRouting.sound _ _ [50,192,80,260,256,1] 13 (by decide) (choices 1) [8,32,128] r340 c340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u53
  · exact u54
  · exact u55

def b341 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 194, targets := 256 }], pairs := [(1,8)], upper := (rows 51 194 84 268 272 40 225 161 417), lower := (rows 51 194 84 268 272 40 64 128 256), losses := [] }

theorem u341 : Upper (D 2) (R 2) [50,192,80,260,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b341
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 84 268 272 160 105 169 297), lower := (rows 51 194 84 268 272 160 64 128 256), losses := [] }

theorem u342 : Upper (D 2) (R 2) [50,192,80,260,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b342
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 140, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 296 272 33 204 140 396), lower := (rows 51 194 84 296 272 33 64 128 256), losses := [] }

theorem u343 : Upper (D 2) (R 2) [50,192,80,288,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b343
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 296 272 36 201 137 393), lower := (rows 51 194 84 296 272 36 64 128 256), losses := [] }

theorem u344 : Upper (D 2) (R 2) [50,192,80,288,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b344
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 296 272 40 197 133 389), lower := (rows 51 194 84 296 272 40 64 128 256), losses := [] }

theorem u345 : Upper (D 2) (R 2) [50,192,80,288,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b345
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 84 296 272 160 77 141 269), lower := (rows 51 194 84 296 272 160 64 128 256), losses := [] }

theorem u346 : Upper (D 2) (R 2) [50,192,80,288,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b346
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r347 : Route 9 := (fun mask => (mask,id))

def c347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u347 : Upper (D 2) (R 2) [50,192,80,384,256,1] 13 := by
  apply FastRouting.sound _ _ [50,192,80,384,256,1] 13 (by decide) (choices 1) [4,8,32] r347 c347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u56
  · exact u57
  · exact u58

def b348 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 392 272 36 105 169 297), lower := (rows 51 194 84 392 272 36 64 128 256), losses := [] }

theorem u348 : Upper (D 2) (R 2) [50,192,80,384,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b348
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 198, targets := 256 }], pairs := [(1,8)], upper := (rows 51 194 84 392 272 40 101 165 293), lower := (rows 51 194 84 392 272 40 64 128 256), losses := [] }

theorem u349 : Upper (D 2) (R 2) [50,192,80,384,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b349
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 51 194 261 328 20 40 240 176 432), lower := (rows 51 194 261 328 20 40 64 128 256), losses := [] }

theorem u350 : Upper (D 2) (R 2) [50,192,257,320,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b350
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 261 328 20 48 232 168 424), lower := (rows 51 194 261 328 20 48 64 128 256), losses := [] }

theorem u351 : Upper (D 2) (R 2) [50,192,257,320,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b351
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 261 328 20 160 120 184 312), lower := (rows 51 194 261 328 20 160 64 128 256), losses := [] }

theorem u352 : Upper (D 2) (R 2) [50,192,257,320,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b352
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 51 194 324 392 17 36 120 184 312), lower := (rows 51 194 324 392 17 36 64 128 256), losses := [] }

theorem u353 : Upper (D 2) (R 2) [50,192,320,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b353
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 324 392 17 48 108 172 300), lower := (rows 51 194 324 392 17 48 64 128 256), losses := [] }

theorem u354 : Upper (D 2) (R 2) [50,192,320,384,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b354
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 14 152 272 96 480 416 416), lower := (rows 113 7 14 152 272 96 64 128 256), losses := [] }

theorem u355 : Upper (D 2) (R 2) [112,5,10,144,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b355
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m356_32 : Upper (D 2) (R 2) [112,5,10,144,256,128,32] 13 :=
  permutation_upper _ _ _ [112,5,10,144,256,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u59

def r356 : Route 9 := (fun mask => (mask,id))

def c356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u356 : Upper (D 2) (R 2) [112,5,10,144,256,128] 13 := by
  apply FastRouting.sound _ _ [112,5,10,144,256,128] 13 (by decide) (choices 1) [32,256] r356 c356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m356_32
  · exact u60

def b357 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 7 14 152 272 288 224 224 480), lower := (rows 113 7 14 152 272 288 64 128 256), losses := [] }

theorem u357 : Upper (D 2) (R 2) [112,5,10,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b357
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 14 392 48 160 336 464 336), lower := (rows 113 7 14 392 48 160 64 128 256), losses := [] }

theorem u358 : Upper (D 2) (R 2) [112,5,10,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b358
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 14 392 80 160 368 432 304), lower := (rows 113 7 14 392 80 160 64 128 256), losses := [] }

theorem u359 : Upper (D 2) (R 2) [112,5,10,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b359
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P02
