import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0504
import IrregularNine14P06C0505
import IrregularNine14P06C0506
import IrregularNine14P06C0507
import IrregularNine14P06C0508

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41220 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 164 42 341 357 325 453 325), lower := (rows 11 22 164 42 16 32 64 128 256), losses := [] }

theorem u41220 : Upper (D 6) (R 6) [10,20,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41221 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 22 164 44 339 355 323 451 323), lower := (rows 11 22 164 44 16 32 64 128 256), losses := [] }

theorem u41221 : Upper (D 6) (R 6) [10,20,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41222 : Route 9 := (fun mask => (mask,id))

def c41222 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41222 : Upper (D 6) (R 6) [10,20,160,65] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41222 c41222
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30295
  · exact u30296
  · exact u30297
  · exact u30298
  · exact u30299
  · exact u30300
  · exact u30301
  · exact u30302
  · exact u30303
  · exact u30304
  · exact u30305
  · exact u30306
  · exact u30307
  · exact u30308
  · exact u30309

def b41223 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 164 74 373 357 357 485 357), lower := (rows 11 22 164 74 16 32 64 128 256), losses := [] }

theorem u41223 : Upper (D 6) (R 6) [10,20,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41224 : Route 9 := (fun mask => (mask,id))

def c41224 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41224 : Upper (D 6) (R 6) [10,20,160,68] 13 := by
  apply FastRouting.sound _ _ [10,20,160,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41224 c41224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30310
  · exact u30311
  · exact u30312
  · exact u30313
  · exact u30314
  · exact u30315
  · exact u30316
  · exact u30317
  · exact u30318
  · exact u30319

def r41225 : Route 9 := (fun mask => (mask,id))

def c41225 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41225 : Upper (D 6) (R 6) [10,20,160,96] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41225 c41225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30320
  · exact u30321
  · exact u30322
  · exact u30323
  · exact u30324
  · exact u30325
  · exact u30326
  · exact u30327
  · exact u30328
  · exact u30329

def r41226 : Route 9 := (fun mask => (mask,id))

def c41226 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41226 : Upper (D 6) (R 6) [10,20,160,257] 13 := by
  apply FastRouting.sound _ _ [10,20,160,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41226 c41226
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30330
  · exact u30331
  · exact u30332
  · exact u30333
  · exact u30334
  · exact u30335
  · exact u30336
  · exact u30337
  · exact u30338
  · exact u30339

def b41227 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 164 266 117 101 101 229 357), lower := (rows 11 22 164 266 16 32 64 128 256), losses := [] }

theorem u41227 : Upper (D 6) (R 6) [10,20,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41228 : Route 9 := (fun mask => (mask,id))

def c41228 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41228 : Upper (D 6) (R 6) [10,20,160,260] 13 := by
  apply FastRouting.sound _ _ [10,20,160,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41228 c41228
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30340
  · exact u30341
  · exact u30342
  · exact u30343
  · exact u30344
  · exact u30345

def r41229 : Route 9 := (fun mask => (mask,id))

def c41229 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41229 : Upper (D 6) (R 6) [10,20,160,288] 13 := by
  apply FastRouting.sound _ _ [10,20,160,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41229 c41229
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30346
  · exact u30347
  · exact u30348
  · exact u30349
  · exact u30350
  · exact u30351

def r41230 : Route 9 := (fun mask => (mask,id))

def c41230 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41230 : Upper (D 6) (R 6) [10,20,160,320] 13 := by
  apply FastRouting.sound _ _ [10,20,160,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41230 c41230
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30352
  · exact u30353
  · exact u30354
  · exact u30355
  · exact u30356
  · exact u30357
  · exact u30358
  · exact u30359
  · exact u30360
  · exact u30361

def b41231 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 388 11 117 101 101 229 357), lower := (rows 11 22 388 11 16 32 64 128 256), losses := [] }

theorem u41231 : Upper (D 6) (R 6) [10,20,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41232 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 388 13 115 99 99 227 355), lower := (rows 11 22 388 13 16 32 64 128 256), losses := [] }

theorem u41232 : Upper (D 6) (R 6) [10,20,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41233 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 388 14 113 97 97 225 353), lower := (rows 11 22 388 14 16 32 64 128 256), losses := [] }

theorem u41233 : Upper (D 6) (R 6) [10,20,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41234 : Route 9 := (fun mask => (mask,id))

def c41234 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41234 : Upper (D 6) (R 6) [10,20,384,33] 13 := by
  apply FastRouting.sound _ _ [10,20,384,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41234 c41234
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30362
  · exact u30363
  · exact u30364
  · exact u30365
  · exact u30366
  · exact u30367
  · exact u30368
  · exact u30369
  · exact u30370
  · exact u30371

def b41235 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 388 42 117 101 101 229 357), lower := (rows 11 22 388 42 16 32 64 128 256), losses := [] }

theorem u41235 : Upper (D 6) (R 6) [10,20,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41236 : Route 9 := (fun mask => (mask,id))

def c41236 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41236 : Upper (D 6) (R 6) [10,20,384,36] 13 := by
  apply FastRouting.sound _ _ [10,20,384,36] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41236 c41236
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30372
  · exact u30373
  · exact u30374
  · exact u30375
  · exact u30376
  · exact u30377

def r41237 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41237 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41237 : Upper (D 6) (R 6) [10,20,384,96] 13 := by
  apply FastRouting.sound _ _ [10,20,384,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41237 c41237
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30378
  · exact u30379
  · exact u30380
  · exact u30381
  · exact u30382
  · exact u30383
  · exact u30384

def b41238 : PairBound 9 := { available := 484, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 22 13 500 484 484 484 484), lower := (rows 11 35 22 13 16 32 64 128 256), losses := [] }

theorem u41238 : Upper (D 6) (R 6) [10,33,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41239 : PairBound 9 := { available := 452, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 41 468 484 452 452 452), lower := (rows 11 35 22 41 16 32 64 128 256), losses := [] }

theorem u41239 : Upper (D 6) (R 6) [10,33,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41240 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 44 469 485 453 453 453), lower := (rows 11 35 22 44 16 32 64 128 256), losses := [] }

theorem u41240 : Upper (D 6) (R 6) [10,33,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41241 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 2, region := 496, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 35 22 73 500 484 484 484 484), lower := (rows 11 35 22 73 16 32 64 128 256), losses := [] }

theorem u41241 : Upper (D 6) (R 6) [10,33,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41242 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41242 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41242 : Upper (D 6) (R 6) [10,33,18,68] 13 := by
  apply FastRouting.sound _ _ [10,33,18,68] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r41242 c41242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30385
  · exact u30386
  · exact u30387
  · exact u30388
  · exact u30389
  · exact u30390
  · exact u30391
  · exact u30392
  · exact u30393
  · exact u30394
  · exact u30395

def b41243 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 104 469 485 453 453 453), lower := (rows 11 35 22 104 16 32 64 128 256), losses := [] }

theorem u41243 : Upper (D 6) (R 6) [10,33,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41244 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 368, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 35 22 137 372 356 356 484 356), lower := (rows 11 35 22 137 16 32 64 128 256), losses := [] }

theorem u41244 : Upper (D 6) (R 6) [10,33,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41245 : Route 9 := (fun mask => (mask,id))

def c41245 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41245 : Upper (D 6) (R 6) [10,33,18,132] 13 := by
  apply FastRouting.sound _ _ [10,33,18,132] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41245 c41245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30396
  · exact u30397
  · exact u30398
  · exact u30399
  · exact u30400
  · exact u30401
  · exact u30402
  · exact u30403
  · exact u30404
  · exact u30405

def b41246 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 168 341 357 325 453 325), lower := (rows 11 35 22 168 16 32 64 128 256), losses := [] }

theorem u41246 : Upper (D 6) (R 6) [10,33,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41247 : Route 9 := (fun mask => (mask,id))

def c41247 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41247 : Upper (D 6) (R 6) [10,33,18,192] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41247 c41247
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30406
  · exact u30407
  · exact u30408
  · exact u30409
  · exact u30410
  · exact u30411
  · exact u30412
  · exact u30413
  · exact u30414
  · exact u30415

def r41248 : Route 9 := (fun mask => (mask,id))

def c41248 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41248 : Upper (D 6) (R 6) [10,33,18,384] 13 := by
  apply FastRouting.sound _ _ [10,33,18,384] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41248 c41248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30416
  · exact u30417
  · exact u30418
  · exact u30419
  · exact u30420
  · exact u30421

def b41249 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 52 11 468 484 452 452 452), lower := (rows 11 35 52 11 16 32 64 128 256), losses := [] }

theorem u41249 : Upper (D 6) (R 6) [10,33,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41250 : PairBound 9 := { available := 454, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 52 13 470 486 454 454 454), lower := (rows 11 35 52 13 16 32 64 128 256), losses := [] }

theorem u41250 : Upper (D 6) (R 6) [10,33,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41251 : PairBound 9 := { available := 453, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 52 14 469 485 453 453 453), lower := (rows 11 35 52 14 16 32 64 128 256), losses := [] }

theorem u41251 : Upper (D 6) (R 6) [10,33,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41252 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41252 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41252 : Upper (D 6) (R 6) [10,33,48,65] 13 := by
  apply FastRouting.sound _ _ [10,33,48,65] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r41252 c41252
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30422
  · exact u30423
  · exact u30424
  · exact u30425
  · exact u30426
  · exact u30427
  · exact u30428

def b41253 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 52 74 469 485 453 453 453), lower := (rows 11 35 52 74 16 32 64 128 256), losses := [] }

theorem u41253 : Upper (D 6) (R 6) [10,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41254 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41254 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41254 : Upper (D 6) (R 6) [10,33,48,68] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41254 c41254
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30429
  · exact u30430
  · exact u30431
  · exact u30432
  · exact u30433
  · exact u30434
  · exact u30435
  · exact u30436
  · exact u30437
  · exact u30438
  · exact u30439

def r41255 : Route 9 := (fun mask => (mask,id))

def c41255 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41255 : Upper (D 6) (R 6) [10,33,48,129] 13 := by
  apply FastRouting.sound _ _ [10,33,48,129] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41255 c41255
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30440
  · exact u30441
  · exact u30442
  · exact u30443
  · exact u30444
  · exact u30445

def b41256 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 52 138 341 357 325 453 325), lower := (rows 11 35 52 138 16 32 64 128 256), losses := [] }

theorem u41256 : Upper (D 6) (R 6) [10,33,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41257 : Route 9 := (fun mask => (mask,id))

def c41257 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41257 : Upper (D 6) (R 6) [10,33,48,132] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41257 c41257
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30446
  · exact u30447
  · exact u30448
  · exact u30449
  · exact u30450
  · exact u30451
  · exact u30452
  · exact u30453
  · exact u30454
  · exact u30455

def r41258 : Route 9 := (fun mask => (mask,id))

def c41258 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41258 : Upper (D 6) (R 6) [10,33,48,192] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41258 c41258
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30456
  · exact u30457
  · exact u30458
  · exact u30459
  · exact u30460
  · exact u30461
  · exact u30462
  · exact u30463
  · exact u30464
  · exact u30465

def r41259 : Route 9 := (fun mask => (mask,id))

def c41259 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41259 : Upper (D 6) (R 6) [10,33,48,384] 13 := by
  apply FastRouting.sound _ _ [10,33,48,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41259 c41259
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30466
  · exact u30467
  · exact u30468
  · exact u30469
  · exact u30470
  · exact u30471

def b41260 : PairBound 9 := { available := 500, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 69 14 500 500 500 500 500), lower := (rows 11 35 69 14 16 32 64 128 256), losses := [] }

theorem u41260 : Upper (D 6) (R 6) [10,33,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41261 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 69 26 500 484 484 484 484), lower := (rows 11 35 69 26 16 32 64 128 256), losses := [] }

theorem u41261 : Upper (D 6) (R 6) [10,33,65,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41262 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41262 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41262 : Upper (D 6) (R 6) [10,33,65,20] 13 := by
  apply FastRouting.sound _ _ [10,33,65,20] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r41262 c41262
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30472
  · exact u30473
  · exact u30474
  · exact u30475
  · exact u30476
  · exact u30477
  · exact u30478
  · exact u30479
  · exact u30480
  · exact u30481
  · exact u30482

def b41263 : PairBound 9 := { available := 468, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 42 468 500 468 468 468), lower := (rows 11 35 69 42 16 32 64 128 256), losses := [] }

theorem u41263 : Upper (D 6) (R 6) [10,33,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41264 : PairBound 9 := { available := 470, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 44 470 502 470 470 470), lower := (rows 11 35 69 44 16 32 64 128 256), losses := [] }

theorem u41264 : Upper (D 6) (R 6) [10,33,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41265 : PairBound 9 := { available := 454, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 56 470 486 454 454 454), lower := (rows 11 35 69 56 16 32 64 128 256), losses := [] }

theorem u41265 : Upper (D 6) (R 6) [10,33,65,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41266 : PairBound 9 := { available := 436, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 11 35 69 74 436 436 500 436 436), lower := (rows 11 35 69 74 16 32 64 128 256), losses := [] }

theorem u41266 : Upper (D 6) (R 6) [10,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41267 : PairBound 9 := { available := 438, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 69 76 438 438 502 438 438), lower := (rows 11 35 69 76 16 32 64 128 256), losses := [] }

theorem u41267 : Upper (D 6) (R 6) [10,33,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41268 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41268 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41268 : Upper (D 6) (R 6) [10,33,65,80] 13 := by
  apply FastRouting.sound _ _ [10,33,65,80] 13 (by decide) (choices 2) [6,34,36,130,132,160,384] r41268 c41268
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30483
  · exact u30484
  · exact u30485
  · exact u30486
  · exact u30487
  · exact u30488
  · exact u30489

def b41269 : PairBound 9 := { available := 406, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 104 406 438 470 406 406), lower := (rows 11 35 69 104 16 32 64 128 256), losses := [] }

theorem u41269 : Upper (D 6) (R 6) [10,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41270 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 69 138 372 372 372 500 372), lower := (rows 11 35 69 138 16 32 64 128 256), losses := [] }

theorem u41270 : Upper (D 6) (R 6) [10,33,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41271 : Route 9 := (fun mask => (mask,id))

def c41271 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41271 : Upper (D 6) (R 6) [10,33,65,132] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41271 c41271
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30490
  · exact u30491
  · exact u30492
  · exact u30493
  · exact u30494
  · exact u30495
  · exact u30496
  · exact u30497
  · exact u30498
  · exact u30499

def r41272 : Route 9 := (fun mask => (mask,id))

def c41272 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41272 : Upper (D 6) (R 6) [10,33,65,144] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41272 c41272
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30500
  · exact u30501
  · exact u30502
  · exact u30503
  · exact u30504
  · exact u30505
  · exact u30506
  · exact u30507
  · exact u30508
  · exact u30509

def b41273 : PairBound 9 := { available := 342, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 168 342 374 342 470 342), lower := (rows 11 35 69 168 16 32 64 128 256), losses := [] }

theorem u41273 : Upper (D 6) (R 6) [10,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41274 : Route 9 := (fun mask => (mask,id))

def c41274 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41274 : Upper (D 6) (R 6) [10,33,65,192] 13 := by
  apply FastRouting.sound _ _ [10,33,65,192] 13 (by decide) (choices 2) [6,34,36,258,260,288] r41274 c41274
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30510
  · exact u30511
  · exact u30512
  · exact u30513
  · exact u30514
  · exact u30515

def r41275 : Route 9 := (fun mask => (mask,id))

def c41275 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41275 : Upper (D 6) (R 6) [10,33,65,384] 13 := by
  apply FastRouting.sound _ _ [10,33,65,384] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41275 c41275
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30516
  · exact u30517
  · exact u30518
  · exact u30519
  · exact u30520
  · exact u30521

def b41276 : PairBound 9 := { available := 500, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 70 13 500 500 500 500 500), lower := (rows 11 35 70 13 16 32 64 128 256), losses := [] }

theorem u41276 : Upper (D 6) (R 6) [10,33,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41277 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 2, region := 432, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 35 70 25 500 484 484 484 484), lower := (rows 11 35 70 25 16 32 64 128 256), losses := [] }

theorem u41277 : Upper (D 6) (R 6) [10,33,66,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41278 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41278 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41278 : Upper (D 6) (R 6) [10,33,66,20] 13 := by
  apply FastRouting.sound _ _ [10,33,66,20] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r41278 c41278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30522
  · exact u30523
  · exact u30524
  · exact u30525
  · exact u30526
  · exact u30527
  · exact u30528
  · exact u30529
  · exact u30530
  · exact u30531
  · exact u30532

def b41279 : PairBound 9 := { available := 468, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 41 468 500 468 468 468), lower := (rows 11 35 70 41 16 32 64 128 256), losses := [] }

theorem u41279 : Upper (D 6) (R 6) [10,33,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u41279
end Delivery.IrregularNine14.P06
