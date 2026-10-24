import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0520
import IrregularNine14P06C0521
import IrregularNine14P06C0522
import IrregularNine14P06C0523
import IrregularNine14P06C0524
import IrregularNine14P06C0525

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41460 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 84 14 497 481 481 481 481), lower := (rows 11 38 84 14 16 32 64 128 256), losses := [] }

theorem u41460 : Upper (D 6) (R 6) [10,36,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41461 : PairBound 9 := { available := 455, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 84 41 471 487 455 455 455), lower := (rows 11 38 84 41 16 32 64 128 256), losses := [] }

theorem u41461 : Upper (D 6) (R 6) [10,36,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41462 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 84 42 469 485 453 453 453), lower := (rows 11 38 84 42 16 32 64 128 256), losses := [] }

theorem u41462 : Upper (D 6) (R 6) [10,36,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41463 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 9, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 38 84 44 467 483 451 451 451), lower := (rows 11 38 84 44 16 32 64 128 256), losses := [] }

theorem u41463 : Upper (D 6) (R 6) [10,36,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41464 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41464 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41464 : Upper (D 6) (R 6) [10,36,80,65] 13 := by
  apply FastRouting.sound _ _ [10,36,80,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r41464 c41464
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31234
  · exact u31235
  · exact u31236
  · exact u31237
  · exact u31238
  · exact u31239
  · exact u31240
  · exact u31241
  · exact u31242
  · exact u31243
  · exact u31244

def b41465 : PairBound 9 := { available := 421, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 84 74 437 421 485 421 421), lower := (rows 11 38 84 74 16 32 64 128 256), losses := [] }

theorem u41465 : Upper (D 6) (R 6) [10,36,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41466 : PairBound 9 := { available := 419, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 38 84 76 435 419 483 419 419), lower := (rows 11 38 84 76 16 32 64 128 256), losses := [] }

theorem u41466 : Upper (D 6) (R 6) [10,36,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41467 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41467 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41467 : Upper (D 6) (R 6) [10,36,80,96] 13 := by
  apply FastRouting.sound _ _ [10,36,80,96] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r41467 c41467
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31245
  · exact u31246
  · exact u31247
  · exact u31248
  · exact u31249
  · exact u31250
  · exact u31251

def r41468 : Route 9 := (fun mask => (mask,id))

def c41468 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41468 : Upper (D 6) (R 6) [10,36,80,129] 13 := by
  apply FastRouting.sound _ _ [10,36,80,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41468 c41468
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31252
  · exact u31253
  · exact u31254
  · exact u31255
  · exact u31256
  · exact u31257
  · exact u31258
  · exact u31259
  · exact u31260
  · exact u31261
  · exact u31262
  · exact u31263
  · exact u31264
  · exact u31265
  · exact u31266

def b41469 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 84 138 373 357 357 485 357), lower := (rows 11 38 84 138 16 32 64 128 256), losses := [] }

theorem u41469 : Upper (D 6) (R 6) [10,36,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41470 : Route 9 := (fun mask => (mask,id))

def c41470 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41470 : Upper (D 6) (R 6) [10,36,80,132] 13 := by
  apply FastRouting.sound _ _ [10,36,80,132] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41470 c41470
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31267
  · exact u31268
  · exact u31269
  · exact u31270
  · exact u31271
  · exact u31272
  · exact u31273
  · exact u31274
  · exact u31275
  · exact u31276

def r41471 : Route 9 := (fun mask => (mask,id))

def c41471 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41471 : Upper (D 6) (R 6) [10,36,80,160] 13 := by
  apply FastRouting.sound _ _ [10,36,80,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41471 c41471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31277
  · exact u31278
  · exact u31279
  · exact u31280
  · exact u31281
  · exact u31282
  · exact u31283
  · exact u31284
  · exact u31285
  · exact u31286

def r41472 : Route 9 := (fun mask => (mask,id))

def c41472 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41472 : Upper (D 6) (R 6) [10,36,80,192] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r41472 c41472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31287
  · exact u31288
  · exact u31289
  · exact u31290
  · exact u31291
  · exact u31292
  · exact u31293
  · exact u31294
  · exact u31295
  · exact u31296

def r41473 : Route 9 := (fun mask => (mask,id))

def c41473 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41473 : Upper (D 6) (R 6) [10,36,80,384] 13 := by
  apply FastRouting.sound _ _ [10,36,80,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41473 c41473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31297
  · exact u31298
  · exact u31299
  · exact u31300
  · exact u31301
  · exact u31302
  · exact u31303
  · exact u31304
  · exact u31305
  · exact u31306

def b41474 : PairBound 9 := { available := 372, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 133 11 372 372 372 500 372), lower := (rows 11 38 133 11 16 32 64 128 256), losses := [] }

theorem u41474 : Upper (D 6) (R 6) [10,36,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41475 : PairBound 9 := { available := 370, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 133 13 370 370 370 498 370), lower := (rows 11 38 133 13 16 32 64 128 256), losses := [] }

theorem u41475 : Upper (D 6) (R 6) [10,36,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41476 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 133 14 369 369 369 497 369), lower := (rows 11 38 133 14 16 32 64 128 256), losses := [] }

theorem u41476 : Upper (D 6) (R 6) [10,36,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41477 : Route 9 := (fun mask => (mask,id))

def c41477 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41477 : Upper (D 6) (R 6) [10,36,129,17] 13 := by
  apply FastRouting.sound _ _ [10,36,129,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41477 c41477
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31307
  · exact u31308
  · exact u31309
  · exact u31310
  · exact u31311
  · exact u31312
  · exact u31313
  · exact u31314
  · exact u31315
  · exact u31316

def b41478 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 133 26 373 357 357 485 357), lower := (rows 11 38 133 26 16 32 64 128 256), losses := [] }

theorem u41478 : Upper (D 6) (R 6) [10,36,129,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41479 : Route 9 := (fun mask => (mask,id))

def c41479 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41479 : Upper (D 6) (R 6) [10,36,129,20] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41479 c41479
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31317
  · exact u31318
  · exact u31319
  · exact u31320
  · exact u31321
  · exact u31322
  · exact u31323
  · exact u31324
  · exact u31325
  · exact u31326

def b41480 : PairBound 9 := { available := 342, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 133 41 342 374 342 470 342), lower := (rows 11 38 133 41 16 32 64 128 256), losses := [] }

theorem u41480 : Upper (D 6) (R 6) [10,36,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41481 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 133 42 341 373 341 469 341), lower := (rows 11 38 133 42 16 32 64 128 256), losses := [] }

theorem u41481 : Upper (D 6) (R 6) [10,36,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41482 : PairBound 9 := { available := 339, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 9, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 38 133 44 339 371 339 467 339), lower := (rows 11 38 133 44 16 32 64 128 256), losses := [] }

theorem u41482 : Upper (D 6) (R 6) [10,36,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41483 : Route 9 := (fun mask => (mask,id))

def c41483 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41483 : Upper (D 6) (R 6) [10,36,129,48] 13 := by
  apply FastRouting.sound _ _ [10,36,129,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41483 c41483
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31327
  · exact u31328
  · exact u31329
  · exact u31330
  · exact u31331
  · exact u31332
  · exact u31333
  · exact u31334
  · exact u31335
  · exact u31336

def r41484 : Route 9 := (fun mask => (mask,id))

def c41484 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41484 : Upper (D 6) (R 6) [10,36,129,65] 13 := by
  apply FastRouting.sound _ _ [10,36,129,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41484 c41484
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31337
  · exact u31338
  · exact u31339
  · exact u31340
  · exact u31341
  · exact u31342
  · exact u31343
  · exact u31344
  · exact u31345
  · exact u31346

def b41485 : PairBound 9 := { available := 373, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 133 74 373 373 373 501 373), lower := (rows 11 38 133 74 16 32 64 128 256), losses := [] }

theorem u41485 : Upper (D 6) (R 6) [10,36,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41486 : Route 9 := (fun mask => (mask,id))

def c41486 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41486 : Upper (D 6) (R 6) [10,36,129,68] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41486 c41486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31347
  · exact u31348
  · exact u31349
  · exact u31350
  · exact u31351
  · exact u31352
  · exact u31353
  · exact u31354
  · exact u31355
  · exact u31356

def r41487 : Route 9 := (fun mask => (mask,id))

def c41487 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41487 : Upper (D 6) (R 6) [10,36,129,80] 13 := by
  apply FastRouting.sound _ _ [10,36,129,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41487 c41487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31357
  · exact u31358
  · exact u31359
  · exact u31360
  · exact u31361
  · exact u31362
  · exact u31363
  · exact u31364
  · exact u31365
  · exact u31366
  · exact u31367
  · exact u31368
  · exact u31369
  · exact u31370
  · exact u31371

def r41488 : Route 9 := (fun mask => (mask,id))

def c41488 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41488 : Upper (D 6) (R 6) [10,36,129,96] 13 := by
  apply FastRouting.sound _ _ [10,36,129,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41488 c41488
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31372
  · exact u31373
  · exact u31374
  · exact u31375
  · exact u31376
  · exact u31377
  · exact u31378
  · exact u31379
  · exact u31380
  · exact u31381

def r41489 : Route 9 := (fun mask => (mask,id))

def c41489 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41489 : Upper (D 6) (R 6) [10,36,129,257] 13 := by
  apply FastRouting.sound _ _ [10,36,129,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41489 c41489
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31382
  · exact u31383
  · exact u31384
  · exact u31385
  · exact u31386
  · exact u31387

def b41490 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 133 266 117 117 117 245 373), lower := (rows 11 38 133 266 16 32 64 128 256), losses := [] }

theorem u41490 : Upper (D 6) (R 6) [10,36,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41491 : Route 9 := (fun mask => (mask,id))

def c41491 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41491 : Upper (D 6) (R 6) [10,36,129,260] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41491 c41491
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31388
  · exact u31389
  · exact u31390
  · exact u31391
  · exact u31392
  · exact u31393

def r41492 : Route 9 := (fun mask => (mask,id))

def c41492 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41492 : Upper (D 6) (R 6) [10,36,129,272] 13 := by
  apply FastRouting.sound _ _ [10,36,129,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41492 c41492
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31394
  · exact u31395
  · exact u31396
  · exact u31397
  · exact u31398
  · exact u31399
  · exact u31400
  · exact u31401
  · exact u31402
  · exact u31403

def r41493 : Route 9 := (fun mask => (mask,id))

def c41493 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41493 : Upper (D 6) (R 6) [10,36,129,288] 13 := by
  apply FastRouting.sound _ _ [10,36,129,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41493 c41493
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31404
  · exact u31405
  · exact u31406
  · exact u31407
  · exact u31408
  · exact u31409

def r41494 : Route 9 := (fun mask => (mask,id))

def c41494 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41494 : Upper (D 6) (R 6) [10,36,129,320] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41494 c41494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31410
  · exact u31411
  · exact u31412
  · exact u31413
  · exact u31414
  · exact u31415
  · exact u31416
  · exact u31417
  · exact u31418
  · exact u31419

def b41495 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 134 13 369 369 369 497 369), lower := (rows 11 38 134 13 16 32 64 128 256), losses := [] }

theorem u41495 : Upper (D 6) (R 6) [10,36,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41496 : Route 9 := (fun mask => (mask,id))

def c41496 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41496 : Upper (D 6) (R 6) [10,36,130,17] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41496 c41496
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31420
  · exact u31421
  · exact u31422
  · exact u31423
  · exact u31424
  · exact u31425
  · exact u31426
  · exact u31427
  · exact u31428
  · exact u31429

def r41497 : Route 9 := (fun mask => (mask,id))

def c41497 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41497 : Upper (D 6) (R 6) [10,36,130,20] 13 := by
  apply FastRouting.sound _ _ [10,36,130,20] 13 (by decide) (choices 2) [33,65,96,257,288,320] r41497 c41497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31430
  · exact u31431
  · exact u31432
  · exact u31433
  · exact u31434
  · exact u31435

def b41498 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 134 41 341 373 341 469 341), lower := (rows 11 38 134 41 16 32 64 128 256), losses := [] }

theorem u41498 : Upper (D 6) (R 6) [10,36,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41499 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 38 134 44 337 369 337 465 337), lower := (rows 11 38 134 44 16 32 64 128 256), losses := [] }

theorem u41499 : Upper (D 6) (R 6) [10,36,130,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41500 : Route 9 := (fun mask => (mask,id))

def c41500 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41500 : Upper (D 6) (R 6) [10,36,130,48] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41500 c41500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31436
  · exact u31437
  · exact u31438
  · exact u31439
  · exact u31440
  · exact u31441

def r41501 : Route 9 := (fun mask => (mask,id))

def c41501 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41501 : Upper (D 6) (R 6) [10,36,130,65] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41501 c41501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31442
  · exact u31443
  · exact u31444
  · exact u31445
  · exact u31446
  · exact u31447
  · exact u31448
  · exact u31449
  · exact u31450
  · exact u31451

def r41502 : Route 9 := (fun mask => (mask,id))

def c41502 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41502 : Upper (D 6) (R 6) [10,36,130,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,68] 13 (by decide) (choices 2) [33,65,96,257,288,320] r41502 c41502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31452
  · exact u31453
  · exact u31454
  · exact u31455
  · exact u31456
  · exact u31457

def r41503 : Route 9 := (fun mask => (mask,id))

def c41503 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41503 : Upper (D 6) (R 6) [10,36,130,80] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41503 c41503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31458
  · exact u31459
  · exact u31460
  · exact u31461
  · exact u31462
  · exact u31463
  · exact u31464
  · exact u31465
  · exact u31466
  · exact u31467

def r41504 : Route 9 := (fun mask => (mask,id))

def c41504 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41504 : Upper (D 6) (R 6) [10,36,130,96] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41504 c41504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31468
  · exact u31469
  · exact u31470
  · exact u31471
  · exact u31472
  · exact u31473

def r41505 : Route 9 := (fun mask => (mask,id))

def c41505 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41505 : Upper (D 6) (R 6) [10,36,130,257] 13 := by
  apply FastRouting.sound _ _ [10,36,130,257] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41505 c41505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31474
  · exact u31475
  · exact u31476
  · exact u31477
  · exact u31478
  · exact u31479

def r41506 : Route 9 := (fun mask => (mask,id))

def c41506 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41506 : Upper (D 6) (R 6) [10,36,130,260] 13 := by
  apply FastRouting.sound _ _ [10,36,130,260] 13 (by decide) (choices 2) [33,65,96] r41506 c41506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u31480
  · exact u31481
  · exact u31482

def r41507 : Route 9 := (fun mask => (mask,id))

def c41507 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41507 : Upper (D 6) (R 6) [10,36,130,272] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41507 c41507
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31483
  · exact u31484
  · exact u31485
  · exact u31486
  · exact u31487
  · exact u31488

def r41508 : Route 9 := (fun mask => (mask,id))

def c41508 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41508 : Upper (D 6) (R 6) [10,36,130,288] 13 := by
  apply FastRouting.sound _ _ [10,36,130,288] 13 (by decide) (choices 2) [5,65,68] r41508 c41508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u31489
  · exact u31490
  · exact u31491

def r41509 : Route 9 := (fun mask => (mask,id))

def c41509 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41509 : Upper (D 6) (R 6) [10,36,130,320] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41509 c41509
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31492
  · exact u31493
  · exact u31494
  · exact u31495
  · exact u31496
  · exact u31497

def b41510 : PairBound 9 := { available := 357, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 148 11 373 357 357 485 357), lower := (rows 11 38 148 11 16 32 64 128 256), losses := [] }

theorem u41510 : Upper (D 6) (R 6) [10,36,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41511 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 148 13 371 355 355 483 355), lower := (rows 11 38 148 13 16 32 64 128 256), losses := [] }

theorem u41511 : Upper (D 6) (R 6) [10,36,144,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41512 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 148 14 369 353 353 481 353), lower := (rows 11 38 148 14 16 32 64 128 256), losses := [] }

theorem u41512 : Upper (D 6) (R 6) [10,36,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41513 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 148 41 343 359 327 455 327), lower := (rows 11 38 148 41 16 32 64 128 256), losses := [] }

theorem u41513 : Upper (D 6) (R 6) [10,36,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41514 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 148 42 341 357 325 453 325), lower := (rows 11 38 148 42 16 32 64 128 256), losses := [] }

theorem u41514 : Upper (D 6) (R 6) [10,36,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41515 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 9, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 38 148 44 339 355 323 451 323), lower := (rows 11 38 148 44 16 32 64 128 256), losses := [] }

theorem u41515 : Upper (D 6) (R 6) [10,36,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41516 : Route 9 := (fun mask => (mask,id))

def c41516 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41516 : Upper (D 6) (R 6) [10,36,144,65] 13 := by
  apply FastRouting.sound _ _ [10,36,144,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41516 c41516
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31498
  · exact u31499
  · exact u31500
  · exact u31501
  · exact u31502
  · exact u31503
  · exact u31504
  · exact u31505
  · exact u31506
  · exact u31507
  · exact u31508
  · exact u31509
  · exact u31510
  · exact u31511
  · exact u31512

def b41517 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 148 74 373 357 357 485 357), lower := (rows 11 38 148 74 16 32 64 128 256), losses := [] }

theorem u41517 : Upper (D 6) (R 6) [10,36,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41518 : Route 9 := (fun mask => (mask,id))

def c41518 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41518 : Upper (D 6) (R 6) [10,36,144,68] 13 := by
  apply FastRouting.sound _ _ [10,36,144,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41518 c41518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31513
  · exact u31514
  · exact u31515
  · exact u31516
  · exact u31517
  · exact u31518
  · exact u31519
  · exact u31520
  · exact u31521
  · exact u31522

def r41519 : Route 9 := (fun mask => (mask,id))

def c41519 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41519 : Upper (D 6) (R 6) [10,36,144,96] 13 := by
  apply FastRouting.sound _ _ [10,36,144,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41519 c41519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31523
  · exact u31524
  · exact u31525
  · exact u31526
  · exact u31527
  · exact u31528
  · exact u31529
  · exact u31530
  · exact u31531
  · exact u31532

#print axioms u41519
end Delivery.IrregularNine14.P06
