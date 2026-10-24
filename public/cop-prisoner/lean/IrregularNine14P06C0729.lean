import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0687
import IrregularNine14P06C0688
import IrregularNine14P06C0689
import IrregularNine14P06C0690
import IrregularNine14P06C0691
import IrregularNine14P06C0692
import IrregularNine14P06C0693
import IrregularNine14P06C0694
import IrregularNine14P06C0695
import IrregularNine14P06C0696
import IrregularNine14P06C0697
import IrregularNine14P06C0698

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r43740 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43740 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43740 : Upper (D 6) (R 6) [10,33,18] 13 := by
  apply FastRouting.sound _ _ [10,33,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r43740 c43740
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41238
  · exact u41239
  · exact u41240
  · exact u41241
  · exact u41242
  · exact u41243
  · exact u41244
  · exact u41245
  · exact u41246
  · exact u41247
  · exact u41248

def b43741 : PairBound 9 := { available := 470, camps := [{ cop := 1, region := 4, targets := 2 },{ cop := 1, region := 4, targets := 64 },{ cop := 2, region := 2, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 35 37 478 470 502 470 470 470), lower := (rows 11 35 37 8 16 32 64 128 256), losses := [] }

theorem u43741 : Upper (D 6) (R 6) [10,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43742 : PairBound 9 := { available := 469, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 35 38 477 469 501 469 469 469), lower := (rows 11 35 38 8 16 32 64 128 256), losses := [] }

theorem u43742 : Upper (D 6) (R 6) [10,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43743 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43743 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43743 : Upper (D 6) (R 6) [10,33,48] 13 := by
  apply FastRouting.sound _ _ [10,33,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r43743 c43743
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41249
  · exact u41250
  · exact u41251
  · exact u41252
  · exact u41253
  · exact u41254
  · exact u41255
  · exact u41256
  · exact u41257
  · exact u41258
  · exact u41259

def r43744 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43744 : Nat → Fin 9 := (fun _ => 0)

theorem u43744 : Upper (D 6) (R 6) [10,33,65] 13 := by
  apply FastRouting.sound _ _ [10,33,65] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,130,132,144,160,192,384] r43744 c43744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41260
  · exact u41261
  · exact u41262
  · exact u41263
  · exact u41264
  · exact u41265
  · exact u41266
  · exact u41267
  · exact u41268
  · exact u41269
  · exact u41270
  · exact u41271
  · exact u41272
  · exact u41273
  · exact u41274
  · exact u41275

def r43745 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43745 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u43745 : Upper (D 6) (R 6) [10,33,66] 13 := by
  apply FastRouting.sound _ _ [10,33,66] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,384] r43745 c43745
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41276
  · exact u41277
  · exact u41278
  · exact u41279
  · exact u41280
  · exact u41281
  · exact u41282
  · exact u41283
  · exact u41284
  · exact u41285
  · exact u41286
  · exact u41287
  · exact u41288
  · exact u41289
  · exact u41290
  · exact u41291

def r43746 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43746 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43746 : Upper (D 6) (R 6) [10,33,80] 13 := by
  apply FastRouting.sound _ _ [10,33,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43746 c43746
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41292
  · exact u41293
  · exact u41294
  · exact u41295
  · exact u41296
  · exact u41297
  · exact u41298
  · exact u41299
  · exact u41300
  · exact u41301
  · exact u41302
  · exact u41303
  · exact u41304
  · exact u41305
  · exact u41306
  · exact u41307

def r43747 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43747 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43747 : Upper (D 6) (R 6) [10,33,96] 13 := by
  apply FastRouting.sound _ _ [10,33,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192,384] r43747 c43747
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41308
  · exact u41309
  · exact u41310
  · exact u41311
  · exact u41312
  · exact u41313
  · exact u41314
  · exact u41315
  · exact u41316
  · exact u41317
  · exact u41318
  · exact u41319
  · exact u41320
  · exact u41321
  · exact u41322
  · exact u41323

def r43748 : Route 9 := (fun mask => (mask,id))

def c43748 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43748 : Upper (D 6) (R 6) [10,33,129] 13 := by
  apply FastRouting.sound _ _ [10,33,129] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,258,260,272,288,320] r43748 c43748
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41324
  · exact u41325
  · exact u41326
  · exact u41327
  · exact u41328
  · exact u41329
  · exact u41330
  · exact u41331
  · exact u41332
  · exact u41333
  · exact u41334
  · exact u41335
  · exact u41336
  · exact u41337
  · exact u41338

def r43749 : Route 9 := (fun mask => (mask,id))

def c43749 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43749 : Upper (D 6) (R 6) [10,33,130] 13 := by
  apply FastRouting.sound _ _ [10,33,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43749 c43749
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41339
  · exact u41340
  · exact u41341
  · exact u41342
  · exact u41343
  · exact u41344
  · exact u41345
  · exact u41346
  · exact u41347
  · exact u41348
  · exact u41349
  · exact u41350
  · exact u41351
  · exact u41352
  · exact u41353

def r43750 : Route 9 := (fun mask => (mask,id))

def c43750 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43750 : Upper (D 6) (R 6) [10,33,144] 13 := by
  apply FastRouting.sound _ _ [10,33,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43750 c43750
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41354
  · exact u41355
  · exact u41356
  · exact u41357
  · exact u41358
  · exact u41359
  · exact u41360
  · exact u41361
  · exact u41362
  · exact u41363
  · exact u41364
  · exact u41365
  · exact u41366
  · exact u41367
  · exact u41368

def r43751 : Route 9 := (fun mask => (mask,id))

def c43751 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43751 : Upper (D 6) (R 6) [10,33,160] 13 := by
  apply FastRouting.sound _ _ [10,33,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43751 c43751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41369
  · exact u41370
  · exact u41371
  · exact u41372
  · exact u41373
  · exact u41374
  · exact u41375
  · exact u41376
  · exact u41377
  · exact u41378
  · exact u41379
  · exact u41380
  · exact u41381
  · exact u41382
  · exact u41383

def r43752 : Route 9 := (fun mask => (mask,id))

def c43752 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43752 : Upper (D 6) (R 6) [10,33,192] 13 := by
  apply FastRouting.sound _ _ [10,33,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43752 c43752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41384
  · exact u41385
  · exact u41386
  · exact u41387
  · exact u41388
  · exact u41389
  · exact u41390
  · exact u41391
  · exact u41392
  · exact u41393
  · exact u41394
  · exact u41395
  · exact u41396
  · exact u41397
  · exact u41398
  · exact u41399
  · exact u41400
  · exact u41401
  · exact u41402
  · exact u41403
  · exact u41404

def r43753 : Route 9 := (fun mask => (mask,id))

def c43753 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43753 : Upper (D 6) (R 6) [10,33,384] 13 := by
  apply FastRouting.sound _ _ [10,33,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43753 c43753
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41405
  · exact u41406
  · exact u41407
  · exact u41408
  · exact u41409
  · exact u41410
  · exact u41411
  · exact u41412
  · exact u41413
  · exact u41414
  · exact u41415
  · exact u41416
  · exact u41417
  · exact u41418
  · exact u41419

def b43754 : PairBound 9 := { available := 471, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 37 479 471 503 471 471 471), lower := (rows 11 38 37 8 16 32 64 128 256), losses := [] }

theorem u43754 : Upper (D 6) (R 6) [10,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43755 : PairBound 9 := { available := 469, camps := [{ cop := 5, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 38 477 469 501 469 469 469), lower := (rows 11 38 38 8 16 32 64 128 256), losses := [] }

theorem u43755 : Upper (D 6) (R 6) [10,36,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43756 : PairBound 9 := { available := 455, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 52 463 471 487 455 455 455), lower := (rows 11 38 52 8 16 32 64 128 256), losses := [] }

theorem u43756 : Upper (D 6) (R 6) [10,36,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43757 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43757 : Nat → Fin 9 := (fun _ => 0)

theorem u43757 : Upper (D 6) (R 6) [10,36,65] 13 := by
  apply FastRouting.sound _ _ [10,36,65] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,129,130,132,144,160,192,384] r43757 c43757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41420
  · exact u41421
  · exact u41422
  · exact u41423
  · exact u41424
  · exact u41425
  · exact u41426
  · exact u41427
  · exact u41428
  · exact u41429
  · exact u41430
  · exact u41431
  · exact u41432
  · exact u41433
  · exact u41434
  · exact u41435
  · exact u41436
  · exact u41437
  · exact u41438
  · exact u41439
  · exact u41440
  · exact u41441

def r43758 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43758 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u43758 : Upper (D 6) (R 6) [10,36,66] 13 := by
  apply FastRouting.sound _ _ [10,36,66] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,384] r43758 c43758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41442
  · exact u41443
  · exact u41444
  · exact u41445
  · exact u41446
  · exact u41447
  · exact u41448
  · exact u41449
  · exact u41450
  · exact u41451
  · exact u41452
  · exact u41453
  · exact u41454
  · exact u41455
  · exact u41456
  · exact u41457

def r43759 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43759 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43759 : Upper (D 6) (R 6) [10,36,80] 13 := by
  apply FastRouting.sound _ _ [10,36,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43759 c43759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41458
  · exact u41459
  · exact u41460
  · exact u41461
  · exact u41462
  · exact u41463
  · exact u41464
  · exact u41465
  · exact u41466
  · exact u41467
  · exact u41468
  · exact u41469
  · exact u41470
  · exact u41471
  · exact u41472
  · exact u41473

def b43760 : PairBound 9 := { available := 471, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 100 479 471 503 471 471 471), lower := (rows 11 38 100 8 16 32 64 128 256), losses := [] }

theorem u43760 : Upper (D 6) (R 6) [10,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43761 : Route 9 := (fun mask => (mask,id))

def c43761 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43761 : Upper (D 6) (R 6) [10,36,129] 13 := by
  apply FastRouting.sound _ _ [10,36,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43761 c43761
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41474
  · exact u41475
  · exact u41476
  · exact u41477
  · exact u41478
  · exact u41479
  · exact u41480
  · exact u41481
  · exact u41482
  · exact u41483
  · exact u41484
  · exact u41485
  · exact u41486
  · exact u41487
  · exact u41488
  · exact u41489
  · exact u41490
  · exact u41491
  · exact u41492
  · exact u41493
  · exact u41494

def r43762 : Route 9 := (fun mask => (mask,id))

def c43762 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43762 : Upper (D 6) (R 6) [10,36,130] 13 := by
  apply FastRouting.sound _ _ [10,36,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43762 c43762
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41495
  · exact u41496
  · exact u41497
  · exact u41498
  · exact u41499
  · exact u41500
  · exact u41501
  · exact u41502
  · exact u41503
  · exact u41504
  · exact u41505
  · exact u41506
  · exact u41507
  · exact u41508
  · exact u41509

def r43763 : Route 9 := (fun mask => (mask,id))

def c43763 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43763 : Upper (D 6) (R 6) [10,36,144] 13 := by
  apply FastRouting.sound _ _ [10,36,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43763 c43763
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41510
  · exact u41511
  · exact u41512
  · exact u41513
  · exact u41514
  · exact u41515
  · exact u41516
  · exact u41517
  · exact u41518
  · exact u41519
  · exact u41520
  · exact u41521
  · exact u41522
  · exact u41523
  · exact u41524

def b43764 : PairBound 9 := { available := 343, camps := [{ cop := 1, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 164 351 343 375 343 471 343), lower := (rows 11 38 164 8 16 32 64 128 256), losses := [] }

theorem u43764 : Upper (D 6) (R 6) [10,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43765 : Route 9 := (fun mask => (mask,id))

def c43765 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43765 : Upper (D 6) (R 6) [10,36,192] 13 := by
  apply FastRouting.sound _ _ [10,36,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43765 c43765
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41525
  · exact u41526
  · exact u41527
  · exact u41528
  · exact u41529
  · exact u41530
  · exact u41531
  · exact u41532
  · exact u41533
  · exact u41534
  · exact u41535
  · exact u41536
  · exact u41537
  · exact u41538
  · exact u41539
  · exact u41540
  · exact u41541
  · exact u41542
  · exact u41543
  · exact u41544
  · exact u41545

def r43766 : Route 9 := (fun mask => (mask,id))

def c43766 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43766 : Upper (D 6) (R 6) [10,36,384] 13 := by
  apply FastRouting.sound _ _ [10,36,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43766 c43766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41546
  · exact u41547
  · exact u41548
  · exact u41549
  · exact u41550
  · exact u41551
  · exact u41552
  · exact u41553
  · exact u41554
  · exact u41555
  · exact u41556
  · exact u41557
  · exact u41558
  · exact u41559
  · exact u41560

def r43767 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43767 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43767 : Upper (D 6) (R 6) [10,48,33] 13 := by
  apply FastRouting.sound _ _ [10,48,33] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r43767 c43767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41561
  · exact u41562
  · exact u41563
  · exact u41564
  · exact u41565
  · exact u41566
  · exact u41567
  · exact u41568
  · exact u41569
  · exact u41570
  · exact u41571

def b43768 : PairBound 9 := { available := 453, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 38 461 469 485 453 453 453), lower := (rows 11 50 38 8 16 32 64 128 256), losses := [] }

theorem u43768 : Upper (D 6) (R 6) [10,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43769 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43769 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43769 : Upper (D 6) (R 6) [10,48,65] 13 := by
  apply FastRouting.sound _ _ [10,48,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43769 c43769
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41572
  · exact u41573
  · exact u41574
  · exact u41575
  · exact u41576
  · exact u41577
  · exact u41578
  · exact u41579
  · exact u41580
  · exact u41581
  · exact u41582
  · exact u41583
  · exact u41584
  · exact u41585
  · exact u41586
  · exact u41587

def r43770 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43770 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43770 : Upper (D 6) (R 6) [10,48,66] 13 := by
  apply FastRouting.sound _ _ [10,48,66] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r43770 c43770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41588
  · exact u41589
  · exact u41590
  · exact u41591
  · exact u41592
  · exact u41593
  · exact u41594
  · exact u41595
  · exact u41596
  · exact u41597
  · exact u41598

def r43771 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43771 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43771 : Upper (D 6) (R 6) [10,48,96] 13 := by
  apply FastRouting.sound _ _ [10,48,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r43771 c43771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41599
  · exact u41600
  · exact u41601
  · exact u41602
  · exact u41603
  · exact u41604
  · exact u41605
  · exact u41606
  · exact u41607
  · exact u41608
  · exact u41609

def r43772 : Route 9 := (fun mask => (mask,id))

def c43772 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43772 : Upper (D 6) (R 6) [10,48,129] 13 := by
  apply FastRouting.sound _ _ [10,48,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43772 c43772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41610
  · exact u41611
  · exact u41612
  · exact u41613
  · exact u41614
  · exact u41615
  · exact u41616
  · exact u41617
  · exact u41618
  · exact u41619
  · exact u41620
  · exact u41621
  · exact u41622
  · exact u41623
  · exact u41624

def r43773 : Route 9 := (fun mask => (mask,id))

def c43773 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43773 : Upper (D 6) (R 6) [10,48,130] 13 := by
  apply FastRouting.sound _ _ [10,48,130] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r43773 c43773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41625
  · exact u41626
  · exact u41627
  · exact u41628
  · exact u41629
  · exact u41630
  · exact u41631
  · exact u41632
  · exact u41633
  · exact u41634

def r43774 : Route 9 := (fun mask => (mask,id))

def c43774 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43774 : Upper (D 6) (R 6) [10,48,160] 13 := by
  apply FastRouting.sound _ _ [10,48,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43774 c43774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41635
  · exact u41636
  · exact u41637
  · exact u41638
  · exact u41639
  · exact u41640
  · exact u41641
  · exact u41642
  · exact u41643
  · exact u41644

def r43775 : Route 9 := (fun mask => (mask,id))

def c43775 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43775 : Upper (D 6) (R 6) [10,48,192] 13 := by
  apply FastRouting.sound _ _ [10,48,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43775 c43775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41645
  · exact u41646
  · exact u41647
  · exact u41648
  · exact u41649
  · exact u41650
  · exact u41651
  · exact u41652
  · exact u41653
  · exact u41654
  · exact u41655
  · exact u41656
  · exact u41657
  · exact u41658
  · exact u41659

def r43776 : Route 9 := (fun mask => (mask,id))

def c43776 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43776 : Upper (D 6) (R 6) [10,48,384] 13 := by
  apply FastRouting.sound _ _ [10,48,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43776 c43776
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41660
  · exact u41661
  · exact u41662
  · exact u41663
  · exact u41664
  · exact u41665
  · exact u41666
  · exact u41667
  · exact u41668
  · exact u41669

def r43777 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43777 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43777 : Upper (D 6) (R 6) [10,96,18] 13 := by
  apply FastRouting.sound _ _ [10,96,18] 13 (by decide) (choices 2) [5,33,36,96,129,132,160,384] r43777 c43777
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41670
  · exact u41671
  · exact u41672
  · exact u41673
  · exact u41674
  · exact u41675
  · exact u41676
  · exact u41677

def r43778 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43778 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43778 : Upper (D 6) (R 6) [10,96,33] 13 := by
  apply FastRouting.sound _ _ [10,96,33] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192,384] r43778 c43778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41678
  · exact u41679
  · exact u41680
  · exact u41681
  · exact u41682
  · exact u41683
  · exact u41684
  · exact u41685
  · exact u41686
  · exact u41687
  · exact u41688
  · exact u41689
  · exact u41690
  · exact u41691
  · exact u41692
  · exact u41693

def b43779 : PairBound 9 := { available := 469, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 98 38 477 469 501 469 469 469), lower := (rows 11 98 38 8 16 32 64 128 256), losses := [] }

theorem u43779 : Upper (D 6) (R 6) [10,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43780 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43780 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43780 : Upper (D 6) (R 6) [10,96,48] 13 := by
  apply FastRouting.sound _ _ [10,96,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r43780 c43780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41694
  · exact u41695
  · exact u41696
  · exact u41697
  · exact u41698
  · exact u41699
  · exact u41700
  · exact u41701
  · exact u41702
  · exact u41703
  · exact u41704

def b43781 : PairBound 9 := { available := 407, camps := [{ cop := 1, region := 4, targets := 1 },{ cop := 1, region := 4, targets := 2 },{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 98 100 415 407 439 471 407 407), lower := (rows 11 98 100 8 16 32 64 128 256), losses := [] }

theorem u43781 : Upper (D 6) (R 6) [10,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43782 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43782 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43782 : Upper (D 6) (R 6) [10,96,129] 13 := by
  apply FastRouting.sound _ _ [10,96,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,257,258,260,272,288] r43782 c43782
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41705
  · exact u41706
  · exact u41707
  · exact u41708
  · exact u41709
  · exact u41710
  · exact u41711
  · exact u41712
  · exact u41713
  · exact u41714
  · exact u41715
  · exact u41716
  · exact u41717
  · exact u41718
  · exact u41719
  · exact u41720

def r43783 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43783 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43783 : Upper (D 6) (R 6) [10,96,130] 13 := by
  apply FastRouting.sound _ _ [10,96,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,96,257,260,272,288] r43783 c43783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41721
  · exact u41722
  · exact u41723
  · exact u41724
  · exact u41725
  · exact u41726
  · exact u41727
  · exact u41728
  · exact u41729
  · exact u41730
  · exact u41731

def r43784 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43784 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43784 : Upper (D 6) (R 6) [10,96,144] 13 := by
  apply FastRouting.sound _ _ [10,96,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r43784 c43784
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41732
  · exact u41733
  · exact u41734
  · exact u41735
  · exact u41736
  · exact u41737
  · exact u41738
  · exact u41739
  · exact u41740
  · exact u41741
  · exact u41742

def r43785 : Route 9 := (fun mask => (mask,id))

def c43785 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43785 : Upper (D 6) (R 6) [10,96,160] 13 := by
  apply FastRouting.sound _ _ [10,96,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43785 c43785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41743
  · exact u41744
  · exact u41745
  · exact u41746
  · exact u41747
  · exact u41748
  · exact u41749
  · exact u41750
  · exact u41751
  · exact u41752
  · exact u41753
  · exact u41754
  · exact u41755
  · exact u41756
  · exact u41757

def r43786 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43786 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43786 : Upper (D 6) (R 6) [10,96,384] 13 := by
  apply FastRouting.sound _ _ [10,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96] r43786 c43786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41758
  · exact u41759
  · exact u41760
  · exact u41761
  · exact u41762
  · exact u41763
  · exact u41764
  · exact u41765
  · exact u41766
  · exact u41767
  · exact u41768

def r43787 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43787 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43787 : Upper (D 6) (R 6) [10,129,18] 13 := by
  apply FastRouting.sound _ _ [10,129,18] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r43787 c43787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41769
  · exact u41770
  · exact u41771
  · exact u41772
  · exact u41773
  · exact u41774
  · exact u41775

def r43788 : Route 9 := (fun mask => (mask,id))

def c43788 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43788 : Upper (D 6) (R 6) [10,129,33] 13 := by
  apply FastRouting.sound _ _ [10,129,33] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,258,260,272,288,320] r43788 c43788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41776
  · exact u41777
  · exact u41778
  · exact u41779
  · exact u41780
  · exact u41781
  · exact u41782
  · exact u41783
  · exact u41784
  · exact u41785
  · exact u41786
  · exact u41787
  · exact u41788
  · exact u41789
  · exact u41790

def r43789 : Route 9 := (fun mask => (mask,id))

def c43789 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43789 : Upper (D 6) (R 6) [10,129,34] 13 := by
  apply FastRouting.sound _ _ [10,129,34] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43789 c43789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41791
  · exact u41792
  · exact u41793
  · exact u41794
  · exact u41795
  · exact u41796
  · exact u41797
  · exact u41798
  · exact u41799
  · exact u41800
  · exact u41801
  · exact u41802
  · exact u41803
  · exact u41804
  · exact u41805

def r43790 : Route 9 := (fun mask => (mask,id))

def c43790 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43790 : Upper (D 6) (R 6) [10,129,48] 13 := by
  apply FastRouting.sound _ _ [10,129,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43790 c43790
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41806
  · exact u41807
  · exact u41808
  · exact u41809
  · exact u41810
  · exact u41811
  · exact u41812
  · exact u41813
  · exact u41814
  · exact u41815
  · exact u41816
  · exact u41817
  · exact u41818
  · exact u41819
  · exact u41820

def r43791 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43791 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43791 : Upper (D 6) (R 6) [10,129,96] 13 := by
  apply FastRouting.sound _ _ [10,129,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,257,258,260,272,288] r43791 c43791
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41821
  · exact u41822
  · exact u41823
  · exact u41824
  · exact u41825
  · exact u41826
  · exact u41827
  · exact u41828
  · exact u41829
  · exact u41830
  · exact u41831
  · exact u41832
  · exact u41833
  · exact u41834
  · exact u41835
  · exact u41836

def r43792 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43792 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43792 : Upper (D 6) (R 6) [10,129,257] 13 := by
  apply FastRouting.sound _ _ [10,129,257] 13 (by decide) (choices 2) [6,18,20,34,36,48,96] r43792 c43792
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41837
  · exact u41838
  · exact u41839
  · exact u41840
  · exact u41841
  · exact u41842
  · exact u41843

def r43793 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43793 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43793 : Upper (D 6) (R 6) [10,129,258] 13 := by
  apply FastRouting.sound _ _ [10,129,258] 13 (by decide) (choices 2) [5,17,20,33,36,48,96] r43793 c43793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41844
  · exact u41845
  · exact u41846
  · exact u41847
  · exact u41848
  · exact u41849
  · exact u41850

def r43794 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43794 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43794 : Upper (D 6) (R 6) [10,129,272] 13 := by
  apply FastRouting.sound _ _ [10,129,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43794 c43794
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41851
  · exact u41852
  · exact u41853
  · exact u41854
  · exact u41855
  · exact u41856
  · exact u41857

def r43795 : Route 9 := (fun mask => (mask,id))

def c43795 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43795 : Upper (D 6) (R 6) [10,129,288] 13 := by
  apply FastRouting.sound _ _ [10,129,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43795 c43795
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41858
  · exact u41859
  · exact u41860
  · exact u41861
  · exact u41862
  · exact u41863
  · exact u41864
  · exact u41865
  · exact u41866
  · exact u41867
  · exact u41868
  · exact u41869
  · exact u41870
  · exact u41871
  · exact u41872

def r43796 : Route 9 := (fun mask => (mask,id))

def c43796 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43796 : Upper (D 6) (R 6) [10,132,33] 13 := by
  apply FastRouting.sound _ _ [10,132,33] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43796 c43796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41873
  · exact u41874
  · exact u41875
  · exact u41876
  · exact u41877
  · exact u41878
  · exact u41879
  · exact u41880
  · exact u41881
  · exact u41882
  · exact u41883
  · exact u41884
  · exact u41885
  · exact u41886
  · exact u41887
  · exact u41888
  · exact u41889
  · exact u41890
  · exact u41891
  · exact u41892
  · exact u41893

def r43797 : Route 9 := (fun mask => (mask,id))

def c43797 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43797 : Upper (D 6) (R 6) [10,132,34] 13 := by
  apply FastRouting.sound _ _ [10,132,34] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43797 c43797
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41894
  · exact u41895
  · exact u41896
  · exact u41897
  · exact u41898
  · exact u41899
  · exact u41900
  · exact u41901
  · exact u41902
  · exact u41903
  · exact u41904
  · exact u41905
  · exact u41906
  · exact u41907
  · exact u41908

def r43798 : Route 9 := (fun mask => (mask,id))

def c43798 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43798 : Upper (D 6) (R 6) [10,132,48] 13 := by
  apply FastRouting.sound _ _ [10,132,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43798 c43798
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41909
  · exact u41910
  · exact u41911
  · exact u41912
  · exact u41913
  · exact u41914
  · exact u41915
  · exact u41916
  · exact u41917
  · exact u41918
  · exact u41919
  · exact u41920
  · exact u41921
  · exact u41922
  · exact u41923

def r43799 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43799 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43799 : Upper (D 6) (R 6) [10,132,96] 13 := by
  apply FastRouting.sound _ _ [10,132,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,257,258,260,272,288] r43799 c43799
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41924
  · exact u41925
  · exact u41926
  · exact u41927
  · exact u41928
  · exact u41929
  · exact u41930
  · exact u41931
  · exact u41932
  · exact u41933
  · exact u41934
  · exact u41935
  · exact u41936
  · exact u41937
  · exact u41938
  · exact u41939

#print axioms u43799
end Delivery.IrregularNine14.P06
