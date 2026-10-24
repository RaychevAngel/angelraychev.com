import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0688
import IrregularNine14P07C0689
import IrregularNine14P07C0690
import IrregularNine14P07C0691
import IrregularNine14P07C0692
import IrregularNine14P07C0693
import IrregularNine14P07C0694

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b44040 : PairBound 9 := { available := 505, camps := [{ cop := 1, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 98 7 505 505 505 505 505 505), lower := (rows 7 98 7 8 16 32 64 128 256), losses := [] }

theorem u44040 : Upper (D 7) (R 7) [6,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44041 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44041 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44041 : Upper (D 7) (R 7) [6,96,9] 13 := by
  apply FastRouting.sound _ _ [6,96,9] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160,257,258,272,288,384] r44041 c44041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact u41324
  · exact u41325
  · exact u41326
  · exact u41327

def b44042 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 98 14 505 497 497 497 497 497), lower := (rows 7 98 14 8 16 32 64 128 256), losses := [] }

theorem u44042 : Upper (D 7) (R 7) [6,96,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44043 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44043 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44043 : Upper (D 7) (R 7) [6,96,24] 13 := by
  apply FastRouting.sound _ _ [6,96,24] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r44043 c44043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b44044 : PairBound 9 := { available := 475, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 37 475 475 507 475 475 475), lower := (rows 7 98 37 8 16 32 64 128 256), losses := [] }

theorem u44044 : Upper (D 7) (R 7) [6,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44045 : PairBound 9 := { available := 473, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 38 473 473 505 473 473 473), lower := (rows 7 98 38 8 16 32 64 128 256), losses := [] }

theorem u44045 : Upper (D 7) (R 7) [6,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44046 : Route 9 := (fun mask => (mask,id))

def c44046 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44046 : Upper (D 7) (R 7) [6,96,40] 13 := by
  apply FastRouting.sound _ _ [6,96,40] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192,257,258,272,320,384] r44046 c44046
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

def b44047 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 98 100 411 411 443 475 411 411), lower := (rows 7 98 100 8 16 32 64 128 256), losses := [] }

theorem u44047 : Upper (D 7) (R 7) [6,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44048 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44048 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44048 : Upper (D 7) (R 7) [6,96,129] 13 := by
  apply FastRouting.sound _ _ [6,96,129] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160,257,258,272,288,384] r44048 c44048
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact u41369

def b44049 : PairBound 9 := { available := 505, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 98 134 505 505 505 505 505 505), lower := (rows 7 98 134 8 16 32 64 128 256), losses := [] }

theorem u44049 : Upper (D 7) (R 7) [6,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44050 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44050 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44050 : Upper (D 7) (R 7) [6,96,136] 13 := by
  apply FastRouting.sound _ _ [6,96,136] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160,257,258,272,288,384] r44050 c44050
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact u41384
  · exact u41385

def r44051 : Route 9 := (fun mask => (mask,id))

def c44051 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44051 : Upper (D 7) (R 7) [6,96,160] 13 := by
  apply FastRouting.sound _ _ [6,96,160] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192,257,258,272,320,384] r44051 c44051
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44052 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44052 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44052 : Upper (D 7) (R 7) [6,96,257] 13 := by
  apply FastRouting.sound _ _ [6,96,257] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44052 c44052
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41401
  · exact u41402
  · exact u41403
  · exact u41404
  · exact u41405
  · exact u41406
  · exact u41407
  · exact u41408
  · exact u41409
  · exact u41410
  · exact u41411

def b44053 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 98 262 249 249 249 249 249 505), lower := (rows 7 98 262 8 16 32 64 128 256), losses := [] }

theorem u44053 : Upper (D 7) (R 7) [6,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44054 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44054 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44054 : Upper (D 7) (R 7) [6,96,264] 13 := by
  apply FastRouting.sound _ _ [6,96,264] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44054 c44054
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41412
  · exact u41413
  · exact u41414
  · exact u41415
  · exact u41416
  · exact u41417
  · exact u41418
  · exact u41419
  · exact u41420
  · exact u41421
  · exact u41422

def r44055 : Route 9 := (fun mask => (mask,id))

def c44055 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44055 : Upper (D 7) (R 7) [6,96,288] 13 := by
  apply FastRouting.sound _ _ [6,96,288] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44055 c44055
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44056 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44056 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44056 : Upper (D 7) (R 7) [6,96,384] 13 := by
  apply FastRouting.sound _ _ [6,96,384] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44056 c44056
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41433
  · exact u41434
  · exact u41435
  · exact u41436
  · exact u41437
  · exact u41438
  · exact u41439
  · exact u41440
  · exact u41441
  · exact u41442
  · exact u41443

def b44057 : PairBound 9 := { available := 248, camps := [{ cop := 8, region := 7, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(1,5)], upper := (rows 7 259 7 248 248 248 248 248 504), lower := (rows 7 259 7 8 16 32 64 128 256), losses := [] }

theorem u44057 : Upper (D 7) (R 7) [6,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44058 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44058 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44058 : Upper (D 7) (R 7) [6,257,9] 13 := by
  apply FastRouting.sound _ _ [6,257,9] 13 (by decide) (choices 2) [18,34,48,96] r44058 c44058
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u41444
  · exact u41445
  · exact u41446
  · exact u41447

def b44059 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 259 14 249 241 241 241 241 497), lower := (rows 7 259 14 8 16 32 64 128 256), losses := [] }

theorem u44059 : Upper (D 7) (R 7) [6,257,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44060 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44060 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44060 : Upper (D 7) (R 7) [6,257,24] 13 := by
  apply FastRouting.sound _ _ [6,257,24] 13 (by decide) (choices 2) [3,33,34,96] r44060 c44060
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u41448
  · exact u41449
  · exact u41450
  · exact u41451

def r44061 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44061 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44061 : Upper (D 7) (R 7) [6,257,33] 13 := by
  apply FastRouting.sound _ _ [6,257,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r44061 c44061
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41452
  · exact u41453
  · exact u41454
  · exact u41455
  · exact u41456
  · exact u41457
  · exact u41458

def b44062 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 259 38 249 249 249 249 249 505), lower := (rows 7 259 38 8 16 32 64 128 256), losses := [] }

theorem u44062 : Upper (D 7) (R 7) [6,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44063 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44063 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44063 : Upper (D 7) (R 7) [6,257,40] 13 := by
  apply FastRouting.sound _ _ [6,257,40] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44063 c44063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44064 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44064 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44064 : Upper (D 7) (R 7) [6,257,96] 13 := by
  apply FastRouting.sound _ _ [6,257,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44064 c44064
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41470
  · exact u41471
  · exact u41472
  · exact u41473
  · exact u41474
  · exact u41475
  · exact u41476
  · exact u41477
  · exact u41478
  · exact u41479
  · exact u41480

def b44065 : PairBound 9 := { available := 241, camps := [{ cop := 1, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 266 7 249 241 241 241 241 497), lower := (rows 7 266 7 8 16 32 64 128 256), losses := [] }

theorem u44065 : Upper (D 7) (R 7) [6,264,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44066 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44066 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44066 : Upper (D 7) (R 7) [6,264,17] 13 := by
  apply FastRouting.sound _ _ [6,264,17] 13 (by decide) (choices 2) [3,33,34,96] r44066 c44066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u41481
  · exact u41482
  · exact u41483
  · exact u41484

def b44067 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 232, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 266 22 233 241 225 225 225 481), lower := (rows 7 266 22 8 16 32 64 128 256), losses := [] }

theorem u44067 : Upper (D 7) (R 7) [6,264,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44068 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44068 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44068 : Upper (D 7) (R 7) [6,264,33] 13 := by
  apply FastRouting.sound _ _ [6,264,33] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44068 c44068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact u41495

def b44069 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 266 38 249 241 241 241 241 497), lower := (rows 7 266 38 8 16 32 64 128 256), losses := [] }

theorem u44069 : Upper (D 7) (R 7) [6,264,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44070 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44070 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44070 : Upper (D 7) (R 7) [6,264,48] 13 := by
  apply FastRouting.sound _ _ [6,264,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r44070 c44070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41496
  · exact u41497
  · exact u41498
  · exact u41499
  · exact u41500
  · exact u41501
  · exact u41502

def r44071 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44071 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44071 : Upper (D 7) (R 7) [6,264,96] 13 := by
  apply FastRouting.sound _ _ [6,264,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44071 c44071
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41503
  · exact u41504
  · exact u41505
  · exact u41506
  · exact u41507
  · exact u41508
  · exact u41509
  · exact u41510
  · exact u41511
  · exact u41512
  · exact u41513

def b44072 : PairBound 9 := { available := 249, camps := [{ cop := 1, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 290 7 249 249 249 249 249 505), lower := (rows 7 290 7 8 16 32 64 128 256), losses := [] }

theorem u44072 : Upper (D 7) (R 7) [6,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44073 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44073 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44073 : Upper (D 7) (R 7) [6,288,9] 13 := by
  apply FastRouting.sound _ _ [6,288,9] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44073 c44073
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b44074 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 290 14 249 241 241 241 241 497), lower := (rows 7 290 14 8 16 32 64 128 256), losses := [] }

theorem u44074 : Upper (D 7) (R 7) [6,288,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44075 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44075 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44075 : Upper (D 7) (R 7) [6,288,24] 13 := by
  apply FastRouting.sound _ _ [6,288,24] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r44075 c44075
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41525
  · exact u41526
  · exact u41527
  · exact u41528
  · exact u41529
  · exact u41530
  · exact u41531

def b44076 : PairBound 9 := { available := 219, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 37 219 219 251 219 219 475), lower := (rows 7 290 37 8 16 32 64 128 256), losses := [] }

theorem u44076 : Upper (D 7) (R 7) [6,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44077 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 38 217 217 249 217 217 473), lower := (rows 7 290 38 8 16 32 64 128 256), losses := [] }

theorem u44077 : Upper (D 7) (R 7) [6,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44078 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44078 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44078 : Upper (D 7) (R 7) [6,288,40] 13 := by
  apply FastRouting.sound _ _ [6,288,40] 13 (by decide) (choices 2) [3,17,18,65,66,80,192] r44078 c44078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41532
  · exact u41533
  · exact u41534
  · exact u41535
  · exact u41536
  · exact u41537
  · exact u41538

def r44079 : Route 9 := (fun mask => (mask,id))

def c44079 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44079 : Upper (D 7) (R 7) [6,288,65] 13 := by
  apply FastRouting.sound _ _ [6,288,65] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44079 c44079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41539
  · exact u41540
  · exact u41541
  · exact u41542
  · exact u41543
  · exact u41544
  · exact u41545
  · exact u41546
  · exact u41547
  · exact u41548
  · exact u41549
  · exact u41550
  · exact u41551
  · exact u41552
  · exact u41553

def b44080 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 248, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 290 70 249 249 249 249 249 505), lower := (rows 7 290 70 8 16 32 64 128 256), losses := [] }

theorem u44080 : Upper (D 7) (R 7) [6,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44081 : Route 9 := (fun mask => (mask,id))

def c44081 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44081 : Upper (D 7) (R 7) [6,288,72] 13 := by
  apply FastRouting.sound _ _ [6,288,72] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44081 c44081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41554
  · exact u41555
  · exact u41556
  · exact u41557
  · exact u41558
  · exact u41559
  · exact u41560
  · exact u41561
  · exact u41562
  · exact u41563
  · exact u41564
  · exact u41565
  · exact u41566
  · exact u41567
  · exact u41568

def r44082 : Route 9 := (fun mask => (mask,id))

def c44082 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44082 : Upper (D 7) (R 7) [6,288,96] 13 := by
  apply FastRouting.sound _ _ [6,288,96] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44082 c44082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41569
  · exact u41570
  · exact u41571
  · exact u41572
  · exact u41573
  · exact u41574
  · exact u41575
  · exact u41576
  · exact u41577
  · exact u41578

def r44083 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44083 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44083 : Upper (D 7) (R 7) [6,288,192] 13 := by
  apply FastRouting.sound _ _ [6,288,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44083 c44083
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41579
  · exact u41580
  · exact u41581
  · exact u41582
  · exact u41583
  · exact u41584
  · exact u41585
  · exact u41586
  · exact u41587
  · exact u41588
  · exact u41589

def b44084 : PairBound 9 := { available := 498, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 1, region := 472, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 13 35 7 506 498 498 498 498 498), lower := (rows 13 35 7 8 16 32 64 128 256), losses := [] }

theorem u44084 : Upper (D 7) (R 7) [12,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44085 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44085 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44085 : Upper (D 7) (R 7) [12,33,17] 13 := by
  apply FastRouting.sound _ _ [12,33,17] 13 (by decide) (choices 2) [34,66,96,192,258,288,320] r44085 c44085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41600
  · exact u41601
  · exact u41602
  · exact u41603
  · exact u41604
  · exact u41605
  · exact u41606

theorem m44086_3 : Upper (D 7) (R 7) [12,33,18,3] 13 :=
  permutation_upper _ _ _ [12,33,3,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41590

def r44086 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44086 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44086 : Upper (D 7) (R 7) [12,33,18] 13 := by
  apply FastRouting.sound _ _ [12,33,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r44086 c44086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44086_3
  · exact u41607
  · exact u41608
  · exact u41609
  · exact u41610
  · exact u41611
  · exact u41612
  · exact u41613
  · exact u41614
  · exact u41615
  · exact u41616

def b44087 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 37 474 466 498 466 466 466), lower := (rows 13 35 37 8 16 32 64 128 256), losses := [] }

theorem u44087 : Upper (D 7) (R 7) [12,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44088 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 35 38 475 467 499 467 467 467), lower := (rows 13 35 38 8 16 32 64 128 256), losses := [] }

theorem u44088 : Upper (D 7) (R 7) [12,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44089_3 : Upper (D 7) (R 7) [12,33,48,3] 13 :=
  permutation_upper _ _ _ [12,33,3,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41591

def r44089 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44089 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44089 : Upper (D 7) (R 7) [12,33,48] 13 := by
  apply FastRouting.sound _ _ [12,33,48] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r44089 c44089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44089_3
  · exact u41631
  · exact u41632
  · exact u41633
  · exact u41634
  · exact u41635
  · exact u41636

theorem m44090_18 : Upper (D 7) (R 7) [12,33,65,18] 13 :=
  permutation_upper _ _ _ [12,33,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41609

theorem m44090_34 : Upper (D 7) (R 7) [12,33,65,34] 13 :=
  permutation_upper _ _ _ [12,33,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41623

theorem m44090_48 : Upper (D 7) (R 7) [12,33,65,48] 13 :=
  permutation_upper _ _ _ [12,33,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41631

def r44090 : Route 9 := (fun mask => (mask,id))

def c44090 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44090 : Upper (D 7) (R 7) [12,33,65] 13 := by
  apply FastRouting.sound _ _ [12,33,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192,258,272,288,320,384] r44090 c44090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44090_18
  · exact m44090_34
  · exact m44090_48
  · exact u41637
  · exact u41638
  · exact u41639
  · exact u41640
  · exact u41641
  · exact u41642
  · exact u41643
  · exact u41644
  · exact u41645
  · exact u41646
  · exact u41647
  · exact u41648

theorem m44091_3 : Upper (D 7) (R 7) [12,33,66,3] 13 :=
  permutation_upper _ _ _ [12,33,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41592

theorem m44091_17 : Upper (D 7) (R 7) [12,33,66,17] 13 :=
  permutation_upper _ _ _ [12,33,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41601

theorem m44091_18 : Upper (D 7) (R 7) [12,33,66,18] 13 :=
  permutation_upper _ _ _ [12,33,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41610

theorem m44091_33 : Upper (D 7) (R 7) [12,33,66,33] 13 :=
  permutation_upper _ _ _ [12,33,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41617

theorem m44091_34 : Upper (D 7) (R 7) [12,33,66,34] 13 :=
  permutation_upper _ _ _ [12,33,34,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41624

theorem m44091_48 : Upper (D 7) (R 7) [12,33,66,48] 13 :=
  permutation_upper _ _ _ [12,33,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41632

theorem m44091_65 : Upper (D 7) (R 7) [12,33,66,65] 13 :=
  permutation_upper _ _ _ [12,33,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41637

theorem m44091_129 : Upper (D 7) (R 7) [12,33,66,129] 13 :=
  permutation_upper _ _ _ [12,33,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41640

def r44091 : Route 9 := (fun mask => (mask,id))

def c44091 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44091 : Upper (D 7) (R 7) [12,33,66] 13 := by
  apply FastRouting.sound _ _ [12,33,66] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192,257,258,272,288,320,384] r44091 c44091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44091_3
  · exact m44091_17
  · exact m44091_18
  · exact m44091_33
  · exact m44091_34
  · exact m44091_48
  · exact m44091_65
  · exact u41649
  · exact u41650
  · exact u41651
  · exact m44091_129
  · exact u41652
  · exact u41653
  · exact u41654
  · exact u41655
  · exact u41656
  · exact u41657
  · exact u41658
  · exact u41659
  · exact u41660
  · exact u41661

theorem m44092_3 : Upper (D 7) (R 7) [12,33,80,3] 13 :=
  permutation_upper _ _ _ [12,33,3,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41593

theorem m44092_33 : Upper (D 7) (R 7) [12,33,80,33] 13 :=
  permutation_upper _ _ _ [12,33,33,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41618

theorem m44092_34 : Upper (D 7) (R 7) [12,33,80,34] 13 :=
  permutation_upper _ _ _ [12,33,34,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41625

theorem m44092_65 : Upper (D 7) (R 7) [12,33,80,65] 13 :=
  permutation_upper _ _ _ [12,33,65,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41638

theorem m44092_66 : Upper (D 7) (R 7) [12,33,80,66] 13 :=
  permutation_upper _ _ _ [12,33,66,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41650

theorem m44092_129 : Upper (D 7) (R 7) [12,33,80,129] 13 :=
  permutation_upper _ _ _ [12,33,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41641

theorem m44092_130 : Upper (D 7) (R 7) [12,33,80,130] 13 :=
  permutation_upper _ _ _ [12,33,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41653

def r44092 : Route 9 := (fun mask => (mask,id))

def c44092 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44092 : Upper (D 7) (R 7) [12,33,80] 13 := by
  apply FastRouting.sound _ _ [12,33,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r44092 c44092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44092_3
  · exact m44092_33
  · exact m44092_34
  · exact m44092_65
  · exact m44092_66
  · exact u41662
  · exact m44092_129
  · exact m44092_130
  · exact u41663
  · exact u41664
  · exact u41665
  · exact u41666
  · exact u41667
  · exact u41668
  · exact u41669

theorem m44093_3 : Upper (D 7) (R 7) [12,33,96,3] 13 :=
  permutation_upper _ _ _ [12,33,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41594

theorem m44093_17 : Upper (D 7) (R 7) [12,33,96,17] 13 :=
  permutation_upper _ _ _ [12,33,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41602

theorem m44093_18 : Upper (D 7) (R 7) [12,33,96,18] 13 :=
  permutation_upper _ _ _ [12,33,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41611

theorem m44093_65 : Upper (D 7) (R 7) [12,33,96,65] 13 :=
  permutation_upper _ _ _ [12,33,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41639

theorem m44093_66 : Upper (D 7) (R 7) [12,33,96,66] 13 :=
  permutation_upper _ _ _ [12,33,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41651

theorem m44093_80 : Upper (D 7) (R 7) [12,33,96,80] 13 :=
  permutation_upper _ _ _ [12,33,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41662

theorem m44093_129 : Upper (D 7) (R 7) [12,33,96,129] 13 :=
  permutation_upper _ _ _ [12,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41642

theorem m44093_130 : Upper (D 7) (R 7) [12,33,96,130] 13 :=
  permutation_upper _ _ _ [12,33,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41654

theorem m44093_144 : Upper (D 7) (R 7) [12,33,96,144] 13 :=
  permutation_upper _ _ _ [12,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41663

def r44093 : Route 9 := (fun mask => (mask,id))

def c44093 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44093 : Upper (D 7) (R 7) [12,33,96] 13 := by
  apply FastRouting.sound _ _ [12,33,96] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192,257,258,272,320,384] r44093 c44093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44093_3
  · exact m44093_17
  · exact m44093_18
  · exact m44093_65
  · exact m44093_66
  · exact m44093_80
  · exact m44093_129
  · exact m44093_130
  · exact m44093_144
  · exact u41670
  · exact u41671
  · exact u41672
  · exact u41673
  · exact u41674
  · exact u41675

theorem m44094_3 : Upper (D 7) (R 7) [12,33,192,3] 13 :=
  permutation_upper _ _ _ [12,33,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41595

theorem m44094_17 : Upper (D 7) (R 7) [12,33,192,17] 13 :=
  permutation_upper _ _ _ [12,33,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41603

theorem m44094_18 : Upper (D 7) (R 7) [12,33,192,18] 13 :=
  permutation_upper _ _ _ [12,33,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41612

theorem m44094_33 : Upper (D 7) (R 7) [12,33,192,33] 13 :=
  permutation_upper _ _ _ [12,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41619

theorem m44094_34 : Upper (D 7) (R 7) [12,33,192,34] 13 :=
  permutation_upper _ _ _ [12,33,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41626

theorem m44094_48 : Upper (D 7) (R 7) [12,33,192,48] 13 :=
  permutation_upper _ _ _ [12,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41633

theorem m44094_65 : Upper (D 7) (R 7) [12,33,192,65] 13 :=
  permutation_upper _ _ _ [12,33,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41643

theorem m44094_66 : Upper (D 7) (R 7) [12,33,192,66] 13 :=
  permutation_upper _ _ _ [12,33,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41655

theorem m44094_80 : Upper (D 7) (R 7) [12,33,192,80] 13 :=
  permutation_upper _ _ _ [12,33,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41664

theorem m44094_96 : Upper (D 7) (R 7) [12,33,192,96] 13 :=
  permutation_upper _ _ _ [12,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41670

def r44094 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44094 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44094 : Upper (D 7) (R 7) [12,33,192] 13 := by
  apply FastRouting.sound _ _ [12,33,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r44094 c44094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44094_3
  · exact m44094_17
  · exact m44094_18
  · exact m44094_33
  · exact m44094_34
  · exact m44094_48
  · exact m44094_65
  · exact m44094_66
  · exact m44094_80
  · exact m44094_96
  · exact u41676
  · exact u41677
  · exact u41678
  · exact u41679
  · exact u41680
  · exact u41681

theorem m44095_18 : Upper (D 7) (R 7) [12,33,257,18] 13 :=
  permutation_upper _ _ _ [12,33,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41613

theorem m44095_34 : Upper (D 7) (R 7) [12,33,257,34] 13 :=
  permutation_upper _ _ _ [12,33,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41627

theorem m44095_48 : Upper (D 7) (R 7) [12,33,257,48] 13 :=
  permutation_upper _ _ _ [12,33,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41634

theorem m44095_66 : Upper (D 7) (R 7) [12,33,257,66] 13 :=
  permutation_upper _ _ _ [12,33,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41656

theorem m44095_80 : Upper (D 7) (R 7) [12,33,257,80] 13 :=
  permutation_upper _ _ _ [12,33,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41665

theorem m44095_96 : Upper (D 7) (R 7) [12,33,257,96] 13 :=
  permutation_upper _ _ _ [12,33,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41671

theorem m44095_192 : Upper (D 7) (R 7) [12,33,257,192] 13 :=
  permutation_upper _ _ _ [12,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41677

def r44095 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44095 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44095 : Upper (D 7) (R 7) [12,33,257] 13 := by
  apply FastRouting.sound _ _ [12,33,257] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r44095 c44095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44095_18
  · exact m44095_34
  · exact m44095_48
  · exact m44095_66
  · exact m44095_80
  · exact m44095_96
  · exact m44095_192

theorem m44096_3 : Upper (D 7) (R 7) [12,33,258,3] 13 :=
  permutation_upper _ _ _ [12,33,3,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41596

theorem m44096_17 : Upper (D 7) (R 7) [12,33,258,17] 13 :=
  permutation_upper _ _ _ [12,33,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41604

theorem m44096_18 : Upper (D 7) (R 7) [12,33,258,18] 13 :=
  permutation_upper _ _ _ [12,33,18,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41614

theorem m44096_33 : Upper (D 7) (R 7) [12,33,258,33] 13 :=
  permutation_upper _ _ _ [12,33,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41620

theorem m44096_34 : Upper (D 7) (R 7) [12,33,258,34] 13 :=
  permutation_upper _ _ _ [12,33,34,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41628

theorem m44096_48 : Upper (D 7) (R 7) [12,33,258,48] 13 :=
  permutation_upper _ _ _ [12,33,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41635

theorem m44096_65 : Upper (D 7) (R 7) [12,33,258,65] 13 :=
  permutation_upper _ _ _ [12,33,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41644

theorem m44096_66 : Upper (D 7) (R 7) [12,33,258,66] 13 :=
  permutation_upper _ _ _ [12,33,66,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41657

theorem m44096_80 : Upper (D 7) (R 7) [12,33,258,80] 13 :=
  permutation_upper _ _ _ [12,33,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41666

theorem m44096_96 : Upper (D 7) (R 7) [12,33,258,96] 13 :=
  permutation_upper _ _ _ [12,33,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41672

theorem m44096_192 : Upper (D 7) (R 7) [12,33,258,192] 13 :=
  permutation_upper _ _ _ [12,33,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41678

def r44096 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44096 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44096 : Upper (D 7) (R 7) [12,33,258] 13 := by
  apply FastRouting.sound _ _ [12,33,258] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44096 c44096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44096_3
  · exact m44096_17
  · exact m44096_18
  · exact m44096_33
  · exact m44096_34
  · exact m44096_48
  · exact m44096_65
  · exact m44096_66
  · exact m44096_80
  · exact m44096_96
  · exact m44096_192

theorem m44097_3 : Upper (D 7) (R 7) [12,33,272,3] 13 :=
  permutation_upper _ _ _ [12,33,3,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41597

theorem m44097_33 : Upper (D 7) (R 7) [12,33,272,33] 13 :=
  permutation_upper _ _ _ [12,33,33,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41621

theorem m44097_34 : Upper (D 7) (R 7) [12,33,272,34] 13 :=
  permutation_upper _ _ _ [12,33,34,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41629

theorem m44097_65 : Upper (D 7) (R 7) [12,33,272,65] 13 :=
  permutation_upper _ _ _ [12,33,65,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41645

theorem m44097_66 : Upper (D 7) (R 7) [12,33,272,66] 13 :=
  permutation_upper _ _ _ [12,33,66,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41658

theorem m44097_96 : Upper (D 7) (R 7) [12,33,272,96] 13 :=
  permutation_upper _ _ _ [12,33,96,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41673

theorem m44097_192 : Upper (D 7) (R 7) [12,33,272,192] 13 :=
  permutation_upper _ _ _ [12,33,192,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41679

def r44097 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44097 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44097 : Upper (D 7) (R 7) [12,33,272] 13 := by
  apply FastRouting.sound _ _ [12,33,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r44097 c44097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44097_3
  · exact m44097_33
  · exact m44097_34
  · exact m44097_65
  · exact m44097_66
  · exact m44097_96
  · exact m44097_192

theorem m44098_3 : Upper (D 7) (R 7) [12,33,288,3] 13 :=
  permutation_upper _ _ _ [12,33,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41598

theorem m44098_17 : Upper (D 7) (R 7) [12,33,288,17] 13 :=
  permutation_upper _ _ _ [12,33,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41605

theorem m44098_18 : Upper (D 7) (R 7) [12,33,288,18] 13 :=
  permutation_upper _ _ _ [12,33,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41615

theorem m44098_65 : Upper (D 7) (R 7) [12,33,288,65] 13 :=
  permutation_upper _ _ _ [12,33,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41646

theorem m44098_66 : Upper (D 7) (R 7) [12,33,288,66] 13 :=
  permutation_upper _ _ _ [12,33,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41659

theorem m44098_80 : Upper (D 7) (R 7) [12,33,288,80] 13 :=
  permutation_upper _ _ _ [12,33,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41667

theorem m44098_192 : Upper (D 7) (R 7) [12,33,288,192] 13 :=
  permutation_upper _ _ _ [12,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41680

def r44098 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44098 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44098 : Upper (D 7) (R 7) [12,33,288] 13 := by
  apply FastRouting.sound _ _ [12,33,288] 13 (by decide) (choices 2) [3,17,18,65,66,80,192] r44098 c44098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44098_3
  · exact m44098_17
  · exact m44098_18
  · exact m44098_65
  · exact m44098_66
  · exact m44098_80
  · exact m44098_192

theorem m44099_3 : Upper (D 7) (R 7) [12,33,320,3] 13 :=
  permutation_upper _ _ _ [12,33,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41599

theorem m44099_17 : Upper (D 7) (R 7) [12,33,320,17] 13 :=
  permutation_upper _ _ _ [12,33,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41606

theorem m44099_18 : Upper (D 7) (R 7) [12,33,320,18] 13 :=
  permutation_upper _ _ _ [12,33,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41616

theorem m44099_33 : Upper (D 7) (R 7) [12,33,320,33] 13 :=
  permutation_upper _ _ _ [12,33,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41622

theorem m44099_34 : Upper (D 7) (R 7) [12,33,320,34] 13 :=
  permutation_upper _ _ _ [12,33,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41630

theorem m44099_48 : Upper (D 7) (R 7) [12,33,320,48] 13 :=
  permutation_upper _ _ _ [12,33,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41636

theorem m44099_65 : Upper (D 7) (R 7) [12,33,320,65] 13 :=
  permutation_upper _ _ _ [12,33,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41647

theorem m44099_66 : Upper (D 7) (R 7) [12,33,320,66] 13 :=
  permutation_upper _ _ _ [12,33,66,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41660

theorem m44099_80 : Upper (D 7) (R 7) [12,33,320,80] 13 :=
  permutation_upper _ _ _ [12,33,80,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41668

theorem m44099_96 : Upper (D 7) (R 7) [12,33,320,96] 13 :=
  permutation_upper _ _ _ [12,33,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41674

theorem m44099_129 : Upper (D 7) (R 7) [12,33,320,129] 13 :=
  permutation_upper _ _ _ [12,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41648

theorem m44099_130 : Upper (D 7) (R 7) [12,33,320,130] 13 :=
  permutation_upper _ _ _ [12,33,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41661

theorem m44099_144 : Upper (D 7) (R 7) [12,33,320,144] 13 :=
  permutation_upper _ _ _ [12,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41669

theorem m44099_160 : Upper (D 7) (R 7) [12,33,320,160] 13 :=
  permutation_upper _ _ _ [12,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41675

theorem m44099_192 : Upper (D 7) (R 7) [12,33,320,192] 13 :=
  permutation_upper _ _ _ [12,33,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u41681

def r44099 : Route 9 := (fun mask => (mask,id))

def c44099 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44099 : Upper (D 7) (R 7) [12,33,320] 13 := by
  apply FastRouting.sound _ _ [12,33,320] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44099 c44099
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44099_3
  · exact m44099_17
  · exact m44099_18
  · exact m44099_33
  · exact m44099_34
  · exact m44099_48
  · exact m44099_65
  · exact m44099_66
  · exact m44099_80
  · exact m44099_96
  · exact m44099_129
  · exact m44099_130
  · exact m44099_144
  · exact m44099_160
  · exact m44099_192

#print axioms u44099
end Delivery.IrregularNine14.P07
