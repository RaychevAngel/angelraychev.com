import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0105
import IrregularNine14P05C0106
import IrregularNine14P05C0107
import IrregularNine14P05C0108
import IrregularNine14P05C0109
import IrregularNine14P05C0110

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9060 : Route 9 := (fun mask => (mask,id))

def c9060 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9060 : Upper (D 5) (R 5) [6,48,192,288] 13 := by
  apply FastRouting.sound _ _ [6,48,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9060 c9060
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6305
  · exact u6306
  · exact u6307
  · exact u6308
  · exact u6309
  · exact u6310

def b9061 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 133 14 312 312 376 440 312), lower := (rows 7 67 133 14 16 32 64 128 256), losses := [] }

theorem u9061 : Upper (D 5) (R 5) [6,65,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9061
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9062 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 133 26 316 300 364 428 300), lower := (rows 7 67 133 26 16 32 64 128 256), losses := [] }

theorem u9062 : Upper (D 5) (R 5) [6,65,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9062
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9063 : PairBound 9 := { available := 316, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 133 42 316 316 380 444 316), lower := (rows 7 67 133 42 16 32 64 128 256), losses := [] }

theorem u9063 : Upper (D 5) (R 5) [6,65,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9064 : PairBound 9 := { available := 302, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 133 56 318 302 366 430 302), lower := (rows 7 67 133 56 16 32 64 128 256), losses := [] }

theorem u9064 : Upper (D 5) (R 5) [6,65,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9064
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9065 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 133 266 60 60 124 188 316), lower := (rows 7 67 133 266 16 32 64 128 256), losses := [] }

theorem u9065 : Upper (D 5) (R 5) [6,65,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9065
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9066 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 133 280 62 46 110 174 302), lower := (rows 7 67 133 280 16 32 64 128 256), losses := [] }

theorem u9066 : Upper (D 5) (R 5) [6,65,129,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9066
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9067 : PairBound 9 := { available := 62, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 133 296 62 62 126 190 318), lower := (rows 7 67 133 296 16 32 64 128 256), losses := [] }

theorem u9067 : Upper (D 5) (R 5) [6,65,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9067
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9068 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 25 316 300 364 428 300), lower := (rows 7 67 134 25 16 32 64 128 256), losses := [] }

theorem u9068 : Upper (D 5) (R 5) [6,65,130,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9068
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9069 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 28 313 297 361 425 297), lower := (rows 7 67 134 28 16 32 64 128 256), losses := [] }

theorem u9069 : Upper (D 5) (R 5) [6,65,130,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9069
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9070 : PairBound 9 := { available := 316, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 41 316 316 380 444 316), lower := (rows 7 67 134 41 16 32 64 128 256), losses := [] }

theorem u9070 : Upper (D 5) (R 5) [6,65,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9070
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9071 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 44 313 313 377 441 313), lower := (rows 7 67 134 44 16 32 64 128 256), losses := [] }

theorem u9071 : Upper (D 5) (R 5) [6,65,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9071
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9072 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 56 317 301 365 429 301), lower := (rows 7 67 134 56 16 32 64 128 256), losses := [] }

theorem u9072 : Upper (D 5) (R 5) [6,65,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9072
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9073 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 265 60 60 124 188 316), lower := (rows 7 67 134 265 16 32 64 128 256), losses := [] }

theorem u9073 : Upper (D 5) (R 5) [6,65,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9073
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9074 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 268 57 57 121 185 313), lower := (rows 7 67 134 268 16 32 64 128 256), losses := [] }

theorem u9074 : Upper (D 5) (R 5) [6,65,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9074
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9075 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 280 61 45 109 173 301), lower := (rows 7 67 134 280 16 32 64 128 256), losses := [] }

theorem u9075 : Upper (D 5) (R 5) [6,65,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9075
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9076 : PairBound 9 := { available := 61, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 134 296 61 61 125 189 317), lower := (rows 7 67 134 296 16 32 64 128 256), losses := [] }

theorem u9076 : Upper (D 5) (R 5) [6,65,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9076
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9077 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 67 140 14 313 313 377 441 313), lower := (rows 7 67 140 14 16 32 64 128 256), losses := [] }

theorem u9077 : Upper (D 5) (R 5) [6,65,136,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9077
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9078 : Route 9 := (fun mask => (mask,id))

def c9078 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9078 : Upper (D 5) (R 5) [6,65,136,17] 13 := by
  apply FastRouting.sound _ _ [6,65,136,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9078 c9078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6311
  · exact u6312
  · exact u6313
  · exact u6314
  · exact u6315
  · exact u6316
  · exact u6317
  · exact u6318
  · exact u6319
  · exact u6320

def r9079 : Route 9 := (fun mask => (mask,id))

def c9079 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9079 : Upper (D 5) (R 5) [6,65,136,18] 13 := by
  apply FastRouting.sound _ _ [6,65,136,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9079 c9079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6321
  · exact u6322
  · exact u6323
  · exact u6324
  · exact u6325
  · exact u6326
  · exact u6327
  · exact u6328
  · exact u6329
  · exact u6330

def r9080 : Route 9 := (fun mask => (mask,id))

def c9080 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9080 : Upper (D 5) (R 5) [6,65,136,20] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9080 c9080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6331
  · exact u6332
  · exact u6333
  · exact u6334
  · exact u6335
  · exact u6336
  · exact u6337
  · exact u6338
  · exact u6339
  · exact u6340

def r9081 : Route 9 := (fun mask => (mask,id))

def c9081 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9081 : Upper (D 5) (R 5) [6,65,136,33] 13 := by
  apply FastRouting.sound _ _ [6,65,136,33] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9081 c9081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6341
  · exact u6342
  · exact u6343
  · exact u6344
  · exact u6345
  · exact u6346
  · exact u6347
  · exact u6348
  · exact u6349
  · exact u6350

def r9082 : Route 9 := (fun mask => (mask,id))

def c9082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9082 : Upper (D 5) (R 5) [6,65,136,34] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9082 c9082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6351
  · exact u6352
  · exact u6353
  · exact u6354
  · exact u6355
  · exact u6356
  · exact u6357
  · exact u6358
  · exact u6359
  · exact u6360

def r9083 : Route 9 := (fun mask => (mask,id))

def c9083 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9083 : Upper (D 5) (R 5) [6,65,136,36] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9083 c9083
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6361
  · exact u6362
  · exact u6363
  · exact u6364
  · exact u6365
  · exact u6366
  · exact u6367
  · exact u6368
  · exact u6369
  · exact u6370

def r9084 : Route 9 := (fun mask => (mask,id))

def c9084 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9084 : Upper (D 5) (R 5) [6,65,136,48] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9084 c9084
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6371
  · exact u6372
  · exact u6373
  · exact u6374
  · exact u6375
  · exact u6376
  · exact u6377
  · exact u6378
  · exact u6379
  · exact u6380
  · exact u6381
  · exact u6382
  · exact u6383
  · exact u6384
  · exact u6385

def r9085 : Route 9 := (fun mask => (mask,id))

def c9085 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9085 : Upper (D 5) (R 5) [6,65,136,257] 13 := by
  apply FastRouting.sound _ _ [6,65,136,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9085 c9085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6386
  · exact u6387
  · exact u6388
  · exact u6389
  · exact u6390
  · exact u6391

def r9086 : Route 9 := (fun mask => (mask,id))

def c9086 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9086 : Upper (D 5) (R 5) [6,65,136,258] 13 := by
  apply FastRouting.sound _ _ [6,65,136,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9086 c9086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6392
  · exact u6393
  · exact u6394
  · exact u6395
  · exact u6396
  · exact u6397

def r9087 : Route 9 := (fun mask => (mask,id))

def c9087 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9087 : Upper (D 5) (R 5) [6,65,136,260] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9087 c9087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6398
  · exact u6399
  · exact u6400
  · exact u6401
  · exact u6402
  · exact u6403

def r9088 : Route 9 := (fun mask => (mask,id))

def c9088 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9088 : Upper (D 5) (R 5) [6,65,136,272] 13 := by
  apply FastRouting.sound _ _ [6,65,136,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9088 c9088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6404
  · exact u6405
  · exact u6406
  · exact u6407
  · exact u6408
  · exact u6409
  · exact u6410
  · exact u6411
  · exact u6412
  · exact u6413

def r9089 : Route 9 := (fun mask => (mask,id))

def c9089 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9089 : Upper (D 5) (R 5) [6,65,136,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9089 c9089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6414
  · exact u6415
  · exact u6416
  · exact u6417
  · exact u6418
  · exact u6419
  · exact u6420
  · exact u6421
  · exact u6422
  · exact u6423

def b9090 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 67 148 14 313 297 361 425 297), lower := (rows 7 67 148 14 16 32 64 128 256), losses := [] }

theorem u9090 : Upper (D 5) (R 5) [6,65,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9090
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9091 : Route 9 := (fun mask => (mask,id))

def c9091 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9091 : Upper (D 5) (R 5) [6,65,144,33] 13 := by
  apply FastRouting.sound _ _ [6,65,144,33] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9091 c9091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6424
  · exact u6425
  · exact u6426
  · exact u6427
  · exact u6428
  · exact u6429
  · exact u6430
  · exact u6431
  · exact u6432
  · exact u6433

def r9092 : Route 9 := (fun mask => (mask,id))

def c9092 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9092 : Upper (D 5) (R 5) [6,65,144,34] 13 := by
  apply FastRouting.sound _ _ [6,65,144,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9092 c9092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6434
  · exact u6435
  · exact u6436
  · exact u6437
  · exact u6438
  · exact u6439
  · exact u6440
  · exact u6441
  · exact u6442
  · exact u6443

def r9093 : Route 9 := (fun mask => (mask,id))

def c9093 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9093 : Upper (D 5) (R 5) [6,65,144,36] 13 := by
  apply FastRouting.sound _ _ [6,65,144,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9093 c9093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6444
  · exact u6445
  · exact u6446
  · exact u6447
  · exact u6448
  · exact u6449
  · exact u6450
  · exact u6451
  · exact u6452
  · exact u6453

def r9094 : Route 9 := (fun mask => (mask,id))

def c9094 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9094 : Upper (D 5) (R 5) [6,65,144,257] 13 := by
  apply FastRouting.sound _ _ [6,65,144,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9094 c9094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6454
  · exact u6455
  · exact u6456
  · exact u6457
  · exact u6458
  · exact u6459

def r9095 : Route 9 := (fun mask => (mask,id))

def c9095 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9095 : Upper (D 5) (R 5) [6,65,144,258] 13 := by
  apply FastRouting.sound _ _ [6,65,144,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9095 c9095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6460
  · exact u6461
  · exact u6462
  · exact u6463
  · exact u6464
  · exact u6465

def r9096 : Route 9 := (fun mask => (mask,id))

def c9096 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9096 : Upper (D 5) (R 5) [6,65,144,260] 13 := by
  apply FastRouting.sound _ _ [6,65,144,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9096 c9096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6466
  · exact u6467
  · exact u6468
  · exact u6469
  · exact u6470
  · exact u6471

def r9097 : Route 9 := (fun mask => (mask,id))

def c9097 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9097 : Upper (D 5) (R 5) [6,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,65,144,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9097 c9097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6472
  · exact u6473
  · exact u6474
  · exact u6475
  · exact u6476
  · exact u6477
  · exact u6478
  · exact u6479
  · exact u6480
  · exact u6481

def b9098 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 67 164 14 313 313 377 441 313), lower := (rows 7 67 164 14 16 32 64 128 256), losses := [] }

theorem u9098 : Upper (D 5) (R 5) [6,65,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9098
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9099 : Route 9 := (fun mask => (mask,id))

def c9099 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9099 : Upper (D 5) (R 5) [6,65,160,17] 13 := by
  apply FastRouting.sound _ _ [6,65,160,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9099 c9099
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6482
  · exact u6483
  · exact u6484
  · exact u6485
  · exact u6486
  · exact u6487
  · exact u6488
  · exact u6489
  · exact u6490
  · exact u6491

def r9100 : Route 9 := (fun mask => (mask,id))

def c9100 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9100 : Upper (D 5) (R 5) [6,65,160,18] 13 := by
  apply FastRouting.sound _ _ [6,65,160,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9100 c9100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6492
  · exact u6493
  · exact u6494
  · exact u6495
  · exact u6496
  · exact u6497
  · exact u6498
  · exact u6499
  · exact u6500
  · exact u6501

def r9101 : Route 9 := (fun mask => (mask,id))

def c9101 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9101 : Upper (D 5) (R 5) [6,65,160,20] 13 := by
  apply FastRouting.sound _ _ [6,65,160,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9101 c9101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6502
  · exact u6503
  · exact u6504
  · exact u6505
  · exact u6506
  · exact u6507
  · exact u6508
  · exact u6509
  · exact u6510
  · exact u6511

def r9102 : Route 9 := (fun mask => (mask,id))

def c9102 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9102 : Upper (D 5) (R 5) [6,65,160,33] 13 := by
  apply FastRouting.sound _ _ [6,65,160,33] 13 (by decide) (choices 2) [6,10,12,258,260,264] r9102 c9102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6512
  · exact u6513
  · exact u6514
  · exact u6515
  · exact u6516
  · exact u6517

def r9103 : Route 9 := (fun mask => (mask,id))

def c9103 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9103 : Upper (D 5) (R 5) [6,65,160,34] 13 := by
  apply FastRouting.sound _ _ [6,65,160,34] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9103 c9103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6518
  · exact u6519
  · exact u6520
  · exact u6521
  · exact u6522
  · exact u6523

def b9104 : PairBound 9 := { available := 283, camps := [{ cop := 3, region := 339, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 44 283 315 347 411 283), lower := (rows 7 67 164 44 16 32 64 128 256), losses := [] }

theorem u9104 : Upper (D 5) (R 5) [6,65,160,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9104
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9105 : Route 9 := (fun mask => (mask,id))

def c9105 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9105 : Upper (D 5) (R 5) [6,65,160,48] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9105 c9105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6524
  · exact u6525
  · exact u6526
  · exact u6527
  · exact u6528
  · exact u6529
  · exact u6530
  · exact u6531
  · exact u6532
  · exact u6533

def r9106 : Route 9 := (fun mask => (mask,id))

def c9106 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9106 : Upper (D 5) (R 5) [6,65,160,257] 13 := by
  apply FastRouting.sound _ _ [6,65,160,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9106 c9106
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6534
  · exact u6535
  · exact u6536
  · exact u6537
  · exact u6538
  · exact u6539

def r9107 : Route 9 := (fun mask => (mask,id))

def c9107 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9107 : Upper (D 5) (R 5) [6,65,160,258] 13 := by
  apply FastRouting.sound _ _ [6,65,160,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9107 c9107
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6540
  · exact u6541
  · exact u6542
  · exact u6543
  · exact u6544
  · exact u6545

def r9108 : Route 9 := (fun mask => (mask,id))

def c9108 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9108 : Upper (D 5) (R 5) [6,65,160,260] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9108 c9108
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6546
  · exact u6547
  · exact u6548
  · exact u6549
  · exact u6550
  · exact u6551

def r9109 : Route 9 := (fun mask => (mask,id))

def c9109 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9109 : Upper (D 5) (R 5) [6,65,160,272] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9109 c9109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6552
  · exact u6553
  · exact u6554
  · exact u6555
  · exact u6556
  · exact u6557
  · exact u6558
  · exact u6559
  · exact u6560
  · exact u6561

def r9110 : Route 9 := (fun mask => (mask,id))

def c9110 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9110 : Upper (D 5) (R 5) [6,65,160,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9110 c9110
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6562
  · exact u6563
  · exact u6564
  · exact u6565
  · exact u6566
  · exact u6567

def b9111 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 67 388 14 57 57 121 185 313), lower := (rows 7 67 388 14 16 32 64 128 256), losses := [] }

theorem u9111 : Upper (D 5) (R 5) [6,65,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9111
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9112 : Route 9 := (fun mask => (mask,id))

def c9112 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9112 : Upper (D 5) (R 5) [6,65,384,17] 13 := by
  apply FastRouting.sound _ _ [6,65,384,17] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9112 c9112
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6568
  · exact u6569
  · exact u6570
  · exact u6571
  · exact u6572
  · exact u6573

def r9113 : Route 9 := (fun mask => (mask,id))

def c9113 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9113 : Upper (D 5) (R 5) [6,65,384,18] 13 := by
  apply FastRouting.sound _ _ [6,65,384,18] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9113 c9113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6574
  · exact u6575
  · exact u6576
  · exact u6577
  · exact u6578
  · exact u6579

def r9114 : Route 9 := (fun mask => (mask,id))

def c9114 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9114 : Upper (D 5) (R 5) [6,65,384,20] 13 := by
  apply FastRouting.sound _ _ [6,65,384,20] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9114 c9114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6580
  · exact u6581
  · exact u6582
  · exact u6583
  · exact u6584
  · exact u6585

def r9115 : Route 9 := (fun mask => (mask,id))

def c9115 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9115 : Upper (D 5) (R 5) [6,65,384,33] 13 := by
  apply FastRouting.sound _ _ [6,65,384,33] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9115 c9115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6586
  · exact u6587
  · exact u6588
  · exact u6589
  · exact u6590
  · exact u6591

def r9116 : Route 9 := (fun mask => (mask,id))

def c9116 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9116 : Upper (D 5) (R 5) [6,65,384,34] 13 := by
  apply FastRouting.sound _ _ [6,65,384,34] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9116 c9116
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6592
  · exact u6593
  · exact u6594
  · exact u6595
  · exact u6596
  · exact u6597

def r9117 : Route 9 := (fun mask => (mask,id))

def c9117 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9117 : Upper (D 5) (R 5) [6,65,384,36] 13 := by
  apply FastRouting.sound _ _ [6,65,384,36] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9117 c9117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6598
  · exact u6599
  · exact u6600
  · exact u6601
  · exact u6602
  · exact u6603

def r9118 : Route 9 := (fun mask => (mask,id))

def c9118 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9118 : Upper (D 5) (R 5) [6,65,384,48] 13 := by
  apply FastRouting.sound _ _ [6,65,384,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9118 c9118
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6604
  · exact u6605
  · exact u6606
  · exact u6607
  · exact u6608
  · exact u6609
  · exact u6610
  · exact u6611
  · exact u6612
  · exact u6613

def b9119 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 70 134 25 313 297 361 425 297), lower := (rows 7 70 134 25 16 32 64 128 256), losses := [] }

theorem u9119 : Upper (D 5) (R 5) [6,68,130,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9119
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u9119
end Delivery.IrregularNine14.P05
