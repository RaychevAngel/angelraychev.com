import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0071
import IrregularNine14P05C0072
import IrregularNine14P05C0073

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7980 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 268 50 45 77 141 269), lower := (rows 19 194 44 268 50 32 64 128 256), losses := [] }

theorem u7980 : Upper (D 5) (R 5) [18,192,40,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7980
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7981 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 44 268 52 43 75 139 267), lower := (rows 19 194 44 268 52 32 64 128 256), losses := [] }

theorem u7981 : Upper (D 5) (R 5) [18,192,40,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7981
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7982 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 44 268 56 39 71 135 263), lower := (rows 19 194 44 268 56 32 64 128 256), losses := [] }

theorem u7982 : Upper (D 5) (R 5) [18,192,40,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7982
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7983 : Route 9 := (fun mask => (mask,id))

def c7983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7983 : Upper (D 5) (R 5) [34,65,40,129,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,6] 13 (by decide) (choices 1) [4,8,16,256] r7983 c7983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4310
  · exact u4311
  · exact u4312
  · exact u4313

def b7984 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 137 26 308 340 404 276), lower := (rows 35 67 44 137 26 32 64 128 256), losses := [] }

theorem u7984 : Upper (D 5) (R 5) [34,65,40,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7984
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7985 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 44 137 28 310 342 406 278), lower := (rows 35 67 44 137 28 32 64 128 256), losses := [] }

theorem u7985 : Upper (D 5) (R 5) [34,65,40,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7985
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7986 : Route 9 := (fun mask => (mask,id))

def c7986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7986 : Upper (D 5) (R 5) [34,65,40,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,258] 13 (by decide) (choices 1) [4,8,16] r7986 c7986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4314
  · exact u4315
  · exact u4316

def r7987 : Route 9 := (fun mask => (mask,id))

def c7987 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7987 : Upper (D 5) (R 5) [34,65,40,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,260] 13 (by decide) (choices 1) [2,4,8,16] r7987 c7987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4317
  · exact u4318
  · exact u4319
  · exact u4320

def r7988 : Route 9 := (fun mask => (mask,id))

def c7988 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7988 : Upper (D 5) (R 5) [34,65,40,129,264] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,264] 13 (by decide) (choices 1) [2,4,16] r7988 c7988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4321
  · exact u4322
  · exact u4323

def b7989 : PairBound 9 := { available := 284, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 44 138 21 316 348 412 284), lower := (rows 35 67 44 138 21 32 64 128 256), losses := [] }

theorem u7989 : Upper (D 5) (R 5) [34,65,40,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7990 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 138 25 308 340 404 276), lower := (rows 35 67 44 138 25 32 64 128 256), losses := [] }

theorem u7990 : Upper (D 5) (R 5) [34,65,40,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7990
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7991 : PairBound 9 := { available := 277, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 44 138 28 309 341 405 277), lower := (rows 35 67 44 138 28 32 64 128 256), losses := [] }

theorem u7991 : Upper (D 5) (R 5) [34,65,40,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7991
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7992 : Route 9 := (fun mask => (mask,id))

def c7992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7992 : Upper (D 5) (R 5) [34,65,40,130,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,257] 13 (by decide) (choices 1) [4,8,16] r7992 c7992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4324
  · exact u4325
  · exact u4326

def r7993 : Route 9 := (fun mask => (mask,id))

def c7993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7993 : Upper (D 5) (R 5) [34,65,40,130,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,260] 13 (by decide) (choices 1) [1,4,8,16] r7993 c7993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4327
  · exact u4328
  · exact u4329
  · exact u4330

def r7994 : Route 9 := (fun mask => (mask,id))

def c7994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7994 : Upper (D 5) (R 5) [34,65,40,130,264] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,264] 13 (by decide) (choices 1) [1,4,16] r7994 c7994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4331
  · exact u4332
  · exact u4333

def b7995 : PairBound 9 := { available := 284, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 140 19 316 348 412 284), lower := (rows 35 67 44 140 19 32 64 128 256), losses := [] }

theorem u7995 : Upper (D 5) (R 5) [34,65,40,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7995
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7996 : PairBound 9 := { available := 282, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 44 140 21 314 346 410 282), lower := (rows 35 67 44 140 21 32 64 128 256), losses := [] }

theorem u7996 : Upper (D 5) (R 5) [34,65,40,132,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7996
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7997 : Route 9 := (fun mask => (mask,id))

def c7997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7997 : Upper (D 5) (R 5) [34,65,40,132,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,6] 13 (by decide) (choices 1) [1,8,16,256] r7997 c7997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4334
  · exact u4335
  · exact u4336
  · exact u4337

theorem m7998_4 : Upper (D 5) (R 5) [34,65,40,132,10,4] 13 :=
  permutation_upper _ _ _ [34,65,40,132,10,1] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4338

def r7998 : Route 9 := (fun mask => (mask,id))

def c7998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7998 : Upper (D 5) (R 5) [34,65,40,132,10] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,10] 13 (by decide) (choices 1) [1,4,16,256] r7998 c7998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4338
  · exact m7998_4
  · exact u4339
  · exact u4340

def r7999 : Route 9 := (fun mask => (mask,id))

def c7999 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7999 : Upper (D 5) (R 5) [34,65,40,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,257] 13 (by decide) (choices 1) [2,4,8,16] r7999 c7999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4341
  · exact u4342
  · exact u4343
  · exact u4344

def r8000 : Route 9 := (fun mask => (mask,id))

def c8000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8000 : Upper (D 5) (R 5) [34,65,40,132,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,258] 13 (by decide) (choices 1) [1,4,8,16] r8000 c8000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4345
  · exact u4346
  · exact u4347
  · exact u4348

def b8001 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 152 19 300 332 396 268), lower := (rows 35 67 44 152 19 32 64 128 256), losses := [] }

theorem u8001 : Upper (D 5) (R 5) [34,65,40,144,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8001
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8002 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 44 152 21 302 334 398 270), lower := (rows 35 67 44 152 21 32 64 128 256), losses := [] }

theorem u8002 : Upper (D 5) (R 5) [34,65,40,144,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8002
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8003 : Route 9 := (fun mask => (mask,id))

def c8003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8003 : Upper (D 5) (R 5) [34,65,40,144,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,6] 13 (by decide) (choices 1) [1,4,8,256] r8003 c8003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4349
  · exact u4350
  · exact u4351
  · exact u4352

def b8004 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 152 25 294 326 390 262), lower := (rows 35 67 44 152 25 32 64 128 256), losses := [] }

theorem u8004 : Upper (D 5) (R 5) [34,65,40,144,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8004
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8005 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 152 26 293 325 389 261), lower := (rows 35 67 44 152 26 32 64 128 256), losses := [] }

theorem u8005 : Upper (D 5) (R 5) [34,65,40,144,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8005
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8006 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 44 152 28 295 327 391 263), lower := (rows 35 67 44 152 28 32 64 128 256), losses := [] }

theorem u8006 : Upper (D 5) (R 5) [34,65,40,144,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8006
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8007 : Route 9 := (fun mask => (mask,id))

def c8007 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8007 : Upper (D 5) (R 5) [34,65,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,257] 13 (by decide) (choices 1) [2,4,8] r8007 c8007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4353
  · exact u4354
  · exact u4355

def r8008 : Route 9 := (fun mask => (mask,id))

def c8008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8008 : Upper (D 5) (R 5) [34,65,40,144,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,258] 13 (by decide) (choices 1) [1,4,8] r8008 c8008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4356
  · exact u4357
  · exact u4358

def r8009 : Route 9 := (fun mask => (mask,id))

def c8009 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8009 : Upper (D 5) (R 5) [34,65,40,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,260] 13 (by decide) (choices 1) [1,2,4,8] r8009 c8009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4359
  · exact u4360
  · exact u4361
  · exact u4362

def b8010 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 152 280 39 71 135 263), lower := (rows 35 67 44 152 280 32 64 128 256), losses := [] }

theorem u8010 : Upper (D 5) (R 5) [34,65,40,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8010
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8011 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 392 19 60 92 156 284), lower := (rows 35 67 44 392 19 32 64 128 256), losses := [] }

theorem u8011 : Upper (D 5) (R 5) [34,65,40,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8012 : PairBound 9 := { available := 30, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 44 392 21 62 94 158 286), lower := (rows 35 67 44 392 21 32 64 128 256), losses := [] }

theorem u8012 : Upper (D 5) (R 5) [34,65,40,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8012
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8013 : Route 9 := (fun mask => (mask,id))

def c8013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8013 : Upper (D 5) (R 5) [34,65,40,384,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,6] 13 (by decide) (choices 1) [1,4,8,16] r8013 c8013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4363
  · exact u4364
  · exact u4365
  · exact u4366

def r8014 : Route 9 := (fun mask => (mask,id))

def c8014 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8014 : Upper (D 5) (R 5) [34,65,40,384,9] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,9] 13 (by decide) (choices 1) [2,4,16] r8014 c8014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4367
  · exact u4368
  · exact u4369

def r8015 : Route 9 := (fun mask => (mask,id))

def c8015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8015 : Upper (D 5) (R 5) [34,65,40,384,10] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,10] 13 (by decide) (choices 1) [1,4,16] r8015 c8015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4370
  · exact u4371
  · exact u4372

def b8016 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 44 392 28 55 87 151 279), lower := (rows 35 67 44 392 28 32 64 128 256), losses := [] }

theorem u8016 : Upper (D 5) (R 5) [34,65,40,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8016
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8017 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 52 137 22 300 332 396 268), lower := (rows 35 67 52 137 22 32 64 128 256), losses := [] }

theorem u8017 : Upper (D 5) (R 5) [34,65,48,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8017
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8018 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 137 26 300 332 396 268), lower := (rows 35 67 52 137 26 32 64 128 256), losses := [] }

theorem u8018 : Upper (D 5) (R 5) [34,65,48,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8018
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8019 : Route 9 := (fun mask => (mask,id))

def c8019 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8019 : Upper (D 5) (R 5) [34,65,48,129,12] 13 := by
  apply FastRouting.sound _ _ [34,65,48,129,12] 13 (by decide) (choices 1) [2,4,8,256] r8019 c8019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4373
  · exact u4374
  · exact u4375
  · exact u4376

def r8020 : Route 9 := (fun mask => (mask,id))

def c8020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8020 : Upper (D 5) (R 5) [34,65,48,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,48,129,258] 13 (by decide) (choices 1) [4,8] r8020 c8020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4377
  · exact u4378

def r8021 : Route 9 := (fun mask => (mask,id))

def c8021 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8021 : Upper (D 5) (R 5) [34,65,48,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,48,129,260] 13 (by decide) (choices 1) [2,4,8] r8021 c8021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4379
  · exact u4380
  · exact u4381

def r8022 : Route 9 := (fun mask => (mask,id))

def c8022 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8022 : Upper (D 5) (R 5) [34,65,48,129,264] 13 := by
  apply FastRouting.sound _ _ [34,65,48,129,264] 13 (by decide) (choices 1) [2,4,8] r8022 c8022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4382
  · exact u4383
  · exact u4384

def b8023 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 67 52 138 21 300 332 396 268), lower := (rows 35 67 52 138 21 32 64 128 256), losses := [] }

theorem u8023 : Upper (D 5) (R 5) [34,65,48,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8023
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8024 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 138 25 300 332 396 268), lower := (rows 35 67 52 138 25 32 64 128 256), losses := [] }

theorem u8024 : Upper (D 5) (R 5) [34,65,48,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8024
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8025 : Route 9 := (fun mask => (mask,id))

def c8025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8025 : Upper (D 5) (R 5) [34,65,48,130,12] 13 := by
  apply FastRouting.sound _ _ [34,65,48,130,12] 13 (by decide) (choices 1) [1,4,8,256] r8025 c8025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4385
  · exact u4386
  · exact u4387
  · exact u4388

def r8026 : Route 9 := (fun mask => (mask,id))

def c8026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8026 : Upper (D 5) (R 5) [34,65,48,130,257] 13 := by
  apply FastRouting.sound _ _ [34,65,48,130,257] 13 (by decide) (choices 1) [4,8] r8026 c8026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4389
  · exact u4390

def r8027 : Route 9 := (fun mask => (mask,id))

def c8027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8027 : Upper (D 5) (R 5) [34,65,48,130,260] 13 := by
  apply FastRouting.sound _ _ [34,65,48,130,260] 13 (by decide) (choices 1) [1,4,8] r8027 c8027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4391
  · exact u4392
  · exact u4393

def r8028 : Route 9 := (fun mask => (mask,id))

def c8028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8028 : Upper (D 5) (R 5) [34,65,48,130,264] 13 := by
  apply FastRouting.sound _ _ [34,65,48,130,264] 13 (by decide) (choices 1) [1,4,8] r8028 c8028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4394
  · exact u4395
  · exact u4396

def b8029 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 140 19 300 332 396 268), lower := (rows 35 67 52 140 19 32 64 128 256), losses := [] }

theorem u8029 : Upper (D 5) (R 5) [34,65,48,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8029
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8030 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 67 52 140 21 298 330 394 266), lower := (rows 35 67 52 140 21 32 64 128 256), losses := [] }

theorem u8030 : Upper (D 5) (R 5) [34,65,48,132,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8030
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8031 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 52 140 22 297 329 393 265), lower := (rows 35 67 52 140 22 32 64 128 256), losses := [] }

theorem u8031 : Upper (D 5) (R 5) [34,65,48,132,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8031
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8032 : Route 9 := (fun mask => (mask,id))

def c8032 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8032 : Upper (D 5) (R 5) [34,65,48,132,9] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,9] 13 (by decide) (choices 1) [2,4,8,256] r8032 c8032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4397
  · exact u4398
  · exact u4399
  · exact u4400

def r8033 : Route 9 := (fun mask => (mask,id))

def c8033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8033 : Upper (D 5) (R 5) [34,65,48,132,10] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,10] 13 (by decide) (choices 1) [1,4,8,256] r8033 c8033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4401
  · exact u4402
  · exact u4403
  · exact u4404

def b8034 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 52 140 28 299 331 395 267), lower := (rows 35 67 52 140 28 32 64 128 256), losses := [] }

theorem u8034 : Upper (D 5) (R 5) [34,65,48,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8034
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8035 : Route 9 := (fun mask => (mask,id))

def c8035 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8035 : Upper (D 5) (R 5) [34,65,48,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,257] 13 (by decide) (choices 1) [2,4,8] r8035 c8035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4405
  · exact u4406
  · exact u4407

def r8036 : Route 9 := (fun mask => (mask,id))

def c8036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8036 : Upper (D 5) (R 5) [34,65,48,132,258] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,258] 13 (by decide) (choices 1) [1,4,8] r8036 c8036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4408
  · exact u4409
  · exact u4410

def b8037 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 52 140 276 43 75 139 267), lower := (rows 35 67 52 140 276 32 64 128 256), losses := [] }

theorem u8037 : Upper (D 5) (R 5) [34,65,48,132,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8037
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8038 : Route 9 := (fun mask => (mask,id))

def c8038 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8038 : Upper (D 5) (R 5) [34,65,48,132,264] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132,264] 13 (by decide) (choices 1) [1,2,4,8] r8038 c8038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4411
  · exact u4412
  · exact u4413
  · exact u4414

def b8039 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 392 19 44 76 140 268), lower := (rows 35 67 52 392 19 32 64 128 256), losses := [] }

theorem u8039 : Upper (D 5) (R 5) [34,65,48,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8039
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8039
end Delivery.IrregularNine14.P05
