import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0055
import IrregularNine14P01C0056

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6960 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 14 41 466 482 450 450 450), lower := (rows 53 82 14 41 16 32 64 128 256), losses := [] }

theorem u6960 : Upper (D 1) (R 1) [52,80,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6960
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6961 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 14 42 465 481 449 449 449), lower := (rows 53 82 14 42 16 32 64 128 256), losses := [] }

theorem u6961 : Upper (D 1) (R 1) [52,80,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6961
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6962 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 14 73 434 418 482 418 418), lower := (rows 53 82 14 73 16 32 64 128 256), losses := [] }

theorem u6962 : Upper (D 1) (R 1) [52,80,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6962
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6963 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 14 74 433 417 481 417 417), lower := (rows 53 82 14 74 16 32 64 128 256), losses := [] }

theorem u6963 : Upper (D 1) (R 1) [52,80,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6963
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6964 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 14 104 403 419 451 387 387), lower := (rows 53 82 14 104 16 32 64 128 256), losses := [] }

theorem u6964 : Upper (D 1) (R 1) [52,80,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6964
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6965 : PairBound 9 := { available := 482, camps := [], pairs := [(3,4)], upper := (rows 53 82 14 137 498 482 482 482 482), lower := (rows 53 82 14 137 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 9 0 38 70 134 262), good := (rows 493 482 494 137 0 32 64 128 256) }] }

theorem u6965 : Upper (D 1) (R 1) [52,80,10,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6965
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6966 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 14 138 497 481 481 481 481), lower := (rows 53 82 14 138 16 32 64 128 256), losses := [] }

theorem u6966 : Upper (D 1) (R 1) [52,80,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6966
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6967 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 14 168 467 483 451 451 451), lower := (rows 53 82 14 168 16 32 64 128 256), losses := [] }

theorem u6967 : Upper (D 1) (R 1) [52,80,10,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6967
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6968 : PairBound 9 := { available := 419, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 14 200 435 419 483 419 419), lower := (rows 53 82 14 200 16 32 64 128 256), losses := [] }

theorem u6968 : Upper (D 1) (R 1) [52,80,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6968
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6969 : PairBound 9 := { available := 226, camps := [], pairs := [(3,4)], upper := (rows 53 82 14 265 242 226 226 226 482), lower := (rows 53 82 14 265 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 9 0 38 70 134 262), good := (rows 493 482 494 265 0 32 64 128 256) }] }

theorem u6969 : Upper (D 1) (R 1) [52,80,10,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6969
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6970 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 14 266 241 225 225 225 481), lower := (rows 53 82 14 266 16 32 64 128 256), losses := [] }

theorem u6970 : Upper (D 1) (R 1) [52,80,10,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6970
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6971 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 14 296 211 227 195 195 451), lower := (rows 53 82 14 296 16 32 64 128 256), losses := [] }

theorem u6971 : Upper (D 1) (R 1) [52,80,10,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6971
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6972 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 14 328 179 163 227 163 419), lower := (rows 53 82 14 328 16 32 64 128 256), losses := [] }

theorem u6972 : Upper (D 1) (R 1) [52,80,10,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6972
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6973 : Route 9 := (fun mask => (mask,id))

def c6973 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6973 : Upper (D 1) (R 1) [52,80,10,384] 13 := by
  apply FastRouting.sound _ _ [52,80,10,384] 13 (by decide) (choices 1) [1,2,32,64,128] r6973 c6973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3313
  · exact u3314
  · exact u3315
  · exact u3316
  · exact u3317

def b6974 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 76 11 434 418 482 418 418), lower := (rows 53 82 76 11 16 32 64 128 256), losses := [] }

theorem u6974 : Upper (D 1) (R 1) [52,80,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6974
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6975 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 76 41 402 418 450 386 386), lower := (rows 53 82 76 41 16 32 64 128 256), losses := [] }

theorem u6975 : Upper (D 1) (R 1) [52,80,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6975
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6976 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 42 403 419 451 387 387), lower := (rows 53 82 76 42 16 32 64 128 256), losses := [] }

theorem u6976 : Upper (D 1) (R 1) [52,80,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6976
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6977 : Route 9 := (fun mask => (mask,id))

def c6977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6977 : Upper (D 1) (R 1) [52,80,72,129] 13 := by
  apply FastRouting.sound _ _ [52,80,72,129] 13 (by decide) (choices 1) [2,32,128,256] r6977 c6977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3318
  · exact u3319
  · exact u3320
  · exact u3321

def r6978 : Route 9 := (fun mask => (mask,id))

def c6978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6978 : Upper (D 1) (R 1) [52,80,72,130] 13 := by
  apply FastRouting.sound _ _ [52,80,72,130] 13 (by decide) (choices 1) [1,2,32,128,256] r6978 c6978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3322
  · exact u3323
  · exact u3324
  · exact u3325
  · exact u3326

def b6979 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 168 403 419 451 387 387), lower := (rows 53 82 76 168 16 32 64 128 256), losses := [] }

theorem u6979 : Upper (D 1) (R 1) [52,80,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6979
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6980 : Route 9 := (fun mask => (mask,id))

def c6980 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6980 : Upper (D 1) (R 1) [52,80,72,257] 13 := by
  apply FastRouting.sound _ _ [52,80,72,257] 13 (by decide) (choices 1) [2,32,128] r6980 c6980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3327
  · exact u3328
  · exact u3329

def r6981 : Route 9 := (fun mask => (mask,id))

def c6981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6981 : Upper (D 1) (R 1) [52,80,72,258] 13 := by
  apply FastRouting.sound _ _ [52,80,72,258] 13 (by decide) (choices 1) [1,2,32,128] r6981 c6981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3330
  · exact u3331
  · exact u3332
  · exact u3333

def b6982 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 296 147 163 195 131 387), lower := (rows 53 82 76 296 16 32 64 128 256), losses := [] }

theorem u6982 : Upper (D 1) (R 1) [52,80,72,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6983 : Route 9 := (fun mask => (mask,id))

def c6983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6983 : Upper (D 1) (R 1) [52,80,72,384] 13 := by
  apply FastRouting.sound _ _ [52,80,72,384] 13 (by decide) (choices 1) [1,2,32,128] r6983 c6983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3334
  · exact u3335
  · exact u3336
  · exact u3337

def b6984 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 134 11 504 488 488 488 488), lower := (rows 53 82 134 11 16 32 64 128 256), losses := [] }

theorem u6984 : Upper (D 1) (R 1) [52,80,130,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6985 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 41 474 490 458 458 458), lower := (rows 53 82 134 41 16 32 64 128 256), losses := [] }

theorem u6985 : Upper (D 1) (R 1) [52,80,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6985
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6986 : Route 9 := (fun mask => (mask,id))

def c6986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u6986 : Upper (D 1) (R 1) [52,80,130,34] 13 := by
  apply FastRouting.sound _ _ [52,80,130,34] 13 (by decide) (choices 1) [1,8,64,128,256] r6986 c6986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3338
  · exact u3339
  · exact u3340
  · exact u3341
  · exact u3342

def r6987 : Route 9 := (fun mask => (mask,id))

def c6987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | _ => 0)

theorem u6987 : Upper (D 1) (R 1) [52,80,130,65] 13 := by
  apply FastRouting.sound _ _ [52,80,130,65] 13 (by decide) (choices 1) [2,8,32,128,256] r6987 c6987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3343
  · exact u3344
  · exact u3345
  · exact u3346
  · exact u3347

def b6988 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 134 74 441 425 489 425 425), lower := (rows 53 82 134 74 16 32 64 128 256), losses := [] }

theorem u6988 : Upper (D 1) (R 1) [52,80,130,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6988
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6989 : Route 9 := (fun mask => (mask,id))

def c6989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u6989 : Upper (D 1) (R 1) [52,80,130,96] 13 := by
  apply FastRouting.sound _ _ [52,80,130,96] 13 (by decide) (choices 1) [1,2,8,128,256] r6989 c6989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3348
  · exact u3349
  · exact u3350
  · exact u3351
  · exact u3352

def b6990 : PairBound 9 := { available := 362, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 134 137 378 362 362 490 362), lower := (rows 53 82 134 137 16 32 64 128 256), losses := [] }

theorem u6990 : Upper (D 1) (R 1) [52,80,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6990
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6991 : PairBound 9 := { available := 361, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 134 138 377 361 361 489 361), lower := (rows 53 82 134 138 16 32 64 128 256), losses := [] }

theorem u6991 : Upper (D 1) (R 1) [52,80,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6991
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6992 : Route 9 := (fun mask => (mask,id))

def c6992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6992 : Upper (D 1) (R 1) [52,80,130,160] 13 := by
  apply FastRouting.sound _ _ [52,80,130,160] 13 (by decide) (choices 1) [1,2,8,64,256] r6992 c6992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3353
  · exact u3354
  · exact u3355
  · exact u3356
  · exact u3357

def r6993 : Route 9 := (fun mask => (mask,id))

def c6993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6993 : Upper (D 1) (R 1) [52,80,130,192] 13 := by
  apply FastRouting.sound _ _ [52,80,130,192] 13 (by decide) (choices 1) [1,2,8,32,256] r6993 c6993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3358
  · exact u3359
  · exact u3360
  · exact u3361
  · exact u3362

def r6994 : Route 9 := (fun mask => (mask,id))

def c6994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6994 : Upper (D 1) (R 1) [52,80,130,257] 13 := by
  apply FastRouting.sound _ _ [52,80,130,257] 13 (by decide) (choices 1) [2,8,32,64,128] r6994 c6994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3363
  · exact u3364
  · exact u3365
  · exact u3366
  · exact u3367

def r6995 : Route 9 := (fun mask => (mask,id))

def c6995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u6995 : Upper (D 1) (R 1) [52,80,130,258] 13 := by
  apply FastRouting.sound _ _ [52,80,130,258] 13 (by decide) (choices 1) [1,8,32,64,128] r6995 c6995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3368
  · exact u3369
  · exact u3370
  · exact u3371
  · exact u3372

def r6996 : Route 9 := (fun mask => (mask,id))

def c6996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6996 : Upper (D 1) (R 1) [52,80,130,288] 13 := by
  apply FastRouting.sound _ _ [52,80,130,288] 13 (by decide) (choices 1) [1,2,8,64,128] r6996 c6996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3373
  · exact u3374
  · exact u3375
  · exact u3376
  · exact u3377

def r6997 : Route 9 := (fun mask => (mask,id))

def c6997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6997 : Upper (D 1) (R 1) [52,80,130,320] 13 := by
  apply FastRouting.sound _ _ [52,80,130,320] 13 (by decide) (choices 1) [1,2,8,32,128] r6997 c6997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3378
  · exact u3379
  · exact u3380
  · exact u3381
  · exact u3382

def r6998 : Route 9 := (fun mask => (mask,id))

def c6998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6998 : Upper (D 1) (R 1) [52,80,130,384] 13 := by
  apply FastRouting.sound _ _ [52,80,130,384] 13 (by decide) (choices 1) [1,2,8,32,64] r6998 c6998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3383
  · exact u3384
  · exact u3385
  · exact u3386
  · exact u3387

def b6999 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 140 11 498 482 482 482 482), lower := (rows 53 82 140 11 16 32 64 128 256), losses := [] }

theorem u6999 : Upper (D 1) (R 1) [52,80,136,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6999
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7000 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 140 41 466 482 450 450 450), lower := (rows 53 82 140 41 16 32 64 128 256), losses := [] }

theorem u7000 : Upper (D 1) (R 1) [52,80,136,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7000
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7001 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 42 467 483 451 451 451), lower := (rows 53 82 140 42 16 32 64 128 256), losses := [] }

theorem u7001 : Upper (D 1) (R 1) [52,80,136,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7001
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7002 : Route 9 := (fun mask => (mask,id))

def c7002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7002 : Upper (D 1) (R 1) [52,80,136,65] 13 := by
  apply FastRouting.sound _ _ [52,80,136,65] 13 (by decide) (choices 1) [2,32,128,256] r7002 c7002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3388
  · exact u3389
  · exact u3390
  · exact u3391

def b7003 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 140 74 435 419 483 419 419), lower := (rows 53 82 140 74 16 32 64 128 256), losses := [] }

theorem u7003 : Upper (D 1) (R 1) [52,80,136,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7003
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7004 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 104 403 419 451 387 387), lower := (rows 53 82 140 104 16 32 64 128 256), losses := [] }

theorem u7004 : Upper (D 1) (R 1) [52,80,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7004
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7005 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 82 140 137 370 354 354 482 354), lower := (rows 53 82 140 137 16 32 64 128 256), losses := [] }

theorem u7005 : Upper (D 1) (R 1) [52,80,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7005
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7006 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 82 140 138 371 355 355 483 355), lower := (rows 53 82 140 138 16 32 64 128 256), losses := [] }

theorem u7006 : Upper (D 1) (R 1) [52,80,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7006
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7007 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 82 140 168 339 355 323 451 323), lower := (rows 53 82 140 168 16 32 64 128 256), losses := [] }

theorem u7007 : Upper (D 1) (R 1) [52,80,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7007
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7008 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 82 140 200 307 291 355 419 291), lower := (rows 53 82 140 200 16 32 64 128 256), losses := [] }

theorem u7008 : Upper (D 1) (R 1) [52,80,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7008
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7009 : Route 9 := (fun mask => (mask,id))

def c7009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7009 : Upper (D 1) (R 1) [52,80,136,257] 13 := by
  apply FastRouting.sound _ _ [52,80,136,257] 13 (by decide) (choices 1) [2,32,64,128] r7009 c7009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3392
  · exact u3393
  · exact u3394
  · exact u3395

def r7010 : Route 9 := (fun mask => (mask,id))

def c7010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7010 : Upper (D 1) (R 1) [52,80,136,258] 13 := by
  apply FastRouting.sound _ _ [52,80,136,258] 13 (by decide) (choices 1) [1,2,32,64,128] r7010 c7010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3396
  · exact u3397
  · exact u3398
  · exact u3399
  · exact u3400

def b7011 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 296 211 227 195 195 451), lower := (rows 53 82 140 296 16 32 64 128 256), losses := [] }

theorem u7011 : Upper (D 1) (R 1) [52,80,136,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7011
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7012 : Route 9 := (fun mask => (mask,id))

def c7012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7012 : Upper (D 1) (R 1) [52,80,136,320] 13 := by
  apply FastRouting.sound _ _ [52,80,136,320] 13 (by decide) (choices 1) [1,2,32,128] r7012 c7012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3401
  · exact u3402
  · exact u3403
  · exact u3404

def b7013 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 82 140 392 115 99 99 227 355), lower := (rows 53 82 140 392 16 32 64 128 256), losses := [] }

theorem u7013 : Upper (D 1) (R 1) [52,80,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7013
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7014 : PairBound 9 := { available := 426, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 196 11 442 426 490 426 426), lower := (rows 53 82 196 11 16 32 64 128 256), losses := [] }

theorem u7014 : Upper (D 1) (R 1) [52,80,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7014
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7015 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 196 41 410 426 458 394 394), lower := (rows 53 82 196 41 16 32 64 128 256), losses := [] }

theorem u7015 : Upper (D 1) (R 1) [52,80,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7015
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7016 : Route 9 := (fun mask => (mask,id))

def c7016 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u7016 : Upper (D 1) (R 1) [52,80,192,34] 13 := by
  apply FastRouting.sound _ _ [52,80,192,34] 13 (by decide) (choices 1) [1,2,8,128,256] r7016 c7016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3405
  · exact u3406
  · exact u3407
  · exact u3408
  · exact u3409

def b7017 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 196 137 314 298 362 426 298), lower := (rows 53 82 196 137 16 32 64 128 256), losses := [] }

theorem u7017 : Upper (D 1) (R 1) [52,80,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7017
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7018 : Route 9 := (fun mask => (mask,id))

def c7018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7018 : Upper (D 1) (R 1) [52,80,192,130] 13 := by
  apply FastRouting.sound _ _ [52,80,192,130] 13 (by decide) (choices 1) [1,2,8,32,256] r7018 c7018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3410
  · exact u3411
  · exact u3412
  · exact u3413
  · exact u3414

def r7019 : Route 9 := (fun mask => (mask,id))

def c7019 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7019 : Upper (D 1) (R 1) [52,80,192,160] 13 := by
  apply FastRouting.sound _ _ [52,80,192,160] 13 (by decide) (choices 1) [1,2,8,256] r7019 c7019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3415
  · exact u3416
  · exact u3417
  · exact u3418

#print axioms u7019
end Delivery.IrregularNine14.P01
