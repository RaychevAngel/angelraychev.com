import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0065
import IrregularNine14P01C0066
import IrregularNine14P01C0067

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7380 : Route 9 := (fun mask => (mask,id))

def c7380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7380 : Upper (D 1) (R 1) [112,20,40,258] 13 := by
  apply FastRouting.sound _ _ [112,20,40,258] 13 (by decide) (choices 1) [1,2,64,128] r7380 c7380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3911
  · exact u3912
  · exact u3913
  · exact u3914

def r7381 : Route 9 := (fun mask => (mask,id))

def c7381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7381 : Upper (D 1) (R 1) [112,20,40,320] 13 := by
  apply FastRouting.sound _ _ [112,20,40,320] 13 (by decide) (choices 1) [1,2,128] r7381 c7381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3915
  · exact u3916
  · exact u3917

def r7382 : Route 9 := (fun mask => (mask,id))

def c7382 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7382 : Upper (D 1) (R 1) [112,20,40,384] 13 := by
  apply FastRouting.sound _ _ [112,20,40,384] 13 (by decide) (choices 1) [1,2,64,128] r7382 c7382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3918
  · exact u3919
  · exact u3920
  · exact u3921

def b7383 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 134 11 504 488 488 488 488), lower := (rows 113 22 134 11 16 32 64 128 256), losses := [] }

theorem u7383 : Upper (D 1) (R 1) [112,20,130,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7383
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7384 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 134 41 474 490 458 458 458), lower := (rows 113 22 134 41 16 32 64 128 256), losses := [] }

theorem u7384 : Upper (D 1) (R 1) [112,20,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7384
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7385 : PairBound 9 := { available := 457, camps := [{ cop := 3, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 134 42 473 489 457 457 457), lower := (rows 113 22 134 42 16 32 64 128 256), losses := [] }

theorem u7385 : Upper (D 1) (R 1) [112,20,130,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7385
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7386 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 134 104 411 427 459 395 395), lower := (rows 113 22 134 104 16 32 64 128 256), losses := [] }

theorem u7386 : Upper (D 1) (R 1) [112,20,130,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7386
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7387 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u7387 : Upper (D 1) (R 1) [112,20,130,129] 13 := by
  apply FastRouting.sound _ _ [112,20,130,129] 13 (by decide) (choices 1) [2,8,32,256] r7387 c7387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3922
  · exact u3923
  · exact u3924
  · exact u3925

def b7388 : PairBound 9 := { available := 361, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 134 138 377 361 361 489 361), lower := (rows 113 22 134 138 16 32 64 128 256), losses := [] }

theorem u7388 : Upper (D 1) (R 1) [112,20,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7389 : Route 9 := (fun mask => (mask,id))

def c7389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u7389 : Upper (D 1) (R 1) [112,20,130,160] 13 := by
  apply FastRouting.sound _ _ [112,20,130,160] 13 (by decide) (choices 1) [1,2,8,64,256] r7389 c7389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3926
  · exact u3927
  · exact u3928
  · exact u3929
  · exact u3930

def r7390 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7390 : Upper (D 1) (R 1) [112,20,130,257] 13 := by
  apply FastRouting.sound _ _ [112,20,130,257] 13 (by decide) (choices 1) [2,8,32,128] r7390 c7390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3931
  · exact u3932
  · exact u3933
  · exact u3934

def b7391 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 134 266 249 233 233 233 489), lower := (rows 113 22 134 266 16 32 64 128 256), losses := [] }

theorem u7391 : Upper (D 1) (R 1) [112,20,130,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7391
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7392 : Route 9 := (fun mask => (mask,id))

def c7392 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7392 : Upper (D 1) (R 1) [112,20,130,288] 13 := by
  apply FastRouting.sound _ _ [112,20,130,288] 13 (by decide) (choices 1) [1,2,8,64,128] r7392 c7392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3935
  · exact u3936
  · exact u3937
  · exact u3938
  · exact u3939

def r7393 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7393 : Upper (D 1) (R 1) [112,20,130,384] 13 := by
  apply FastRouting.sound _ _ [112,20,130,384] 13 (by decide) (choices 1) [1,2,8,32] r7393 c7393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3940
  · exact u3941
  · exact u3942
  · exact u3943

def b7394 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 140 11 498 482 482 482 482), lower := (rows 113 22 140 11 16 32 64 128 256), losses := [] }

theorem u7394 : Upper (D 1) (R 1) [112,20,136,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7394
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7395 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 140 41 466 482 450 450 450), lower := (rows 113 22 140 41 16 32 64 128 256), losses := [] }

theorem u7395 : Upper (D 1) (R 1) [112,20,136,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7395
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7396 : Route 9 := (fun mask => (mask,id))

def c7396 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u7396 : Upper (D 1) (R 1) [112,20,136,34] 13 := by
  apply FastRouting.sound _ _ [112,20,136,34] 13 (by decide) (choices 1) [1,2,64,128,256] r7396 c7396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3944
  · exact u3945
  · exact u3946
  · exact u3947
  · exact u3948

def b7397 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 140 104 403 419 451 387 387), lower := (rows 113 22 140 104 16 32 64 128 256), losses := [] }

theorem u7397 : Upper (D 1) (R 1) [112,20,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7398 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 140 137 370 354 354 482 354), lower := (rows 113 22 140 137 16 32 64 128 256), losses := [] }

theorem u7398 : Upper (D 1) (R 1) [112,20,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7399 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 140 138 371 355 355 483 355), lower := (rows 113 22 140 138 16 32 64 128 256), losses := [] }

theorem u7399 : Upper (D 1) (R 1) [112,20,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7399
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7400 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 140 168 339 355 323 451 323), lower := (rows 113 22 140 168 16 32 64 128 256), losses := [] }

theorem u7400 : Upper (D 1) (R 1) [112,20,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7400
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7401 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7401 : Upper (D 1) (R 1) [112,20,136,257] 13 := by
  apply FastRouting.sound _ _ [112,20,136,257] 13 (by decide) (choices 1) [2,32,128] r7401 c7401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3949
  · exact u3950
  · exact u3951

def r7402 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7402 : Upper (D 1) (R 1) [112,20,136,258] 13 := by
  apply FastRouting.sound _ _ [112,20,136,258] 13 (by decide) (choices 1) [1,2,32,128] r7402 c7402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3952
  · exact u3953
  · exact u3954
  · exact u3955

def r7403 : Route 9 := (fun mask => (mask,id))

def c7403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7403 : Upper (D 1) (R 1) [112,20,136,288] 13 := by
  apply FastRouting.sound _ _ [112,20,136,288] 13 (by decide) (choices 1) [1,2,64,128] r7403 c7403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3956
  · exact u3957
  · exact u3958
  · exact u3959

def b7404 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 140 392 115 99 99 227 355), lower := (rows 113 22 140 392 16 32 64 128 256), losses := [] }

theorem u7404 : Upper (D 1) (R 1) [112,20,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7404
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7405 : PairBound 9 := { available := 458, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 11 474 490 458 458 458), lower := (rows 113 22 164 11 16 32 64 128 256), losses := [] }

theorem u7405 : Upper (D 1) (R 1) [112,20,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7406 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 164 73 410 426 458 394 394), lower := (rows 113 22 164 73 16 32 64 128 256), losses := [] }

theorem u7406 : Upper (D 1) (R 1) [112,20,160,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7406
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7407 : Route 9 := (fun mask => (mask,id))

def c7407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u7407 : Upper (D 1) (R 1) [112,20,160,66] 13 := by
  apply FastRouting.sound _ _ [112,20,160,66] 13 (by decide) (choices 1) [1,2,8,128,256] r7407 c7407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3960
  · exact u3961
  · exact u3962
  · exact u3963
  · exact u3964

def r7408 : Route 9 := (fun mask => (mask,id))

def c7408 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u7408 : Upper (D 1) (R 1) [112,20,160,129] 13 := by
  apply FastRouting.sound _ _ [112,20,160,129] 13 (by decide) (choices 1) [2,8,64,256] r7408 c7408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3965
  · exact u3966
  · exact u3967
  · exact u3968

def b7409 : PairBound 9 := { available := 331, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 138 347 363 331 459 331), lower := (rows 113 22 164 138 16 32 64 128 256), losses := [] }

theorem u7409 : Upper (D 1) (R 1) [112,20,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7409
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7410 : Route 9 := (fun mask => (mask,id))

def c7410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7410 : Upper (D 1) (R 1) [112,20,160,192] 13 := by
  apply FastRouting.sound _ _ [112,20,160,192] 13 (by decide) (choices 1) [1,2,8,256] r7410 c7410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3969
  · exact u3970
  · exact u3971
  · exact u3972

def r7411 : Route 9 := (fun mask => (mask,id))

def c7411 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7411 : Upper (D 1) (R 1) [112,20,160,257] 13 := by
  apply FastRouting.sound _ _ [112,20,160,257] 13 (by decide) (choices 1) [2,8,64,128] r7411 c7411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3973
  · exact u3974
  · exact u3975
  · exact u3976

def r7412 : Route 9 := (fun mask => (mask,id))

def c7412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7412 : Upper (D 1) (R 1) [112,20,160,258] 13 := by
  apply FastRouting.sound _ _ [112,20,160,258] 13 (by decide) (choices 1) [1,2,8,64,128] r7412 c7412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3977
  · exact u3978
  · exact u3979
  · exact u3980
  · exact u3981

def r7413 : Route 9 := (fun mask => (mask,id))

def c7413 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7413 : Upper (D 1) (R 1) [112,20,160,320] 13 := by
  apply FastRouting.sound _ _ [112,20,160,320] 13 (by decide) (choices 1) [1,2,8,128] r7413 c7413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3982
  · exact u3983
  · exact u3984
  · exact u3985

def r7414 : Route 9 := (fun mask => (mask,id))

def c7414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7414 : Upper (D 1) (R 1) [112,20,160,384] 13 := by
  apply FastRouting.sound _ _ [112,20,160,384] 13 (by decide) (choices 1) [1,2,8,64] r7414 c7414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3986
  · exact u3987
  · exact u3988
  · exact u3989

def b7415 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 262 11 248 232 232 232 488), lower := (rows 113 22 262 11 16 32 64 128 256), losses := [] }

theorem u7415 : Upper (D 1) (R 1) [112,20,258,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7415
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7416 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 262 41 218 234 202 202 458), lower := (rows 113 22 262 41 16 32 64 128 256), losses := [] }

theorem u7416 : Upper (D 1) (R 1) [112,20,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7416
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7417 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 262 42 217 233 201 201 457), lower := (rows 113 22 262 42 16 32 64 128 256), losses := [] }

theorem u7417 : Upper (D 1) (R 1) [112,20,258,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7417
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7418 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 262 104 155 171 203 139 395), lower := (rows 113 22 262 104 16 32 64 128 256), losses := [] }

theorem u7418 : Upper (D 1) (R 1) [112,20,258,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7418
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7419 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7419 : Upper (D 1) (R 1) [112,20,258,129] 13 := by
  apply FastRouting.sound _ _ [112,20,258,129] 13 (by decide) (choices 1) [2,8,32,128] r7419 c7419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3990
  · exact u3991
  · exact u3992
  · exact u3993

def b7420 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 113, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 262 138 249 233 233 233 489), lower := (rows 113 22 262 138 16 32 64 128 256), losses := [] }

theorem u7420 : Upper (D 1) (R 1) [112,20,258,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7421 : Route 9 := (fun mask => (mask,id))

def c7421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7421 : Upper (D 1) (R 1) [112,20,258,160] 13 := by
  apply FastRouting.sound _ _ [112,20,258,160] 13 (by decide) (choices 1) [1,2,8,64,128] r7421 c7421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3994
  · exact u3995
  · exact u3996
  · exact u3997
  · exact u3998

def b7422 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 268 11 242 226 226 226 482), lower := (rows 113 22 268 11 16 32 64 128 256), losses := [] }

theorem u7422 : Upper (D 1) (R 1) [112,20,264,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7422
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7423 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 268 41 210 226 194 194 450), lower := (rows 113 22 268 41 16 32 64 128 256), losses := [] }

theorem u7423 : Upper (D 1) (R 1) [112,20,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7424 : Route 9 := (fun mask => (mask,id))

def c7424 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7424 : Upper (D 1) (R 1) [112,20,264,34] 13 := by
  apply FastRouting.sound _ _ [112,20,264,34] 13 (by decide) (choices 1) [1,2,64,128] r7424 c7424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3999
  · exact u4000
  · exact u4001
  · exact u4002

def b7425 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 268 104 147 163 195 131 387), lower := (rows 113 22 268 104 16 32 64 128 256), losses := [] }

theorem u7425 : Upper (D 1) (R 1) [112,20,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7425
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7426 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7426 : Upper (D 1) (R 1) [112,20,264,129] 13 := by
  apply FastRouting.sound _ _ [112,20,264,129] 13 (by decide) (choices 1) [2,32,128] r7426 c7426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4003
  · exact u4004
  · exact u4005

def r7427 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7427 : Upper (D 1) (R 1) [112,20,264,130] 13 := by
  apply FastRouting.sound _ _ [112,20,264,130] 13 (by decide) (choices 1) [1,2,32,128] r7427 c7427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4006
  · exact u4007
  · exact u4008
  · exact u4009

def r7428 : Route 9 := (fun mask => (mask,id))

def c7428 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7428 : Upper (D 1) (R 1) [112,20,264,160] 13 := by
  apply FastRouting.sound _ _ [112,20,264,160] 13 (by decide) (choices 1) [1,2,64,128] r7428 c7428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4010
  · exact u4011
  · exact u4012
  · exact u4013

def b7429 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 292 11 218 234 202 202 458), lower := (rows 113 22 292 11 16 32 64 128 256), losses := [] }

theorem u7429 : Upper (D 1) (R 1) [112,20,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7429
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7430 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 292 73 154 170 202 138 394), lower := (rows 113 22 292 73 16 32 64 128 256), losses := [] }

theorem u7430 : Upper (D 1) (R 1) [112,20,288,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7430
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7431 : Route 9 := (fun mask => (mask,id))

def c7431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7431 : Upper (D 1) (R 1) [112,20,288,66] 13 := by
  apply FastRouting.sound _ _ [112,20,288,66] 13 (by decide) (choices 1) [1,2,8,128] r7431 c7431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4014
  · exact u4015
  · exact u4016
  · exact u4017

def r7432 : Route 9 := (fun mask => (mask,id))

def c7432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7432 : Upper (D 1) (R 1) [112,20,288,129] 13 := by
  apply FastRouting.sound _ _ [112,20,288,129] 13 (by decide) (choices 1) [2,8,64,128] r7432 c7432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4018
  · exact u4019
  · exact u4020
  · exact u4021

def r7433 : Route 9 := (fun mask => (mask,id))

def c7433 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7433 : Upper (D 1) (R 1) [112,20,288,130] 13 := by
  apply FastRouting.sound _ _ [112,20,288,130] 13 (by decide) (choices 1) [1,2,8,64,128] r7433 c7433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4022
  · exact u4023
  · exact u4024
  · exact u4025
  · exact u4026

def r7434 : Route 9 := (fun mask => (mask,id))

def c7434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7434 : Upper (D 1) (R 1) [112,20,288,192] 13 := by
  apply FastRouting.sound _ _ [112,20,288,192] 13 (by decide) (choices 1) [1,2,8,128] r7434 c7434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4027
  · exact u4028
  · exact u4029
  · exact u4030

def b7435 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 388 11 250 234 234 234 490), lower := (rows 113 22 388 11 16 32 64 128 256), losses := [] }

theorem u7435 : Upper (D 1) (R 1) [112,20,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7436 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 388 41 218 234 202 202 458), lower := (rows 113 22 388 41 16 32 64 128 256), losses := [] }

theorem u7436 : Upper (D 1) (R 1) [112,20,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7436
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7437 : Route 9 := (fun mask => (mask,id))

def c7437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7437 : Upper (D 1) (R 1) [112,20,384,34] 13 := by
  apply FastRouting.sound _ _ [112,20,384,34] 13 (by decide) (choices 1) [1,2,8,64,128] r7437 c7437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4031
  · exact u4032
  · exact u4033
  · exact u4034
  · exact u4035

def b7438 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 22 388 104 155 171 203 139 395), lower := (rows 113 22 388 104 16 32 64 128 256), losses := [] }

theorem u7438 : Upper (D 1) (R 1) [112,20,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7438
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7439 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7439 : Upper (D 1) (R 1) [112,20,384,129] 13 := by
  apply FastRouting.sound _ _ [112,20,384,129] 13 (by decide) (choices 1) [2,8,32] r7439 c7439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4036
  · exact u4037
  · exact u4038

#print axioms u7439
end Delivery.IrregularNine14.P01
