import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0089
import IrregularNine14P09C0090

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7980 : Route 9 := (fun mask => (mask,id))

def c7980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7980 : Upper (D 9) (R 9) [96,5,10,160,129] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,129] 13 (by decide) (choices 1) [16,64,256] r7980 c7980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5371
  · exact u5372
  · exact u5373

def r7981 : Route 9 := (fun mask => (mask,id))

def c7981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7981 : Upper (D 9) (R 9) [96,5,10,160,192] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,192] 13 (by decide) (choices 1) [1,16,256] r7981 c7981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5374
  · exact u5375
  · exact u5376

def r7982 : Route 9 := (fun mask => (mask,id))

def c7982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7982 : Upper (D 9) (R 9) [96,5,10,160,257] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,257] 13 (by decide) (choices 1) [16,64,128,256] r7982 c7982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5377
  · exact u5378
  · exact u5379
  · exact u5380

def r7983 : Route 9 := (fun mask => (mask,id))

def c7983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7983 : Upper (D 9) (R 9) [96,5,10,160,320] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,320] 13 (by decide) (choices 1) [1,16,128,256] r7983 c7983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5381
  · exact u5382
  · exact u5383
  · exact u5384

def r7984 : Route 9 := (fun mask => (mask,id))

def c7984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7984 : Upper (D 9) (R 9) [96,5,10,160,384] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,384] 13 (by decide) (choices 1) [1,16,64,256] r7984 c7984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5385
  · exact u5386
  · exact u5387
  · exact u5388

def b7985 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 7 14 392 49 496 464 464 464), lower := (rows 97 7 14 392 49 32 64 128 256), losses := [] }

theorem u7985 : Upper (D 9) (R 9) [96,5,10,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7985 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7986 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 7 14 392 112 433 465 401 401), lower := (rows 97 7 14 392 112 32 64 128 256), losses := [] }

theorem u7986 : Upper (D 9) (R 9) [96,5,10,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7986 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7987 : Route 9 := (fun mask => (mask,id))

def c7987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7987 : Upper (D 9) (R 9) [96,5,10,384,129] 13 := by
  apply FastRouting.sound _ _ [96,5,10,384,129] 13 (by decide) (choices 1) [16,64,256] r7987 c7987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5389
  · exact u5390
  · exact u5391

def r7988 : Route 9 := (fun mask => (mask,id))

def c7988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7988 : Upper (D 9) (R 9) [96,5,10,384,160] 13 := by
  apply FastRouting.sound _ _ [96,5,10,384,160] 13 (by decide) (choices 1) [1,16,64,256] r7988 c7988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5392
  · exact u5393
  · exact u5394
  · exact u5395

def b7989 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 97 7 14 392 400 113 113 241 369), lower := (rows 97 7 14 392 400 32 64 128 256), losses := [] }

theorem u7989 : Upper (D 9) (R 9) [96,5,10,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7989 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7990 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 30, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 28 41 82 416 448 384 384), lower := (rows 97 7 28 41 82 32 64 128 256), losses := [] }

theorem u7990 : Upper (D 9) (R 9) [96,5,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7990 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7991 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 28 41 146 480 448 448 448), lower := (rows 97 7 28 41 146 32 64 128 256), losses := [] }

theorem u7991 : Upper (D 9) (R 9) [96,5,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7991 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7992 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 28 41 208 418 450 386 386), lower := (rows 97 7 28 41 208 32 64 128 256), losses := [] }

theorem u7992 : Upper (D 9) (R 9) [96,5,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7992 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7993 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 28 41 400 482 450 450 450), lower := (rows 97 7 28 41 400 32 64 128 256), losses := [] }

theorem u7993 : Upper (D 9) (R 9) [96,5,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7993 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7994 : Route 9 := (fun mask => (mask,id))

def c7994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7994 : Upper (D 9) (R 9) [96,5,24,34,129] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,129] 13 (by decide) (choices 1) [64,128,256] r7994 c7994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5396
  · exact u5397
  · exact u5398

def r7995 : Route 9 := (fun mask => (mask,id))

def c7995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7995 : Upper (D 9) (R 9) [96,5,24,34,192] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,192] 13 (by decide) (choices 1) [1,128,256] r7995 c7995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5399
  · exact u5400
  · exact u5401

def r7996 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7996 : Upper (D 9) (R 9) [96,5,24,34,384] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,384] 13 (by decide) (choices 1) [1,64,128] r7996 c7996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5402
  · exact u5403
  · exact u5404

def b7997 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 28 104 145 418 450 386 386), lower := (rows 97 7 28 104 145 32 64 128 256), losses := [] }

theorem u7997 : Upper (D 9) (R 9) [96,5,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7997 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7998 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 28 104 146 417 449 385 385), lower := (rows 97 7 28 104 146 32 64 128 256), losses := [] }

theorem u7998 : Upper (D 9) (R 9) [96,5,24,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7998 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7999 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 28 104 400 419 451 387 387), lower := (rows 97 7 28 104 400 32 64 128 256), losses := [] }

theorem u7999 : Upper (D 9) (R 9) [96,5,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7999 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8000 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 22, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 28 137 146 352 352 480 352), lower := (rows 97 7 28 137 146 32 64 128 256), losses := [] }

theorem u8000 : Upper (D 9) (R 9) [96,5,24,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8000 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8001 : Route 9 := (fun mask => (mask,id))

def c8001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8001 : Upper (D 9) (R 9) [96,5,24,129,160] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,160] 13 (by decide) (choices 1) [2,64,256] r8001 c8001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5405
  · exact u5406
  · exact u5407

def r8002 : Route 9 := (fun mask => (mask,id))

def c8002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8002 : Upper (D 9) (R 9) [96,5,24,129,258] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,258] 13 (by decide) (choices 1) [64,128,256] r8002 c8002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5408
  · exact u5409
  · exact u5410

def r8003 : Route 9 := (fun mask => (mask,id))

def c8003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8003 : Upper (D 9) (R 9) [96,5,24,129,288] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,288] 13 (by decide) (choices 1) [2,64,128,256] r8003 c8003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5411
  · exact u5412
  · exact u5413
  · exact u5414

def r8004 : Route 9 := (fun mask => (mask,id))

def c8004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8004 : Upper (D 9) (R 9) [96,5,24,129,384] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,384] 13 (by decide) (choices 1) [2,64,256] r8004 c8004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5415
  · exact u5416
  · exact u5417

def r8005 : Route 9 := (fun mask => (mask,id))

def c8005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8005 : Upper (D 9) (R 9) [96,5,24,130,160] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130,160] 13 (by decide) (choices 1) [1,64,256] r8005 c8005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5418
  · exact u5419
  · exact u5420

def r8006 : Route 9 := (fun mask => (mask,id))

def c8006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8006 : Upper (D 9) (R 9) [96,5,24,130,288] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130,288] 13 (by decide) (choices 1) [1,64,128,256] r8006 c8006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5421
  · exact u5422
  · exact u5423
  · exact u5424

def r8007 : Route 9 := (fun mask => (mask,id))

def c8007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8007 : Upper (D 9) (R 9) [96,5,24,130,384] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130,384] 13 (by decide) (choices 1) [1,64,256] r8007 c8007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5425
  · exact u5426
  · exact u5427

def r8008 : Route 9 := (fun mask => (mask,id))

def c8008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8008 : Upper (D 9) (R 9) [96,5,24,160,192] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160,192] 13 (by decide) (choices 1) [1,2,256] r8008 c8008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5428
  · exact u5429
  · exact u5430

def r8009 : Route 9 := (fun mask => (mask,id))

def c8009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8009 : Upper (D 9) (R 9) [96,5,24,160,320] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160,320] 13 (by decide) (choices 1) [1,2,128,256] r8009 c8009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5431
  · exact u5432
  · exact u5433
  · exact u5434

def r8010 : Route 9 := (fun mask => (mask,id))

def c8010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8010 : Upper (D 9) (R 9) [96,5,24,160,384] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160,384] 13 (by decide) (choices 1) [1,2,64,256] r8010 c8010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5435
  · exact u5436
  · exact u5437
  · exact u5438

def b8011 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0),(4,5)], upper := (rows 97 7 28 392 400 99 99 227 355), lower := (rows 97 7 28 392 400 32 64 128 256), losses := [] }

theorem u8011 : Upper (D 9) (R 9) [96,5,24,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8011 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8012 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 30, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 37 26 88 416 448 384 384), lower := (rows 97 7 37 26 88 32 64 128 256), losses := [] }

theorem u8012 : Upper (D 9) (R 9) [96,5,33,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8012 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8013 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 26 152 480 448 448 448), lower := (rows 97 7 37 26 152 32 64 128 256), losses := [] }

theorem u8013 : Upper (D 9) (R 9) [96,5,33,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8013 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8014 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 26 208 424 456 392 392), lower := (rows 97 7 37 26 208 32 64 128 256), losses := [] }

theorem u8014 : Upper (D 9) (R 9) [96,5,33,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8014 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8015 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 26 400 488 456 456 456), lower := (rows 97 7 37 26 400 32 64 128 256), losses := [] }

theorem u8015 : Upper (D 9) (R 9) [96,5,33,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8015 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8016 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 37 74 152 432 464 400 400), lower := (rows 97 7 37 74 152 32 64 128 256), losses := [] }

theorem u8016 : Upper (D 9) (R 9) [96,5,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8016 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8017 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 37 74 400 440 472 408 408), lower := (rows 97 7 37 74 400 32 64 128 256), losses := [] }

theorem u8017 : Upper (D 9) (R 9) [96,5,33,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8017 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8018 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 88 146 424 456 392 392), lower := (rows 97 7 37 88 146 32 64 128 256), losses := [] }

theorem u8018 : Upper (D 9) (R 9) [96,5,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8018 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8019 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5),(1,7),(1,8),(2,7),(2,8)], upper := (rows 97 7 37 88 152 418 450 386 386), lower := (rows 97 7 37 88 152 32 64 128 256), losses := [] }

theorem u8019 : Upper (D 9) (R 9) [96,5,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8019 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8020 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 88 400 426 458 394 394), lower := (rows 97 7 37 88 400 32 64 128 256), losses := [] }

theorem u8020 : Upper (D 9) (R 9) [96,5,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8020 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8021 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 138 208 312 344 408 280), lower := (rows 97 7 37 138 208 32 64 128 256), losses := [] }

theorem u8021 : Upper (D 9) (R 9) [96,5,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8021 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8022 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 138 280 496 464 464 464), lower := (rows 97 7 37 138 280 32 64 128 256), losses := [] }

theorem u8022 : Upper (D 9) (R 9) [96,5,33,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8022 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8023 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 138 336 440 472 408 408), lower := (rows 97 7 37 138 336 32 64 128 256), losses := [] }

theorem u8023 : Upper (D 9) (R 9) [96,5,33,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8023 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8024 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 138 400 376 344 472 344), lower := (rows 97 7 37 138 400 32 64 128 256), losses := [] }

theorem u8024 : Upper (D 9) (R 9) [96,5,33,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8024 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8025 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 152 280 482 450 450 450), lower := (rows 97 7 37 152 280 32 64 128 256), losses := [] }

theorem u8025 : Upper (D 9) (R 9) [96,5,33,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8025 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8026 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 152 336 426 458 394 394), lower := (rows 97 7 37 152 336 32 64 128 256), losses := [] }

theorem u8026 : Upper (D 9) (R 9) [96,5,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8026 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8027 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 200 400 314 346 410 282), lower := (rows 97 7 37 200 400 32 64 128 256), losses := [] }

theorem u8027 : Upper (D 9) (R 9) [96,5,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8027 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8028 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 25 152 480 448 448 448), lower := (rows 97 7 38 25 152 32 64 128 256), losses := [] }

theorem u8028 : Upper (D 9) (R 9) [96,5,34,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8028 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8029 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 25 208 424 456 392 392), lower := (rows 97 7 38 25 208 32 64 128 256), losses := [] }

theorem u8029 : Upper (D 9) (R 9) [96,5,34,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8029 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8030 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 25 400 488 456 456 456), lower := (rows 97 7 38 25 400 32 64 128 256), losses := [] }

theorem u8030 : Upper (D 9) (R 9) [96,5,34,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8030 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8031 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 88 145 424 456 392 392), lower := (rows 97 7 38 88 145 32 64 128 256), losses := [] }

theorem u8031 : Upper (D 9) (R 9) [96,5,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8031 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8032 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 38 88 152 417 449 385 385), lower := (rows 97 7 38 88 152 32 64 128 256), losses := [] }

theorem u8032 : Upper (D 9) (R 9) [96,5,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8032 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8033 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 88 400 425 457 393 393), lower := (rows 97 7 38 88 400 32 64 128 256), losses := [] }

theorem u8033 : Upper (D 9) (R 9) [96,5,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8033 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8034 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 137 208 312 344 408 280), lower := (rows 97 7 38 137 208 32 64 128 256), losses := [] }

theorem u8034 : Upper (D 9) (R 9) [96,5,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8034 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8035 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 137 280 496 464 464 464), lower := (rows 97 7 38 137 280 32 64 128 256), losses := [] }

theorem u8035 : Upper (D 9) (R 9) [96,5,34,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8035 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8036 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 137 336 440 472 408 408), lower := (rows 97 7 38 137 336 32 64 128 256), losses := [] }

theorem u8036 : Upper (D 9) (R 9) [96,5,34,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8036 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8037 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 137 400 376 344 472 344), lower := (rows 97 7 38 137 400 32 64 128 256), losses := [] }

theorem u8037 : Upper (D 9) (R 9) [96,5,34,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8037 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8038 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 152 280 481 449 449 449), lower := (rows 97 7 38 152 280 32 64 128 256), losses := [] }

theorem u8038 : Upper (D 9) (R 9) [96,5,34,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8038 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8039 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 152 336 425 457 393 393), lower := (rows 97 7 38 152 336 32 64 128 256), losses := [] }

theorem u8039 : Upper (D 9) (R 9) [96,5,34,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8039 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8039
end Delivery.IrregularNine14.P09
