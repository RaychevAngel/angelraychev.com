import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0171
import IrregularNine14P06C0172
import IrregularNine14P06C0173

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28980 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 133 88 82 293 357 421 293), lower := (rows 7 42 133 88 82 32 64 128 256), losses := [] }

theorem u28980 : Upper (D 6) (R 6) [6,40,129,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28980
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28981 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 133 88 84 291 355 419 291), lower := (rows 7 42 133 88 84 32 64 128 256), losses := [] }

theorem u28981 : Upper (D 6) (R 6) [6,40,129,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28981
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28982 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 88 112 295 327 391 263), lower := (rows 7 42 133 88 112 32 64 128 256), losses := [] }

theorem u28982 : Upper (D 6) (R 6) [6,40,129,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28982
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28983 : Route 9 := (fun mask => (mask,id))

def c28983 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28983 : Upper (D 6) (R 6) [6,40,129,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80,257] 13 (by decide) (choices 1) [2,4,64] r28983 c28983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10298
  · exact u10299
  · exact u10300

def r28984 : Route 9 := (fun mask => (mask,id))

def c28984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28984 : Upper (D 6) (R 6) [6,40,129,80,258] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80,258] 13 (by decide) (choices 1) [1,4,64] r28984 c28984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10301
  · exact u10302
  · exact u10303

def r28985 : Route 9 := (fun mask => (mask,id))

def c28985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28985 : Upper (D 6) (R 6) [6,40,129,80,260] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80,260] 13 (by decide) (choices 1) [1,2,64] r28985 c28985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10304
  · exact u10305
  · exact u10306

def r28986 : Route 9 := (fun mask => (mask,id))

def c28986 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28986 : Upper (D 6) (R 6) [6,40,129,80,288] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80,288] 13 (by decide) (choices 1) [1,2,4,64] r28986 c28986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10307
  · exact u10308
  · exact u10309
  · exact u10310

def b28987 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 133 88 336 39 103 167 295), lower := (rows 7 42 133 88 336 32 64 128 256), losses := [] }

theorem u28987 : Upper (D 6) (R 6) [6,40,129,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28987
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28988 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 133 265 22 112 112 240 368), lower := (rows 7 42 133 265 22 32 64 128 256), losses := [] }

theorem u28988 : Upper (D 6) (R 6) [6,40,129,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28988
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28989 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 265 50 116 84 212 340), lower := (rows 7 42 133 265 50 32 64 128 256), losses := [] }

theorem u28989 : Upper (D 6) (R 6) [6,40,129,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28989
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28990 : Route 9 := (fun mask => (mask,id))

def c28990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28990 : Upper (D 6) (R 6) [6,40,129,257,36] 13 := by
  apply FastRouting.sound _ _ [6,40,129,257,36] 13 (by decide) (choices 1) [2,16,64] r28990 c28990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10311
  · exact u10312
  · exact u10313

def r28991 : Route 9 := (fun mask => (mask,id))

def c28991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28991 : Upper (D 6) (R 6) [6,40,129,257,66] 13 := by
  apply FastRouting.sound _ _ [6,40,129,257,66] 13 (by decide) (choices 1) [4,16,64] r28991 c28991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10314
  · exact u10315
  · exact u10316

def r28992 : Route 9 := (fun mask => (mask,id))

def c28992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28992 : Upper (D 6) (R 6) [6,40,129,257,68] 13 := by
  apply FastRouting.sound _ _ [6,40,129,257,68] 13 (by decide) (choices 1) [2,16,64] r28992 c28992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10317
  · exact u10318
  · exact u10319

def r28993 : Route 9 := (fun mask => (mask,id))

def c28993 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28993 : Upper (D 6) (R 6) [6,40,129,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,129,257,96] 13 (by decide) (choices 1) [2,4,16,64] r28993 c28993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10320
  · exact u10321
  · exact u10322
  · exact u10323

def b28994 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 362, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 266 21 112 112 240 368), lower := (rows 7 42 133 266 21 32 64 128 256), losses := [] }

theorem u28994 : Upper (D 6) (R 6) [6,40,129,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28994
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28995 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 42 133 266 49 116 84 212 340), lower := (rows 7 42 133 266 49 32 64 128 256), losses := [] }

theorem u28995 : Upper (D 6) (R 6) [6,40,129,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28995
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28996 : Route 9 := (fun mask => (mask,id))

def c28996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28996 : Upper (D 6) (R 6) [6,40,129,258,36] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,36] 13 (by decide) (choices 1) [1,16,64] r28996 c28996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10324
  · exact u10325
  · exact u10326

def r28997 : Route 9 := (fun mask => (mask,id))

def c28997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28997 : Upper (D 6) (R 6) [6,40,129,258,65] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,65] 13 (by decide) (choices 1) [4,16,64] r28997 c28997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10327
  · exact u10328
  · exact u10329

def r28998 : Route 9 := (fun mask => (mask,id))

def c28998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28998 : Upper (D 6) (R 6) [6,40,129,258,68] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,68] 13 (by decide) (choices 1) [1,16,64] r28998 c28998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10330
  · exact u10331
  · exact u10332

def r28999 : Route 9 := (fun mask => (mask,id))

def c28999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28999 : Upper (D 6) (R 6) [6,40,129,258,96] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258,96] 13 (by decide) (choices 1) [1,4,16,64] r28999 c28999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10333
  · exact u10334
  · exact u10335
  · exact u10336

def b29000 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 42 133 268 19 112 112 240 368), lower := (rows 7 42 133 268 19 32 64 128 256), losses := [] }

theorem u29000 : Upper (D 6) (R 6) [6,40,129,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29000
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29001 : Route 9 := (fun mask => (mask,id))

def c29001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29001 : Upper (D 6) (R 6) [6,40,129,260,33] 13 := by
  apply FastRouting.sound _ _ [6,40,129,260,33] 13 (by decide) (choices 1) [2,16,64] r29001 c29001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10337
  · exact u10338
  · exact u10339

def b29002 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 268 50 113 81 209 337), lower := (rows 7 42 133 268 50 32 64 128 256), losses := [] }

theorem u29002 : Upper (D 6) (R 6) [6,40,129,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29002
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29003 : Route 9 := (fun mask => (mask,id))

def c29003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29003 : Upper (D 6) (R 6) [6,40,129,260,65] 13 := by
  apply FastRouting.sound _ _ [6,40,129,260,65] 13 (by decide) (choices 1) [2,16,64] r29003 c29003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10340
  · exact u10341
  · exact u10342

def r29004 : Route 9 := (fun mask => (mask,id))

def c29004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29004 : Upper (D 6) (R 6) [6,40,129,260,66] 13 := by
  apply FastRouting.sound _ _ [6,40,129,260,66] 13 (by decide) (choices 1) [1,16,64] r29004 c29004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10343
  · exact u10344
  · exact u10345

def r29005 : Route 9 := (fun mask => (mask,id))

def c29005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29005 : Upper (D 6) (R 6) [6,40,129,260,96] 13 := by
  apply FastRouting.sound _ _ [6,40,129,260,96] 13 (by decide) (choices 1) [1,2,16,64] r29005 c29005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10346
  · exact u10347
  · exact u10348
  · exact u10349

def b29006 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 133 280 19 100 100 228 356), lower := (rows 7 42 133 280 19 32 64 128 256), losses := [] }

theorem u29006 : Upper (D 6) (R 6) [6,40,129,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29006
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29007 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 362, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 280 21 98 98 226 354), lower := (rows 7 42 133 280 21 32 64 128 256), losses := [] }

theorem u29007 : Upper (D 6) (R 6) [6,40,129,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29007
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29008 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 133 280 22 97 97 225 353), lower := (rows 7 42 133 280 22 32 64 128 256), losses := [] }

theorem u29008 : Upper (D 6) (R 6) [6,40,129,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29008
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29009 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 133 280 49 102 70 198 326), lower := (rows 7 42 133 280 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 33 65 129 257), good := (rows 486 42 484 282 506 32 64 128 256) }] }

theorem u29009 : Upper (D 6) (R 6) [6,40,129,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29009
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29010 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 280 50 101 69 197 325), lower := (rows 7 42 133 280 50 32 64 128 256), losses := [] }

theorem u29010 : Upper (D 6) (R 6) [6,40,129,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29010
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29011 : Route 9 := (fun mask => (mask,id))

def c29011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29011 : Upper (D 6) (R 6) [6,40,129,272,36] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,36] 13 (by decide) (choices 1) [1,2,64] r29011 c29011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10350
  · exact u10351
  · exact u10352

def r29012 : Route 9 := (fun mask => (mask,id))

def c29012 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29012 : Upper (D 6) (R 6) [6,40,129,272,65] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,65] 13 (by decide) (choices 1) [2,4,64] r29012 c29012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10353
  · exact u10354
  · exact u10355

def r29013 : Route 9 := (fun mask => (mask,id))

def c29013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29013 : Upper (D 6) (R 6) [6,40,129,272,66] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,66] 13 (by decide) (choices 1) [1,4,64] r29013 c29013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10356
  · exact u10357
  · exact u10358

def r29014 : Route 9 := (fun mask => (mask,id))

def c29014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29014 : Upper (D 6) (R 6) [6,40,129,272,68] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,68] 13 (by decide) (choices 1) [1,2,64] r29014 c29014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10359
  · exact u10360
  · exact u10361

def r29015 : Route 9 := (fun mask => (mask,id))

def c29015 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29015 : Upper (D 6) (R 6) [6,40,129,272,96] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272,96] 13 (by decide) (choices 1) [1,2,4,64] r29015 c29015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10362
  · exact u10363
  · exact u10364
  · exact u10365

def b29016 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 133 328 19 116 116 244 372), lower := (rows 7 42 133 328 19 32 64 128 256), losses := [] }

theorem u29016 : Upper (D 6) (R 6) [6,40,129,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29016
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29017 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 362, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 328 21 114 114 242 370), lower := (rows 7 42 133 328 21 32 64 128 256), losses := [] }

theorem u29017 : Upper (D 6) (R 6) [6,40,129,320,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29017
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29018 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 133 328 22 113 113 241 369), lower := (rows 7 42 133 328 22 32 64 128 256), losses := [] }

theorem u29018 : Upper (D 6) (R 6) [6,40,129,320,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29018
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29019 : Route 9 := (fun mask => (mask,id))

def c29019 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29019 : Upper (D 6) (R 6) [6,40,129,320,33] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,33] 13 (by decide) (choices 1) [2,4,16,64] r29019 c29019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10366
  · exact u10367
  · exact u10368
  · exact u10369

def b29020 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 328 50 117 85 213 341), lower := (rows 7 42 133 328 50 32 64 128 256), losses := [] }

theorem u29020 : Upper (D 6) (R 6) [6,40,129,320,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29020
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29021 : Route 9 := (fun mask => (mask,id))

def c29021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29021 : Upper (D 6) (R 6) [6,40,129,320,36] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,36] 13 (by decide) (choices 1) [1,2,16,64] r29021 c29021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10370
  · exact u10371
  · exact u10372
  · exact u10373

def r29022 : Route 9 := (fun mask => (mask,id))

def c29022 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29022 : Upper (D 6) (R 6) [6,40,129,320,65] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,65] 13 (by decide) (choices 1) [2,4,16] r29022 c29022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10374
  · exact u10375
  · exact u10376

def r29023 : Route 9 := (fun mask => (mask,id))

def c29023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29023 : Upper (D 6) (R 6) [6,40,129,320,66] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,66] 13 (by decide) (choices 1) [1,4,16] r29023 c29023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10377
  · exact u10378
  · exact u10379

def r29024 : Route 9 := (fun mask => (mask,id))

def c29024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29024 : Upper (D 6) (R 6) [6,40,129,320,68] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,68] 13 (by decide) (choices 1) [1,2,16] r29024 c29024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10380
  · exact u10381
  · exact u10382

def r29025 : Route 9 := (fun mask => (mask,id))

def c29025 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29025 : Upper (D 6) (R 6) [6,40,129,320,96] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,96] 13 (by decide) (choices 1) [1,2,4,16] r29025 c29025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10383
  · exact u10384
  · exact u10385
  · exact u10386

def b29026 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 148 73 19 356 356 484 356), lower := (rows 7 42 148 73 19 32 64 128 256), losses := [] }

theorem u29026 : Upper (D 6) (R 6) [6,40,144,65,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29026
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29027 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 42 148 73 21 354 354 482 354), lower := (rows 7 42 148 73 21 32 64 128 256), losses := [] }

theorem u29027 : Upper (D 6) (R 6) [6,40,144,65,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29027
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29028 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 42 148 73 22 353 353 481 353), lower := (rows 7 42 148 73 22 32 64 128 256), losses := [] }

theorem u29028 : Upper (D 6) (R 6) [6,40,144,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29028
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29029 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 328, targets := 32 }], pairs := [(1,0),(2,0),(3,5)], upper := (rows 7 42 148 73 49 358 326 454 326), lower := (rows 7 42 148 73 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 33 65 129 257), good := (rows 486 42 148 490 500 32 64 128 256) }] }

theorem u29029 : Upper (D 6) (R 6) [6,40,144,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29029
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29030 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 148 73 50 357 325 453 325), lower := (rows 7 42 148 73 50 32 64 128 256), losses := [] }

theorem u29030 : Upper (D 6) (R 6) [6,40,144,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29030
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29031 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 328, targets := 32 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 7 42 148 73 52 355 323 451 323), lower := (rows 7 42 148 73 52 32 64 128 256), losses := [] }

theorem u29031 : Upper (D 6) (R 6) [6,40,144,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29031
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29032 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 7 42 148 73 81 294 358 422 294), lower := (rows 7 42 148 73 81 32 64 128 256), losses := [] }

theorem u29032 : Upper (D 6) (R 6) [6,40,144,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29032
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29033 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 360, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 42 148 73 82 293 357 421 293), lower := (rows 7 42 148 73 82 32 64 128 256), losses := [] }

theorem u29033 : Upper (D 6) (R 6) [6,40,144,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29033
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29034 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 42 148 73 84 291 355 419 291), lower := (rows 7 42 148 73 84 32 64 128 256), losses := [] }

theorem u29034 : Upper (D 6) (R 6) [6,40,144,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29034
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29035 : Route 9 := (fun mask => (mask,id))

def c29035 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29035 : Upper (D 6) (R 6) [6,40,144,65,96] 13 := by
  apply FastRouting.sound _ _ [6,40,144,65,96] 13 (by decide) (choices 1) [1,2,4,256] r29035 c29035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10387
  · exact u10388
  · exact u10389
  · exact u10390

def r29036 : Route 9 := (fun mask => (mask,id))

def c29036 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29036 : Upper (D 6) (R 6) [6,40,144,65,257] 13 := by
  apply FastRouting.sound _ _ [6,40,144,65,257] 13 (by decide) (choices 1) [2,4,64] r29036 c29036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10391
  · exact u10392
  · exact u10393

def r29037 : Route 9 := (fun mask => (mask,id))

def c29037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29037 : Upper (D 6) (R 6) [6,40,144,65,258] 13 := by
  apply FastRouting.sound _ _ [6,40,144,65,258] 13 (by decide) (choices 1) [1,4,64] r29037 c29037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10394
  · exact u10395
  · exact u10396

def r29038 : Route 9 := (fun mask => (mask,id))

def c29038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29038 : Upper (D 6) (R 6) [6,40,144,65,260] 13 := by
  apply FastRouting.sound _ _ [6,40,144,65,260] 13 (by decide) (choices 1) [1,2,64] r29038 c29038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10397
  · exact u10398
  · exact u10399

def r29039 : Route 9 := (fun mask => (mask,id))

def c29039 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29039 : Upper (D 6) (R 6) [6,40,144,65,288] 13 := by
  apply FastRouting.sound _ _ [6,40,144,65,288] 13 (by decide) (choices 1) [1,2,4,64] r29039 c29039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10400
  · exact u10401
  · exact u10402
  · exact u10403

#print axioms u29039
end Delivery.IrregularNine14.P06
