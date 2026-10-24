import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0232
import IrregularNine14P07C0233

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31380 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 44 152 145 355 323 451 323), lower := (rows 7 98 44 152 145 32 64 128 256), losses := [] }

theorem u31380 : Upper (D 7) (R 7) [6,96,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31381 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 44 152 146 353 321 449 321), lower := (rows 7 98 44 152 146 32 64 128 256), losses := [] }

theorem u31381 : Upper (D 7) (R 7) [6,96,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31382 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 44 152 208 291 323 387 259), lower := (rows 7 98 44 152 208 32 64 128 256), losses := [] }

theorem u31382 : Upper (D 7) (R 7) [6,96,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31383 : Route 9 := (fun mask => (mask,id))

def c31383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31383 : Upper (D 7) (R 7) [6,96,40,144,257] 13 := by
  apply FastRouting.sound _ _ [6,96,40,144,257] 13 (by decide) (choices 1) [1,2,64,128] r31383 c31383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13927
  · exact u13928
  · exact u13929
  · exact u13930

def r31384 : Route 9 := (fun mask => (mask,id))

def c31384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31384 : Upper (D 7) (R 7) [6,96,40,144,258] 13 := by
  apply FastRouting.sound _ _ [6,96,40,144,258] 13 (by decide) (choices 1) [1,64,128] r31384 c31384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13931
  · exact u13932
  · exact u13933

def r31385 : Route 9 := (fun mask => (mask,id))

def c31385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31385 : Upper (D 7) (R 7) [6,96,40,144,320] 13 := by
  apply FastRouting.sound _ _ [6,96,40,144,320] 13 (by decide) (choices 1) [1,2,128] r31385 c31385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13934
  · exact u13935
  · exact u13936

def b31386 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 44 152 400 99 67 195 323), lower := (rows 7 98 44 152 400 32 64 128 256), losses := [] }

theorem u31386 : Upper (D 7) (R 7) [6,96,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31387 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(4,5)], upper := (rows 7 98 44 200 19 433 465 401 401), lower := (rows 7 98 44 200 19 32 64 128 256), losses := [] }

theorem u31387 : Upper (D 7) (R 7) [6,96,40,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31388 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(3,5),(4,5),(4,6)], upper := (rows 7 98 44 200 145 307 339 403 275), lower := (rows 7 98 44 200 145 32 64 128 256), losses := [] }

theorem u31388 : Upper (D 7) (R 7) [6,96,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31389 : Route 9 := (fun mask => (mask,id))

def c31389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31389 : Upper (D 7) (R 7) [6,96,40,192,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,192,130] 13 (by decide) (choices 1) [1,16,256] r31389 c31389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13937
  · exact u13938
  · exact u13939

def r31390 : Route 9 := (fun mask => (mask,id))

def c31390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31390 : Upper (D 7) (R 7) [6,96,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,96,40,192,257] 13 (by decide) (choices 1) [1,2,16,128] r31390 c31390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13940
  · exact u13941
  · exact u13942
  · exact u13943

def r31391 : Route 9 := (fun mask => (mask,id))

def c31391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31391 : Upper (D 7) (R 7) [6,96,40,192,258] 13 := by
  apply FastRouting.sound _ _ [6,96,40,192,258] 13 (by decide) (choices 1) [1,16,128] r31391 c31391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13944
  · exact u13945
  · exact u13946

def r31392 : Route 9 := (fun mask => (mask,id))

def c31392 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31392 : Upper (D 7) (R 7) [6,96,40,192,384] 13 := by
  apply FastRouting.sound _ _ [6,96,40,192,384] 13 (by decide) (choices 1) [1,2,16] r31392 c31392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13947
  · exact u13948
  · exact u13949

def b31393 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 98 44 265 19 240 208 208 464), lower := (rows 7 98 44 265 19 32 64 128 256), losses := [] }

theorem u31393 : Upper (D 7) (R 7) [6,96,40,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31394 : Route 9 := (fun mask => (mask,id))

def c31394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31394 : Upper (D 7) (R 7) [6,96,40,257,65] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257,65] 13 (by decide) (choices 1) [2,16,128] r31394 c31394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13950
  · exact u13951
  · exact u13952

def b31395 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 44 265 82 177 209 145 401), lower := (rows 7 98 44 265 82 32 64 128 256), losses := [] }

theorem u31395 : Upper (D 7) (R 7) [6,96,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31396 : Route 9 := (fun mask => (mask,id))

def c31396 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31396 : Upper (D 7) (R 7) [6,96,40,257,129] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257,129] 13 (by decide) (choices 1) [2,16,64,128] r31396 c31396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13953
  · exact u13954
  · exact u13955
  · exact u13956

def r31397 : Route 9 := (fun mask => (mask,id))

def c31397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31397 : Upper (D 7) (R 7) [6,96,40,257,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257,130] 13 (by decide) (choices 1) [1,16,64,128] r31397 c31397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13957
  · exact u13958
  · exact u13959
  · exact u13960

def r31398 : Route 9 := (fun mask => (mask,id))

def c31398 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31398 : Upper (D 7) (R 7) [6,96,40,257,192] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257,192] 13 (by decide) (choices 1) [1,2,16,128] r31398 c31398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13961
  · exact u13962
  · exact u13963
  · exact u13964

def r31399 : Route 9 := (fun mask => (mask,id))

def c31399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31399 : Upper (D 7) (R 7) [6,96,40,258,65] 13 := by
  apply FastRouting.sound _ _ [6,96,40,258,65] 13 (by decide) (choices 1) [1,16,128] r31399 c31399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13965
  · exact u13966
  · exact u13967

def r31400 : Route 9 := (fun mask => (mask,id))

def c31400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31400 : Upper (D 7) (R 7) [6,96,40,258,129] 13 := by
  apply FastRouting.sound _ _ [6,96,40,258,129] 13 (by decide) (choices 1) [1,16,64,128] r31400 c31400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13968
  · exact u13969
  · exact u13970
  · exact u13971

def r31401 : Route 9 := (fun mask => (mask,id))

def c31401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31401 : Upper (D 7) (R 7) [6,96,40,258,192] 13 := by
  apply FastRouting.sound _ _ [6,96,40,258,192] 13 (by decide) (choices 1) [1,16,128] r31401 c31401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13972
  · exact u13973
  · exact u13974

def b31402 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 98 44 280 19 225 193 193 449), lower := (rows 7 98 44 280 19 32 64 128 256), losses := [] }

theorem u31402 : Upper (D 7) (R 7) [6,96,40,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31403 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5)], upper := (rows 7 98 44 280 81 163 195 131 387), lower := (rows 7 98 44 280 81 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 33 0 129 257), good := (rows 423 34 44 284 445 32 0 128 256) }] }

theorem u31403 : Upper (D 7) (R 7) [6,96,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31404 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 44 280 82 161 193 129 385), lower := (rows 7 98 44 280 82 32 64 128 256), losses := [] }

theorem u31404 : Upper (D 7) (R 7) [6,96,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31405 : Route 9 := (fun mask => (mask,id))

def c31405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31405 : Upper (D 7) (R 7) [6,96,40,272,129] 13 := by
  apply FastRouting.sound _ _ [6,96,40,272,129] 13 (by decide) (choices 1) [1,2,64,128] r31405 c31405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13975
  · exact u13976
  · exact u13977
  · exact u13978

def r31406 : Route 9 := (fun mask => (mask,id))

def c31406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31406 : Upper (D 7) (R 7) [6,96,40,272,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,272,130] 13 (by decide) (choices 1) [1,64,128] r31406 c31406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13979
  · exact u13980
  · exact u13981

def r31407 : Route 9 := (fun mask => (mask,id))

def c31407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31407 : Upper (D 7) (R 7) [6,96,40,272,192] 13 := by
  apply FastRouting.sound _ _ [6,96,40,272,192] 13 (by decide) (choices 1) [1,2,128] r31407 c31407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13982
  · exact u13983
  · exact u13984

def b31408 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(4,5)], upper := (rows 7 98 44 328 19 177 209 145 401), lower := (rows 7 98 44 328 19 32 64 128 256), losses := [] }

theorem u31408 : Upper (D 7) (R 7) [6,96,40,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31409 : Route 9 := (fun mask => (mask,id))

def c31409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31409 : Upper (D 7) (R 7) [6,96,40,320,129] 13 := by
  apply FastRouting.sound _ _ [6,96,40,320,129] 13 (by decide) (choices 1) [1,2,16,128] r31409 c31409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13985
  · exact u13986
  · exact u13987
  · exact u13988

def r31410 : Route 9 := (fun mask => (mask,id))

def c31410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31410 : Upper (D 7) (R 7) [6,96,40,320,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,320,130] 13 (by decide) (choices 1) [1,16,128] r31410 c31410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13989
  · exact u13990
  · exact u13991

def b31411 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 98 44 392 19 241 209 209 465), lower := (rows 7 98 44 392 19 32 64 128 256), losses := [] }

theorem u31411 : Upper (D 7) (R 7) [6,96,40,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31412 : Route 9 := (fun mask => (mask,id))

def c31412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31412 : Upper (D 7) (R 7) [6,96,40,384,65] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,65] 13 (by decide) (choices 1) [1,2,16,128] r31412 c31412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13992
  · exact u13993
  · exact u13994
  · exact u13995

def b31413 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 44 392 82 177 209 145 401), lower := (rows 7 98 44 392 82 32 64 128 256), losses := [] }

theorem u31413 : Upper (D 7) (R 7) [6,96,40,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31414 : Route 9 := (fun mask => (mask,id))

def c31414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31414 : Upper (D 7) (R 7) [6,96,40,384,129] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,129] 13 (by decide) (choices 1) [1,2,16,64] r31414 c31414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13996
  · exact u13997
  · exact u13998
  · exact u13999

def r31415 : Route 9 := (fun mask => (mask,id))

def c31415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31415 : Upper (D 7) (R 7) [6,96,40,384,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,130] 13 (by decide) (choices 1) [1,16,64] r31415 c31415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14000
  · exact u14001
  · exact u14002

def r31416 : Route 9 := (fun mask => (mask,id))

def c31416 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31416 : Upper (D 7) (R 7) [6,96,40,384,192] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,192] 13 (by decide) (choices 1) [1,2,16] r31416 c31416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14003
  · exact u14004
  · exact u14005

def b31417 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 133 11 56 496 464 464 464), lower := (rows 7 98 133 11 56 32 64 128 256), losses := [] }

theorem u31417 : Upper (D 7) (R 7) [6,96,129,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31418 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 133 11 152 368 368 496 368), lower := (rows 7 98 133 11 152 32 64 128 256), losses := [] }

theorem u31418 : Upper (D 7) (R 7) [6,96,129,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31419 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 133 11 176 376 344 472 344), lower := (rows 7 98 133 11 176 32 64 128 256), losses := [] }

theorem u31419 : Upper (D 7) (R 7) [6,96,129,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31420 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 133 11 280 240 240 240 496), lower := (rows 7 98 133 11 280 32 64 128 256), losses := [] }

theorem u31420 : Upper (D 7) (R 7) [6,96,129,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31421 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 133 11 304 248 216 216 472), lower := (rows 7 98 133 11 304 32 64 128 256), losses := [] }

theorem u31421 : Upper (D 7) (R 7) [6,96,129,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31422 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 133 11 400 120 120 248 376), lower := (rows 7 98 133 11 400 32 64 128 256), losses := [] }

theorem u31422 : Upper (D 7) (R 7) [6,96,129,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31423 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 133 25 26 480 480 480 480), lower := (rows 7 98 133 25 26 32 64 128 256), losses := [] }

theorem u31423 : Upper (D 7) (R 7) [6,96,129,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31424 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 133 25 50 488 456 456 456), lower := (rows 7 98 133 25 50 32 64 128 256), losses := [] }

theorem u31424 : Upper (D 7) (R 7) [6,96,129,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31425 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,0)], upper := (rows 7 98 133 25 56 482 450 450 450), lower := (rows 7 98 133 25 56 32 64 128 256), losses := [] }

theorem u31425 : Upper (D 7) (R 7) [6,96,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31426 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 133 25 112 426 458 394 394), lower := (rows 7 98 133 25 112 32 64 128 256), losses := [] }

theorem u31426 : Upper (D 7) (R 7) [6,96,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31427 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 133 25 146 360 360 488 360), lower := (rows 7 98 133 25 146 32 64 128 256), losses := [] }

theorem u31427 : Upper (D 7) (R 7) [6,96,129,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31428 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 7 98 133 25 152 354 354 482 354), lower := (rows 7 98 133 25 152 32 64 128 256), losses := [] }

theorem u31428 : Upper (D 7) (R 7) [6,96,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31429 : Route 9 := (fun mask => (mask,id))

def c31429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31429 : Upper (D 7) (R 7) [6,96,129,17,160] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,160] 13 (by decide) (choices 1) [2,8,64,256] r31429 c31429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14006
  · exact u14007
  · exact u14008
  · exact u14009

def r31430 : Route 9 := (fun mask => (mask,id))

def c31430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31430 : Upper (D 7) (R 7) [6,96,129,17,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,258] 13 (by decide) (choices 1) [8,64,128] r31430 c31430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14010
  · exact u14011
  · exact u14012

def r31431 : Route 9 := (fun mask => (mask,id))

def c31431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31431 : Upper (D 7) (R 7) [6,96,129,17,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,264] 13 (by decide) (choices 1) [2,64,128] r31431 c31431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14013
  · exact u14014
  · exact u14015

def r31432 : Route 9 := (fun mask => (mask,id))

def c31432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31432 : Upper (D 7) (R 7) [6,96,129,17,288] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,288] 13 (by decide) (choices 1) [2,8,64,128] r31432 c31432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14016
  · exact u14017
  · exact u14018
  · exact u14019

def r31433 : Route 9 := (fun mask => (mask,id))

def c31433 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31433 : Upper (D 7) (R 7) [6,96,129,17,384] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,384] 13 (by decide) (choices 1) [2,8,64] r31433 c31433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14020
  · exact u14021
  · exact u14022

def b31434 : PairBound 9 := { available := 456, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 4, region := 458, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,0)], upper := (rows 7 98 133 26 49 488 456 456 456), lower := (rows 7 98 133 26 49 32 64 128 256), losses := [] }

theorem u31434 : Upper (D 7) (R 7) [6,96,129,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31435 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 7 98 133 26 56 481 449 449 449), lower := (rows 7 98 133 26 56 32 64 128 256), losses := [] }

theorem u31435 : Upper (D 7) (R 7) [6,96,129,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31436 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 133 26 112 425 457 393 393), lower := (rows 7 98 133 26 112 32 64 128 256), losses := [] }

theorem u31436 : Upper (D 7) (R 7) [6,96,129,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31437 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 7 98 133 26 145 360 360 488 360), lower := (rows 7 98 133 26 145 32 64 128 256), losses := [] }

theorem u31437 : Upper (D 7) (R 7) [6,96,129,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31438 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,0)], upper := (rows 7 98 133 26 152 353 353 481 353), lower := (rows 7 98 133 26 152 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 32 64 128 256), good := (rows 30 98 156 26 152 32 64 128 256) }] }

theorem u31438 : Upper (D 7) (R 7) [6,96,129,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31439 : Route 9 := (fun mask => (mask,id))

def c31439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31439 : Upper (D 7) (R 7) [6,96,129,18,160] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,160] 13 (by decide) (choices 1) [1,8,64,256] r31439 c31439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14023
  · exact u14024
  · exact u14025
  · exact u14026

#print axioms u31439
end Delivery.IrregularNine14.P07
