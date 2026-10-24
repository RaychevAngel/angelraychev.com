import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0198
import IrregularNine14P06C0199
import IrregularNine14P06C0200

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30420 : Route 9 := (fun mask => (mask,id))

def c30420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30420 : Upper (D 6) (R 6) [10,33,18,384,68] 13 := by
  apply FastRouting.sound _ _ [10,33,18,384,68] 13 (by decide) (choices 1) [1,4,64] r30420 c30420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11938
  · exact u11939
  · exact u11940

def r30421 : Route 9 := (fun mask => (mask,id))

def c30421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30421 : Upper (D 6) (R 6) [10,33,18,384,96] 13 := by
  apply FastRouting.sound _ _ [10,33,18,384,96] 13 (by decide) (choices 1) [1,4,64] r30421 c30421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11941
  · exact u11942
  · exact u11943

def b30422 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 1, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 52 73 22 484 452 452 452), lower := (rows 11 35 52 73 22 32 64 128 256), losses := [] }

theorem u30422 : Upper (D 6) (R 6) [10,33,48,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30423 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 52 73 82 420 452 388 388), lower := (rows 11 35 52 73 82 32 64 128 256), losses := [] }

theorem u30423 : Upper (D 6) (R 6) [10,33,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30424 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 52 73 84 422 454 390 390), lower := (rows 11 35 52 73 84 32 64 128 256), losses := [{ target := 2, region := (rows 21 6 0 24 16 32 64 128 256), good := (rows 11 35 59 73 91 32 64 128 256) }] }

theorem u30424 : Upper (D 6) (R 6) [10,33,48,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30425 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 73 146 356 324 452 324), lower := (rows 11 35 52 73 146 32 64 128 256), losses := [] }

theorem u30425 : Upper (D 6) (R 6) [10,33,48,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30426 : Route 9 := (fun mask => (mask,id))

def c30426 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30426 : Upper (D 6) (R 6) [10,33,48,65,132] 13 := by
  apply FastRouting.sound _ _ [10,33,48,65,132] 13 (by decide) (choices 1) [2,4,64,256] r30426 c30426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11944
  · exact u11945
  · exact u11946
  · exact u11947

def r30427 : Route 9 := (fun mask => (mask,id))

def c30427 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30427 : Upper (D 6) (R 6) [10,33,48,65,192] 13 := by
  apply FastRouting.sound _ _ [10,33,48,65,192] 13 (by decide) (choices 1) [2,4,256] r30427 c30427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11948
  · exact u11949
  · exact u11950

def r30428 : Route 9 := (fun mask => (mask,id))

def c30428 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30428 : Upper (D 6) (R 6) [10,33,48,65,384] 13 := by
  apply FastRouting.sound _ _ [10,33,48,65,384] 13 (by decide) (choices 1) [2,4,64] r30428 c30428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11951
  · exact u11952
  · exact u11953

def b30429 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 52 76 19 484 452 452 452), lower := (rows 11 35 52 76 19 32 64 128 256), losses := [] }

theorem u30429 : Upper (D 6) (R 6) [10,33,48,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30430 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 20, targets := 2 },{ cop := 1, region := 20, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 35 52 76 21 482 450 450 450), lower := (rows 11 35 52 76 21 32 64 128 256), losses := [] }

theorem u30430 : Upper (D 6) (R 6) [10,33,48,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30431 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 52 76 22 481 449 449 449), lower := (rows 11 35 52 76 22 32 64 128 256), losses := [] }

theorem u30431 : Upper (D 6) (R 6) [10,33,48,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30432 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 52 76 81 422 454 390 390), lower := (rows 11 35 52 76 81 32 64 128 256), losses := [] }

theorem u30432 : Upper (D 6) (R 6) [10,33,48,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30433 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c30433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30433 : Upper (D 6) (R 6) [10,33,48,68,66] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68,66] 13 (by decide) (choices 1) [1,4,128] r30433 c30433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11954
  · exact u11955
  · exact u11956

def b30434 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 52 76 84 419 451 387 387), lower := (rows 11 35 52 76 84 32 64 128 256), losses := [] }

theorem u30434 : Upper (D 6) (R 6) [10,33,48,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30435 : Route 9 := (fun mask => (mask,id))

def c30435 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30435 : Upper (D 6) (R 6) [10,33,48,68,129] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68,129] 13 (by decide) (choices 1) [2,4,64,256] r30435 c30435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11957
  · exact u11958
  · exact u11959
  · exact u11960

def r30436 : Route 9 := (fun mask => (mask,id))

def c30436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30436 : Upper (D 6) (R 6) [10,33,48,68,130] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68,130] 13 (by decide) (choices 1) [1,4,64,256] r30436 c30436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11961
  · exact u11962
  · exact u11963
  · exact u11964

def r30437 : Route 9 := (fun mask => (mask,id))

def c30437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30437 : Upper (D 6) (R 6) [10,33,48,68,132] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68,132] 13 (by decide) (choices 1) [1,2,64,256] r30437 c30437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11965
  · exact u11966
  · exact u11967
  · exact u11968

def r30438 : Route 9 := (fun mask => (mask,id))

def c30438 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30438 : Upper (D 6) (R 6) [10,33,48,68,192] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68,192] 13 (by decide) (choices 1) [1,2,4,256] r30438 c30438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11969
  · exact u11970
  · exact u11971
  · exact u11972

def r30439 : Route 9 := (fun mask => (mask,id))

def c30439 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30439 : Upper (D 6) (R 6) [10,33,48,68,384] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68,384] 13 (by decide) (choices 1) [1,2,4,64] r30439 c30439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11973
  · exact u11974
  · exact u11975
  · exact u11976

def b30440 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 1, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 52 137 22 356 324 452 324), lower := (rows 11 35 52 137 22 32 64 128 256), losses := [] }

theorem u30440 : Upper (D 6) (R 6) [10,33,48,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30441 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 137 82 356 324 452 324), lower := (rows 11 35 52 137 82 32 64 128 256), losses := [] }

theorem u30441 : Upper (D 6) (R 6) [10,33,48,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30442 : Route 9 := (fun mask => (mask,id))

def c30442 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30442 : Upper (D 6) (R 6) [10,33,48,129,68] 13 := by
  apply FastRouting.sound _ _ [10,33,48,129,68] 13 (by decide) (choices 1) [2,4,64,256] r30442 c30442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11977
  · exact u11978
  · exact u11979
  · exact u11980

def b30443 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 137 274 100 68 196 324), lower := (rows 11 35 52 137 274 32 64 128 256), losses := [] }

theorem u30443 : Upper (D 6) (R 6) [10,33,48,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30444 : Route 9 := (fun mask => (mask,id))

def c30444 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30444 : Upper (D 6) (R 6) [10,33,48,129,260] 13 := by
  apply FastRouting.sound _ _ [10,33,48,129,260] 13 (by decide) (choices 1) [2,4,64] r30444 c30444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11981
  · exact u11982
  · exact u11983

def r30445 : Route 9 := (fun mask => (mask,id))

def c30445 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30445 : Upper (D 6) (R 6) [10,33,48,129,320] 13 := by
  apply FastRouting.sound _ _ [10,33,48,129,320] 13 (by decide) (choices 1) [2,4,64] r30445 c30445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11984
  · exact u11985
  · exact u11986

def b30446 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 52 140 19 356 324 452 324), lower := (rows 11 35 52 140 19 32 64 128 256), losses := [] }

theorem u30446 : Upper (D 6) (R 6) [10,33,48,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30447 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 20, targets := 2 },{ cop := 1, region := 20, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 35 52 140 21 354 322 450 322), lower := (rows 11 35 52 140 21 32 64 128 256), losses := [] }

theorem u30447 : Upper (D 6) (R 6) [10,33,48,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30448 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 52 140 22 353 321 449 321), lower := (rows 11 35 52 140 22 32 64 128 256), losses := [] }

theorem u30448 : Upper (D 6) (R 6) [10,33,48,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30449 : Route 9 := (fun mask => (mask,id))

def c30449 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30449 : Upper (D 6) (R 6) [10,33,48,132,65] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,65] 13 (by decide) (choices 1) [2,4,64,256] r30449 c30449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11987
  · exact u11988
  · exact u11989
  · exact u11990

def r30450 : Route 9 := (fun mask => (mask,id))

def c30450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30450 : Upper (D 6) (R 6) [10,33,48,132,66] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,66] 13 (by decide) (choices 1) [1,4,64,256] r30450 c30450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11991
  · exact u11992
  · exact u11993
  · exact u11994

def r30451 : Route 9 := (fun mask => (mask,id))

def c30451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30451 : Upper (D 6) (R 6) [10,33,48,132,68] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,68] 13 (by decide) (choices 1) [1,2,64,256] r30451 c30451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11995
  · exact u11996
  · exact u11997
  · exact u11998

def r30452 : Route 9 := (fun mask => (mask,id))

def c30452 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30452 : Upper (D 6) (R 6) [10,33,48,132,257] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,257] 13 (by decide) (choices 1) [2,4,64] r30452 c30452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11999
  · exact u12000
  · exact u12001

def r30453 : Route 9 := (fun mask => (mask,id))

def c30453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30453 : Upper (D 6) (R 6) [10,33,48,132,258] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,258] 13 (by decide) (choices 1) [1,4,64] r30453 c30453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12002
  · exact u12003
  · exact u12004

def r30454 : Route 9 := (fun mask => (mask,id))

def c30454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30454 : Upper (D 6) (R 6) [10,33,48,132,260] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,260] 13 (by decide) (choices 1) [1,2,64] r30454 c30454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12005
  · exact u12006
  · exact u12007

def r30455 : Route 9 := (fun mask => (mask,id))

def c30455 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30455 : Upper (D 6) (R 6) [10,33,48,132,320] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,320] 13 (by decide) (choices 1) [1,2,4,64] r30455 c30455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12008
  · exact u12009
  · exact u12010
  · exact u12011

def b30456 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 52 200 19 356 324 452 324), lower := (rows 11 35 52 200 19 32 64 128 256), losses := [] }

theorem u30456 : Upper (D 6) (R 6) [10,33,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30457 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 20, targets := 2 },{ cop := 1, region := 20, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 35 52 200 21 358 326 454 326), lower := (rows 11 35 52 200 21 32 64 128 256), losses := [] }

theorem u30457 : Upper (D 6) (R 6) [10,33,48,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30458 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 52 200 22 357 325 453 325), lower := (rows 11 35 52 200 22 32 64 128 256), losses := [] }

theorem u30458 : Upper (D 6) (R 6) [10,33,48,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30459 : Route 9 := (fun mask => (mask,id))

def c30459 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30459 : Upper (D 6) (R 6) [10,33,48,192,65] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,65] 13 (by decide) (choices 1) [2,4,256] r30459 c30459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12012
  · exact u12013
  · exact u12014

def r30460 : Route 9 := (fun mask => (mask,id))

def c30460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30460 : Upper (D 6) (R 6) [10,33,48,192,66] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,66] 13 (by decide) (choices 1) [1,4,256] r30460 c30460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12015
  · exact u12016
  · exact u12017

def r30461 : Route 9 := (fun mask => (mask,id))

def c30461 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30461 : Upper (D 6) (R 6) [10,33,48,192,68] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,68] 13 (by decide) (choices 1) [1,2,4,256] r30461 c30461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12018
  · exact u12019
  · exact u12020
  · exact u12021

def r30462 : Route 9 := (fun mask => (mask,id))

def c30462 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30462 : Upper (D 6) (R 6) [10,33,48,192,257] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,257] 13 (by decide) (choices 1) [2,4,64] r30462 c30462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12022
  · exact u12023
  · exact u12024

def r30463 : Route 9 := (fun mask => (mask,id))

def c30463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30463 : Upper (D 6) (R 6) [10,33,48,192,258] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,258] 13 (by decide) (choices 1) [1,4,64] r30463 c30463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12025
  · exact u12026
  · exact u12027

def r30464 : Route 9 := (fun mask => (mask,id))

def c30464 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30464 : Upper (D 6) (R 6) [10,33,48,192,260] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,260] 13 (by decide) (choices 1) [1,2,4,64] r30464 c30464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12028
  · exact u12029
  · exact u12030
  · exact u12031

def r30465 : Route 9 := (fun mask => (mask,id))

def c30465 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30465 : Upper (D 6) (R 6) [10,33,48,192,320] 13 := by
  apply FastRouting.sound _ _ [10,33,48,192,320] 13 (by decide) (choices 1) [1,2,4] r30465 c30465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12032
  · exact u12033
  · exact u12034

def b30466 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 52 392 19 100 68 196 324), lower := (rows 11 35 52 392 19 32 64 128 256), losses := [] }

theorem u30466 : Upper (D 6) (R 6) [10,33,48,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30467 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 20, targets := 2 },{ cop := 1, region := 20, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 35 52 392 21 102 70 198 326), lower := (rows 11 35 52 392 21 32 64 128 256), losses := [] }

theorem u30467 : Upper (D 6) (R 6) [10,33,48,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30468 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 35 52 392 22 101 69 197 325), lower := (rows 11 35 52 392 22 32 64 128 256), losses := [] }

theorem u30468 : Upper (D 6) (R 6) [10,33,48,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30469 : Route 9 := (fun mask => (mask,id))

def c30469 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30469 : Upper (D 6) (R 6) [10,33,48,384,65] 13 := by
  apply FastRouting.sound _ _ [10,33,48,384,65] 13 (by decide) (choices 1) [2,4,64] r30469 c30469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12035
  · exact u12036
  · exact u12037

def r30470 : Route 9 := (fun mask => (mask,id))

def c30470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30470 : Upper (D 6) (R 6) [10,33,48,384,66] 13 := by
  apply FastRouting.sound _ _ [10,33,48,384,66] 13 (by decide) (choices 1) [1,4,64] r30470 c30470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12038
  · exact u12039
  · exact u12040

def r30471 : Route 9 := (fun mask => (mask,id))

def c30471 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30471 : Upper (D 6) (R 6) [10,33,48,384,68] 13 := by
  apply FastRouting.sound _ _ [10,33,48,384,68] 13 (by decide) (choices 1) [1,2,4,64] r30471 c30471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12041
  · exact u12042
  · exact u12043
  · exact u12044

def b30472 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 69 28 22 480 480 480 480), lower := (rows 11 35 69 28 22 32 64 128 256), losses := [] }

theorem u30472 : Upper (D 6) (R 6) [10,33,65,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30473 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 28 50 484 452 452 452), lower := (rows 11 35 69 28 50 32 64 128 256), losses := [] }

theorem u30473 : Upper (D 6) (R 6) [10,33,65,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30474 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 69 28 52 482 450 450 450), lower := (rows 11 35 69 28 52 32 64 128 256), losses := [] }

theorem u30474 : Upper (D 6) (R 6) [10,33,65,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30475 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 13, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 69 28 82 420 484 420 420), lower := (rows 11 35 69 28 82 32 64 128 256), losses := [] }

theorem u30475 : Upper (D 6) (R 6) [10,33,65,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30476 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 69 28 84 418 482 418 418), lower := (rows 11 35 69 28 84 32 64 128 256), losses := [] }

theorem u30476 : Upper (D 6) (R 6) [10,33,65,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30477 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 35 69 28 112 422 454 390 390), lower := (rows 11 35 69 28 112 32 64 128 256), losses := [] }

theorem u30477 : Upper (D 6) (R 6) [10,33,65,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30478 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 35 69 28 146 356 356 484 356), lower := (rows 11 35 69 28 146 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 44 76 140 268), good := (rows 506 50 508 508 146 32 64 128 256) }] }

theorem u30478 : Upper (D 6) (R 6) [10,33,65,20,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30479 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 69 28 148 354 354 482 354), lower := (rows 11 35 69 28 148 32 64 128 256), losses := [] }

theorem u30479 : Upper (D 6) (R 6) [10,33,65,20,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30479
end Delivery.IrregularNine14.P06
