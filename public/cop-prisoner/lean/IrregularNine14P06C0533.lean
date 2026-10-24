import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0238
import IrregularNine14P06C0239

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31980 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 265 52 102 70 198 326), lower := (rows 11 50 133 265 52 32 64 128 256), losses := [] }

theorem u31980 : Upper (D 6) (R 6) [10,48,129,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31981 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 265 82 100 100 228 356), lower := (rows 11 50 133 265 82 32 64 128 256), losses := [] }

theorem u31981 : Upper (D 6) (R 6) [10,48,129,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31982 : Route 9 := (fun mask => (mask,id))

def c31982 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31982 : Upper (D 6) (R 6) [10,48,129,257,68] 13 := by
  apply FastRouting.sound _ _ [10,48,129,257,68] 13 (by decide) (choices 1) [2,4,64] r31982 c31982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14296
  · exact u14297
  · exact u14298

def b31983 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 265 112 102 70 198 326), lower := (rows 11 50 133 265 112 32 64 128 256), losses := [] }

theorem u31983 : Upper (D 6) (R 6) [10,48,129,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31984 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 133 268 19 100 100 228 356), lower := (rows 11 50 133 268 19 32 64 128 256), losses := [] }

theorem u31984 : Upper (D 6) (R 6) [10,48,129,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31985 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 133 268 21 98 98 226 354), lower := (rows 11 50 133 268 21 32 64 128 256), losses := [] }

theorem u31985 : Upper (D 6) (R 6) [10,48,129,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31986 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 50 133 268 22 97 97 225 353), lower := (rows 11 50 133 268 22 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 69 133 261), good := (rows 491 50 481 488 498 32 64 128 256) }] }

theorem u31986 : Upper (D 6) (R 6) [10,48,129,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31987 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 268 49 102 70 198 326), lower := (rows 11 50 133 268 49 32 64 128 256), losses := [] }

theorem u31987 : Upper (D 6) (R 6) [10,48,129,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31988 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 268 50 101 69 197 325), lower := (rows 11 50 133 268 50 32 64 128 256), losses := [] }

theorem u31988 : Upper (D 6) (R 6) [10,48,129,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31989 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 268 52 99 67 195 323), lower := (rows 11 50 133 268 52 32 64 128 256), losses := [] }

theorem u31989 : Upper (D 6) (R 6) [10,48,129,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31990 : Route 9 := (fun mask => (mask,id))

def c31990 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31990 : Upper (D 6) (R 6) [10,48,129,260,65] 13 := by
  apply FastRouting.sound _ _ [10,48,129,260,65] 13 (by decide) (choices 1) [2,4,64] r31990 c31990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14299
  · exact u14300
  · exact u14301

def r31991 : Route 9 := (fun mask => (mask,id))

def c31991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31991 : Upper (D 6) (R 6) [10,48,129,260,66] 13 := by
  apply FastRouting.sound _ _ [10,48,129,260,66] 13 (by decide) (choices 1) [1,4,64] r31991 c31991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14302
  · exact u14303
  · exact u14304

def r31992 : Route 9 := (fun mask => (mask,id))

def c31992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31992 : Upper (D 6) (R 6) [10,48,129,260,68] 13 := by
  apply FastRouting.sound _ _ [10,48,129,260,68] 13 (by decide) (choices 1) [1,2,64] r31992 c31992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14305
  · exact u14306
  · exact u14307

def b31993 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 268 112 103 71 199 327), lower := (rows 11 50 133 268 112 32 64 128 256), losses := [] }

theorem u31993 : Upper (D 6) (R 6) [10,48,129,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31994 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 133 296 19 100 68 196 324), lower := (rows 11 50 133 296 19 32 64 128 256), losses := [] }

theorem u31994 : Upper (D 6) (R 6) [10,48,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31995 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 133 296 21 102 70 198 326), lower := (rows 11 50 133 296 21 32 64 128 256), losses := [] }

theorem u31995 : Upper (D 6) (R 6) [10,48,129,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31996 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 133 296 22 101 69 197 325), lower := (rows 11 50 133 296 22 32 64 128 256), losses := [] }

theorem u31996 : Upper (D 6) (R 6) [10,48,129,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31997 : Route 9 := (fun mask => (mask,id))

def c31997 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31997 : Upper (D 6) (R 6) [10,48,129,288,65] 13 := by
  apply FastRouting.sound _ _ [10,48,129,288,65] 13 (by decide) (choices 1) [2,4,64] r31997 c31997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14308
  · exact u14309
  · exact u14310

def b31998 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 133 296 82 101 69 197 325), lower := (rows 11 50 133 296 82 32 64 128 256), losses := [] }

theorem u31998 : Upper (D 6) (R 6) [10,48,129,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31999 : Route 9 := (fun mask => (mask,id))

def c31999 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31999 : Upper (D 6) (R 6) [10,48,129,288,68] 13 := by
  apply FastRouting.sound _ _ [10,48,129,288,68] 13 (by decide) (choices 1) [1,2,4,64] r31999 c31999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14311
  · exact u14312
  · exact u14313
  · exact u14314

def b32000 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 133 328 19 100 100 228 356), lower := (rows 11 50 133 328 19 32 64 128 256), losses := [] }

theorem u32000 : Upper (D 6) (R 6) [10,48,129,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32001 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 133 328 21 102 102 230 358), lower := (rows 11 50 133 328 21 32 64 128 256), losses := [] }

theorem u32001 : Upper (D 6) (R 6) [10,48,129,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32002 : Route 9 := (fun mask => (mask,id))

def c32002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32002 : Upper (D 6) (R 6) [10,48,129,320,6] 13 := by
  apply FastRouting.sound _ _ [10,48,129,320,6] 13 (by decide) (choices 1) [1,4,64] r32002 c32002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14315
  · exact u14316
  · exact u14317

def b32003 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 328 49 102 70 198 326), lower := (rows 11 50 133 328 49 32 64 128 256), losses := [] }

theorem u32003 : Upper (D 6) (R 6) [10,48,129,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32004 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 328 50 101 69 197 325), lower := (rows 11 50 133 328 50 32 64 128 256), losses := [] }

theorem u32004 : Upper (D 6) (R 6) [10,48,129,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32005 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 328 52 103 71 199 327), lower := (rows 11 50 133 328 52 32 64 128 256), losses := [] }

theorem u32005 : Upper (D 6) (R 6) [10,48,129,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32006 : Route 9 := (fun mask => (mask,id))

def c32006 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32006 : Upper (D 6) (R 6) [10,48,129,320,65] 13 := by
  apply FastRouting.sound _ _ [10,48,129,320,65] 13 (by decide) (choices 1) [2,4] r32006 c32006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14318
  · exact u14319

def b32007 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 164, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 50 133 328 82 37 101 165 293), lower := (rows 11 50 133 328 82 32 64 128 256), losses := [] }

theorem u32007 : Upper (D 6) (R 6) [10,48,129,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32008 : Route 9 := (fun mask => (mask,id))

def c32008 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32008 : Upper (D 6) (R 6) [10,48,129,320,68] 13 := by
  apply FastRouting.sound _ _ [10,48,129,320,68] 13 (by decide) (choices 1) [1,2,4] r32008 c32008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14320
  · exact u14321
  · exact u14322

def b32009 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 328 112 39 71 135 263), lower := (rows 11 50 133 328 112 32 64 128 256), losses := [] }

theorem u32009 : Upper (D 6) (R 6) [10,48,129,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32010 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 134 44 21 353 321 449 321), lower := (rows 11 50 134 44 21 32 64 128 256), losses := [] }

theorem u32010 : Upper (D 6) (R 6) [10,48,130,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32011 : Route 9 := (fun mask => (mask,id))

def c32011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32011 : Upper (D 6) (R 6) [10,48,130,36,65] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36,65] 13 (by decide) (choices 1) [1,4,64,256] r32011 c32011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14323
  · exact u14324
  · exact u14325
  · exact u14326

def r32012 : Route 9 := (fun mask => (mask,id))

def c32012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32012 : Upper (D 6) (R 6) [10,48,130,36,68] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36,68] 13 (by decide) (choices 1) [1,64,256] r32012 c32012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14327
  · exact u14328
  · exact u14329

def r32013 : Route 9 := (fun mask => (mask,id))

def c32013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32013 : Upper (D 6) (R 6) [10,48,130,36,257] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36,257] 13 (by decide) (choices 1) [1,4,64] r32013 c32013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14330
  · exact u14331
  · exact u14332

def r32014 : Route 9 := (fun mask => (mask,id))

def c32014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32014 : Upper (D 6) (R 6) [10,48,130,36,260] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36,260] 13 (by decide) (choices 1) [1,64] r32014 c32014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14333
  · exact u14334

def r32015 : Route 9 := (fun mask => (mask,id))

def c32015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32015 : Upper (D 6) (R 6) [10,48,130,36,320] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36,320] 13 (by decide) (choices 1) [1,4,64] r32015 c32015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14335
  · exact u14336
  · exact u14337

def b32016 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 50 134 73 21 356 356 484 356), lower := (rows 11 50 134 73 21 32 64 128 256), losses := [] }

theorem u32016 : Upper (D 6) (R 6) [10,48,130,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32017 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 73 49 356 324 452 324), lower := (rows 11 50 134 73 49 32 64 128 256), losses := [] }

theorem u32017 : Upper (D 6) (R 6) [10,48,130,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32018 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 73 52 357 325 453 325), lower := (rows 11 50 134 73 52 32 64 128 256), losses := [] }

theorem u32018 : Upper (D 6) (R 6) [10,48,130,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32019 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 50 134 73 81 292 356 420 292), lower := (rows 11 50 134 73 81 32 64 128 256), losses := [] }

theorem u32019 : Upper (D 6) (R 6) [10,48,130,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32020 : Route 9 := (fun mask => (mask,id))

def c32020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32020 : Upper (D 6) (R 6) [10,48,130,65,68] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65,68] 13 (by decide) (choices 1) [1,4,256] r32020 c32020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14338
  · exact u14339
  · exact u14340

def b32021 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 73 112 293 325 389 261), lower := (rows 11 50 134 73 112 32 64 128 256), losses := [] }

theorem u32021 : Upper (D 6) (R 6) [10,48,130,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32022 : Route 9 := (fun mask => (mask,id))

def c32022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32022 : Upper (D 6) (R 6) [10,48,130,65,257] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65,257] 13 (by decide) (choices 1) [4,64] r32022 c32022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14341
  · exact u14342

def r32023 : Route 9 := (fun mask => (mask,id))

def c32023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32023 : Upper (D 6) (R 6) [10,48,130,65,260] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65,260] 13 (by decide) (choices 1) [1,4,64] r32023 c32023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14343
  · exact u14344
  · exact u14345

def b32024 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 73 304 101 69 197 325), lower := (rows 11 50 134 73 304 32 64 128 256), losses := [] }

theorem u32024 : Upper (D 6) (R 6) [10,48,130,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32025 : Route 9 := (fun mask => (mask,id))

def c32025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32025 : Upper (D 6) (R 6) [10,48,130,65,320] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65,320] 13 (by decide) (choices 1) [1,4] r32025 c32025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14346
  · exact u14347

def r32026 : Route 9 := (fun mask => (mask,id))

def c32026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32026 : Upper (D 6) (R 6) [10,48,130,68,5] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,5] 13 (by decide) (choices 1) [1,64,256] r32026 c32026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14348
  · exact u14349
  · exact u14350

def b32027 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 76 49 357 325 453 325), lower := (rows 11 50 134 76 49 32 64 128 256), losses := [] }

theorem u32027 : Upper (D 6) (R 6) [10,48,130,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32028 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 76 52 353 321 449 321), lower := (rows 11 50 134 76 52 32 64 128 256), losses := [] }

theorem u32028 : Upper (D 6) (R 6) [10,48,130,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32029 : Route 9 := (fun mask => (mask,id))

def c32029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32029 : Upper (D 6) (R 6) [10,48,130,68,65] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,65] 13 (by decide) (choices 1) [1,4,256] r32029 c32029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14351
  · exact u14352
  · exact u14353

def b32030 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 134 76 84 289 353 417 289), lower := (rows 11 50 134 76 84 32 64 128 256), losses := [] }

theorem u32030 : Upper (D 6) (R 6) [10,48,130,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32031 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 76 112 293 325 389 261), lower := (rows 11 50 134 76 112 32 64 128 256), losses := [] }

theorem u32031 : Upper (D 6) (R 6) [10,48,130,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32032 : Route 9 := (fun mask => (mask,id))

def c32032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32032 : Upper (D 6) (R 6) [10,48,130,68,257] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,257] 13 (by decide) (choices 1) [1,4,64] r32032 c32032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14354
  · exact u14355
  · exact u14356

def r32033 : Route 9 := (fun mask => (mask,id))

def c32033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32033 : Upper (D 6) (R 6) [10,48,130,68,260] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,260] 13 (by decide) (choices 1) [1,64] r32033 c32033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14357
  · exact u14358

def b32034 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 76 304 101 69 197 325), lower := (rows 11 50 134 76 304 32 64 128 256), losses := [] }

theorem u32034 : Upper (D 6) (R 6) [10,48,130,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32035 : Route 9 := (fun mask => (mask,id))

def c32035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32035 : Upper (D 6) (R 6) [10,48,130,68,320] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,320] 13 (by decide) (choices 1) [1,4] r32035 c32035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14359
  · exact u14360

def b32036 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 134 104 21 357 325 453 325), lower := (rows 11 50 134 104 21 32 64 128 256), losses := [] }

theorem u32036 : Upper (D 6) (R 6) [10,48,130,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32037 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 104 81 293 325 389 261), lower := (rows 11 50 134 104 81 32 64 128 256), losses := [] }

theorem u32037 : Upper (D 6) (R 6) [10,48,130,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32038 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 134 104 84 293 325 389 261), lower := (rows 11 50 134 104 84 32 64 128 256), losses := [] }

theorem u32038 : Upper (D 6) (R 6) [10,48,130,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32039 : Route 9 := (fun mask => (mask,id))

def c32039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32039 : Upper (D 6) (R 6) [10,48,130,96,257] 13 := by
  apply FastRouting.sound _ _ [10,48,130,96,257] 13 (by decide) (choices 1) [1,4,64] r32039 c32039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14361
  · exact u14362
  · exact u14363

#print axioms u32039
end Delivery.IrregularNine14.P06
