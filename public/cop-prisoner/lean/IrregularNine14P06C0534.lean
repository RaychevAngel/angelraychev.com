import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0239
import IrregularNine14P06C0240
import IrregularNine14P06C0241

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32040 : Route 9 := (fun mask => (mask,id))

def c32040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32040 : Upper (D 6) (R 6) [10,48,130,96,260] 13 := by
  apply FastRouting.sound _ _ [10,48,130,96,260] 13 (by decide) (choices 1) [1,4,64] r32040 c32040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14364
  · exact u14365
  · exact u14366

def b32041 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 134 104 336 37 69 133 261), lower := (rows 11 50 134 104 336 32 64 128 256), losses := [] }

theorem u32041 : Upper (D 6) (R 6) [10,48,130,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32042 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 50 134 265 21 100 100 228 356), lower := (rows 11 50 134 265 21 32 64 128 256), losses := [] }

theorem u32042 : Upper (D 6) (R 6) [10,48,130,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32043 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 265 49 100 68 196 324), lower := (rows 11 50 134 265 49 32 64 128 256), losses := [] }

theorem u32043 : Upper (D 6) (R 6) [10,48,130,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32044 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 265 52 101 69 197 325), lower := (rows 11 50 134 265 52 32 64 128 256), losses := [] }

theorem u32044 : Upper (D 6) (R 6) [10,48,130,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32045 : Route 9 := (fun mask => (mask,id))

def c32045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32045 : Upper (D 6) (R 6) [10,48,130,257,65] 13 := by
  apply FastRouting.sound _ _ [10,48,130,257,65] 13 (by decide) (choices 1) [4,64] r32045 c32045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14367
  · exact u14368

def r32046 : Route 9 := (fun mask => (mask,id))

def c32046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32046 : Upper (D 6) (R 6) [10,48,130,257,68] 13 := by
  apply FastRouting.sound _ _ [10,48,130,257,68] 13 (by decide) (choices 1) [1,4,64] r32046 c32046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14369
  · exact u14370
  · exact u14371

def b32047 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 265 112 101 69 197 325), lower := (rows 11 50 134 265 112 32 64 128 256), losses := [] }

theorem u32047 : Upper (D 6) (R 6) [10,48,130,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32048 : Route 9 := (fun mask => (mask,id))

def c32048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32048 : Upper (D 6) (R 6) [10,48,130,260,5] 13 := by
  apply FastRouting.sound _ _ [10,48,130,260,5] 13 (by decide) (choices 1) [1,64] r32048 c32048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14372
  · exact u14373

def b32049 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 268 49 101 69 197 325), lower := (rows 11 50 134 268 49 32 64 128 256), losses := [] }

theorem u32049 : Upper (D 6) (R 6) [10,48,130,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32050 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 268 52 97 65 193 321), lower := (rows 11 50 134 268 52 32 64 128 256), losses := [] }

theorem u32050 : Upper (D 6) (R 6) [10,48,130,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32051 : Route 9 := (fun mask => (mask,id))

def c32051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32051 : Upper (D 6) (R 6) [10,48,130,260,65] 13 := by
  apply FastRouting.sound _ _ [10,48,130,260,65] 13 (by decide) (choices 1) [1,4,64] r32051 c32051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14374
  · exact u14375
  · exact u14376

def r32052 : Route 9 := (fun mask => (mask,id))

def c32052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32052 : Upper (D 6) (R 6) [10,48,130,260,68] 13 := by
  apply FastRouting.sound _ _ [10,48,130,260,68] 13 (by decide) (choices 1) [1,64] r32052 c32052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14377
  · exact u14378

def b32053 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 268 112 101 69 197 325), lower := (rows 11 50 134 268 112 32 64 128 256), losses := [] }

theorem u32053 : Upper (D 6) (R 6) [10,48,130,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32054 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 134 296 21 101 69 197 325), lower := (rows 11 50 134 296 21 32 64 128 256), losses := [] }

theorem u32054 : Upper (D 6) (R 6) [10,48,130,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32055 : Route 9 := (fun mask => (mask,id))

def c32055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32055 : Upper (D 6) (R 6) [10,48,130,288,65] 13 := by
  apply FastRouting.sound _ _ [10,48,130,288,65] 13 (by decide) (choices 1) [1,4,64] r32055 c32055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14379
  · exact u14380
  · exact u14381

def r32056 : Route 9 := (fun mask => (mask,id))

def c32056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32056 : Upper (D 6) (R 6) [10,48,130,288,68] 13 := by
  apply FastRouting.sound _ _ [10,48,130,288,68] 13 (by decide) (choices 1) [1,4,64] r32056 c32056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14382
  · exact u14383
  · exact u14384

def r32057 : Route 9 := (fun mask => (mask,id))

def c32057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32057 : Upper (D 6) (R 6) [10,48,130,320,5] 13 := by
  apply FastRouting.sound _ _ [10,48,130,320,5] 13 (by decide) (choices 1) [1,4,64] r32057 c32057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14385
  · exact u14386
  · exact u14387

def b32058 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 328 49 101 69 197 325), lower := (rows 11 50 134 328 49 32 64 128 256), losses := [] }

theorem u32058 : Upper (D 6) (R 6) [10,48,130,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32059 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 328 52 101 69 197 325), lower := (rows 11 50 134 328 52 32 64 128 256), losses := [] }

theorem u32059 : Upper (D 6) (R 6) [10,48,130,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32060 : Route 9 := (fun mask => (mask,id))

def c32060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32060 : Upper (D 6) (R 6) [10,48,130,320,65] 13 := by
  apply FastRouting.sound _ _ [10,48,130,320,65] 13 (by decide) (choices 1) [1,4] r32060 c32060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14388
  · exact u14389

def r32061 : Route 9 := (fun mask => (mask,id))

def c32061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32061 : Upper (D 6) (R 6) [10,48,130,320,68] 13 := by
  apply FastRouting.sound _ _ [10,48,130,320,68] 13 (by decide) (choices 1) [1,4] r32061 c32061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14390
  · exact u14391

def b32062 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 134 328 112 37 69 133 261), lower := (rows 11 50 134 328 112 32 64 128 256), losses := [] }

theorem u32062 : Upper (D 6) (R 6) [10,48,130,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32063 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 164 13 19 356 324 452 324), lower := (rows 11 50 164 13 19 32 64 128 256), losses := [] }

theorem u32063 : Upper (D 6) (R 6) [10,48,160,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32064 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 164 13 21 354 322 450 322), lower := (rows 11 50 164 13 21 32 64 128 256), losses := [] }

theorem u32064 : Upper (D 6) (R 6) [10,48,160,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32065 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 164 13 22 353 321 449 321), lower := (rows 11 50 164 13 22 32 64 128 256), losses := [] }

theorem u32065 : Upper (D 6) (R 6) [10,48,160,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32066 : Route 9 := (fun mask => (mask,id))

def c32066 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32066 : Upper (D 6) (R 6) [10,48,160,5,65] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5,65] 13 (by decide) (choices 1) [2,4,64,256] r32066 c32066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14392
  · exact u14393
  · exact u14394
  · exact u14395

def b32067 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 11 50 164 13 82 357 325 453 325), lower := (rows 11 50 164 13 82 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 72 136 264), good := (rows 475 18 132 477 82 0 64 128 256) }] }

theorem u32067 : Upper (D 6) (R 6) [10,48,160,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32068 : Route 9 := (fun mask => (mask,id))

def c32068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32068 : Upper (D 6) (R 6) [10,48,160,5,68] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5,68] 13 (by decide) (choices 1) [1,2,64,256] r32068 c32068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14396
  · exact u14397
  · exact u14398
  · exact u14399

def r32069 : Route 9 := (fun mask => (mask,id))

def c32069 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32069 : Upper (D 6) (R 6) [10,48,160,5,257] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5,257] 13 (by decide) (choices 1) [2,4,64] r32069 c32069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14400
  · exact u14401
  · exact u14402

def b32070 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 11 50 164 13 274 101 69 197 325), lower := (rows 11 50 164 13 274 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 72 136 264), good := (rows 475 18 132 477 274 0 64 128 256) }] }

theorem u32070 : Upper (D 6) (R 6) [10,48,160,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32071 : Route 9 := (fun mask => (mask,id))

def c32071 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32071 : Upper (D 6) (R 6) [10,48,160,5,260] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5,260] 13 (by decide) (choices 1) [1,2,64] r32071 c32071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14403
  · exact u14404
  · exact u14405

def r32072 : Route 9 := (fun mask => (mask,id))

def c32072 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32072 : Upper (D 6) (R 6) [10,48,160,5,320] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5,320] 13 (by decide) (choices 1) [1,2,4,64] r32072 c32072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14406
  · exact u14407
  · exact u14408
  · exact u14409

def b32073 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 164 73 19 356 324 452 324), lower := (rows 11 50 164 73 19 32 64 128 256), losses := [] }

theorem u32073 : Upper (D 6) (R 6) [10,48,160,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32074 : Route 9 := (fun mask => (mask,id))

def c32074 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32074 : Upper (D 6) (R 6) [10,48,160,65,5] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,5] 13 (by decide) (choices 1) [2,4,64,256] r32074 c32074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14410
  · exact u14411
  · exact u14412
  · exact u14413

def b32075 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 164 73 22 357 325 453 325), lower := (rows 11 50 164 73 22 32 64 128 256), losses := [] }

theorem u32075 : Upper (D 6) (R 6) [10,48,160,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32076 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 50 164 73 81 294 326 390 262), lower := (rows 11 50 164 73 81 32 64 128 256), losses := [] }

theorem u32076 : Upper (D 6) (R 6) [10,48,160,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32077 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 164 73 82 293 325 389 261), lower := (rows 11 50 164 73 82 32 64 128 256), losses := [] }

theorem u32077 : Upper (D 6) (R 6) [10,48,160,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32078 : Route 9 := (fun mask => (mask,id))

def c32078 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32078 : Upper (D 6) (R 6) [10,48,160,65,68] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,68] 13 (by decide) (choices 1) [1,2,4,256] r32078 c32078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14414
  · exact u14415
  · exact u14416
  · exact u14417

def r32079 : Route 9 := (fun mask => (mask,id))

def c32079 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32079 : Upper (D 6) (R 6) [10,48,160,65,257] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,257] 13 (by decide) (choices 1) [2,4,64] r32079 c32079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14418
  · exact u14419
  · exact u14420

def r32080 : Route 9 := (fun mask => (mask,id))

def c32080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32080 : Upper (D 6) (R 6) [10,48,160,65,258] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,258] 13 (by decide) (choices 1) [1,4,64] r32080 c32080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14421
  · exact u14422
  · exact u14423

def r32081 : Route 9 := (fun mask => (mask,id))

def c32081 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32081 : Upper (D 6) (R 6) [10,48,160,65,260] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,260] 13 (by decide) (choices 1) [1,2,4,64] r32081 c32081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14424
  · exact u14425
  · exact u14426
  · exact u14427

def r32082 : Route 9 := (fun mask => (mask,id))

def c32082 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32082 : Upper (D 6) (R 6) [10,48,160,65,320] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65,320] 13 (by decide) (choices 1) [1,2,4] r32082 c32082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14428
  · exact u14429
  · exact u14430

def b32083 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 164 76 19 357 325 453 325), lower := (rows 11 50 164 76 19 32 64 128 256), losses := [] }

theorem u32083 : Upper (D 6) (R 6) [10,48,160,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32084 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 354, targets := 4 }], pairs := [(0,5),(1,2),(3,5)], upper := (rows 11 50 164 76 21 355 323 451 323), lower := (rows 11 50 164 76 21 32 64 128 256), losses := [{ target := 5, region := (rows 3 2 4 24 16 0 67 131 259), good := (rows 459 475 132 76 477 0 64 128 256) }] }

theorem u32084 : Upper (D 6) (R 6) [10,48,160,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32085 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 164 76 22 353 321 449 321), lower := (rows 11 50 164 76 22 32 64 128 256), losses := [] }

theorem u32085 : Upper (D 6) (R 6) [10,48,160,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32086 : Route 9 := (fun mask => (mask,id))

def c32086 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32086 : Upper (D 6) (R 6) [10,48,160,68,65] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,65] 13 (by decide) (choices 1) [1,2,4,256] r32086 c32086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14431
  · exact u14432
  · exact u14433
  · exact u14434

def b32087 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 50 164 76 82 293 325 389 261), lower := (rows 11 50 164 76 82 32 64 128 256), losses := [] }

theorem u32087 : Upper (D 6) (R 6) [10,48,160,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32088 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 164 76 84 291 323 387 259), lower := (rows 11 50 164 76 84 32 64 128 256), losses := [] }

theorem u32088 : Upper (D 6) (R 6) [10,48,160,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32089 : Route 9 := (fun mask => (mask,id))

def c32089 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32089 : Upper (D 6) (R 6) [10,48,160,68,257] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,257] 13 (by decide) (choices 1) [1,2,4,64] r32089 c32089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14435
  · exact u14436
  · exact u14437
  · exact u14438

def r32090 : Route 9 := (fun mask => (mask,id))

def c32090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32090 : Upper (D 6) (R 6) [10,48,160,68,258] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,258] 13 (by decide) (choices 1) [1,4,64] r32090 c32090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14439
  · exact u14440
  · exact u14441

def r32091 : Route 9 := (fun mask => (mask,id))

def c32091 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32091 : Upper (D 6) (R 6) [10,48,160,68,260] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,260] 13 (by decide) (choices 1) [1,2,64] r32091 c32091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14442
  · exact u14443
  · exact u14444

def r32092 : Route 9 := (fun mask => (mask,id))

def c32092 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32092 : Upper (D 6) (R 6) [10,48,160,68,320] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,320] 13 (by decide) (choices 1) [1,2,4] r32092 c32092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14445
  · exact u14446
  · exact u14447

def b32093 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 164 265 19 100 68 196 324), lower := (rows 11 50 164 265 19 32 64 128 256), losses := [] }

theorem u32093 : Upper (D 6) (R 6) [10,48,160,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32094 : Route 9 := (fun mask => (mask,id))

def c32094 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32094 : Upper (D 6) (R 6) [10,48,160,257,5] 13 := by
  apply FastRouting.sound _ _ [10,48,160,257,5] 13 (by decide) (choices 1) [2,4,64] r32094 c32094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14448
  · exact u14449
  · exact u14450

def b32095 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 164 265 22 101 69 197 325), lower := (rows 11 50 164 265 22 32 64 128 256), losses := [] }

theorem u32095 : Upper (D 6) (R 6) [10,48,160,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32096 : Route 9 := (fun mask => (mask,id))

def c32096 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32096 : Upper (D 6) (R 6) [10,48,160,257,65] 13 := by
  apply FastRouting.sound _ _ [10,48,160,257,65] 13 (by decide) (choices 1) [2,4,64] r32096 c32096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14451
  · exact u14452
  · exact u14453

def r32097 : Route 9 := (fun mask => (mask,id))

def c32097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32097 : Upper (D 6) (R 6) [10,48,160,257,66] 13 := by
  apply FastRouting.sound _ _ [10,48,160,257,66] 13 (by decide) (choices 1) [1,4,64] r32097 c32097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14454
  · exact u14455
  · exact u14456

def r32098 : Route 9 := (fun mask => (mask,id))

def c32098 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32098 : Upper (D 6) (R 6) [10,48,160,257,68] 13 := by
  apply FastRouting.sound _ _ [10,48,160,257,68] 13 (by decide) (choices 1) [1,2,4,64] r32098 c32098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14457
  · exact u14458
  · exact u14459
  · exact u14460

def b32099 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 164 268 19 101 69 197 325), lower := (rows 11 50 164 268 19 32 64 128 256), losses := [] }

theorem u32099 : Upper (D 6) (R 6) [10,48,160,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u32099
end Delivery.IrregularNine14.P06
