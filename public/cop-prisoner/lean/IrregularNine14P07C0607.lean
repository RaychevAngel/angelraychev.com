import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0366
import IrregularNine14P07C0367
import IrregularNine14P07C0368

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36420 : Route 9 := (fun mask => (mask,id))

def c36420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36420 : Upper (D 7) (R 7) [34,320,40,129,132] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,132] 13 (by decide) (choices 1) [1,2,16,64] r36420 c36420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21983
  · exact u21984
  · exact u21985
  · exact u21986

def r36421 : Route 9 := (fun mask => (mask,id))

def c36421 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36421 : Upper (D 7) (R 7) [34,320,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,192] 13 (by decide) (choices 1) [1,2,4,16] r36421 c36421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21987
  · exact u21988
  · exact u21989
  · exact u21990

def r36422 : Route 9 := (fun mask => (mask,id))

def c36422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36422 : Upper (D 7) (R 7) [34,320,40,130,65] 13 := by
  apply FastRouting.sound _ _ [34,320,40,130,65] 13 (by decide) (choices 1) [1,4,16,128] r36422 c36422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21991
  · exact u21992
  · exact u21993
  · exact u21994

def r36423 : Route 9 := (fun mask => (mask,id))

def c36423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36423 : Upper (D 7) (R 7) [34,320,40,130,68] 13 := by
  apply FastRouting.sound _ _ [34,320,40,130,68] 13 (by decide) (choices 1) [1,16,128] r36423 c36423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21995
  · exact u21996
  · exact u21997

def r36424 : Route 9 := (fun mask => (mask,id))

def c36424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36424 : Upper (D 7) (R 7) [34,320,40,130,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,130,129] 13 (by decide) (choices 1) [1,4,16,64] r36424 c36424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21998
  · exact u21999
  · exact u22000
  · exact u22001

def r36425 : Route 9 := (fun mask => (mask,id))

def c36425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36425 : Upper (D 7) (R 7) [34,320,40,130,132] 13 := by
  apply FastRouting.sound _ _ [34,320,40,130,132] 13 (by decide) (choices 1) [1,16,64] r36425 c36425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22002
  · exact u22003
  · exact u22004

def r36426 : Route 9 := (fun mask => (mask,id))

def c36426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36426 : Upper (D 7) (R 7) [34,320,40,130,192] 13 := by
  apply FastRouting.sound _ _ [34,320,40,130,192] 13 (by decide) (choices 1) [1,4,16] r36426 c36426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22005
  · exact u22006
  · exact u22007

def r36427 : Route 9 := (fun mask => (mask,id))

def c36427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36427 : Upper (D 7) (R 7) [34,320,40,132,65] 13 := by
  apply FastRouting.sound _ _ [34,320,40,132,65] 13 (by decide) (choices 1) [1,2,16,128] r36427 c36427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22008
  · exact u22009
  · exact u22010
  · exact u22011

def b36428 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 44 140 82 177 209 145 401), lower := (rows 35 322 44 140 82 32 64 128 256), losses := [] }

theorem u36428 : Upper (D 7) (R 7) [34,320,40,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36429 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 322 44 140 145 115 83 211 339), lower := (rows 35 322 44 140 145 32 64 128 256), losses := [] }

theorem u36429 : Upper (D 7) (R 7) [34,320,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36430 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 322 44 140 146 113 81 209 337), lower := (rows 35 322 44 140 146 32 64 128 256), losses := [] }

theorem u36430 : Upper (D 7) (R 7) [34,320,40,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36431 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 322 44 140 208 51 83 147 275), lower := (rows 35 322 44 140 208 32 64 128 256), losses := [] }

theorem u36431 : Upper (D 7) (R 7) [34,320,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36432 : Route 9 := (fun mask => (mask,id))

def c36432 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36432 : Upper (D 7) (R 7) [34,320,40,144,65] 13 := by
  apply FastRouting.sound _ _ [34,320,40,144,65] 13 (by decide) (choices 1) [1,2,4,128] r36432 c36432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22012
  · exact u22013
  · exact u22014
  · exact u22015

def b36433 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 44 152 82 165 197 133 389), lower := (rows 35 322 44 152 82 32 64 128 256), losses := [] }

theorem u36433 : Upper (D 7) (R 7) [34,320,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36434 : Route 9 := (fun mask => (mask,id))

def c36434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36434 : Upper (D 7) (R 7) [34,320,40,144,68] 13 := by
  apply FastRouting.sound _ _ [34,320,40,144,68] 13 (by decide) (choices 1) [1,2,128] r36434 c36434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22016
  · exact u22017
  · exact u22018

def b36435 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 44 152 145 103 71 199 327), lower := (rows 35 322 44 152 145 32 64 128 256), losses := [] }

theorem u36435 : Upper (D 7) (R 7) [34,320,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36436 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 44 152 146 101 69 197 325), lower := (rows 35 322 44 152 146 32 64 128 256), losses := [] }

theorem u36436 : Upper (D 7) (R 7) [34,320,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36437 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 44 152 148 99 67 195 323), lower := (rows 35 322 44 152 148 32 64 128 256), losses := [] }

theorem u36437 : Upper (D 7) (R 7) [34,320,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36438 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 44 152 208 39 71 135 263), lower := (rows 35 322 44 152 208 32 64 128 256), losses := [] }

theorem u36438 : Upper (D 7) (R 7) [34,320,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36439 : Route 9 := (fun mask => (mask,id))

def c36439 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36439 : Upper (D 7) (R 7) [34,320,40,192,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,129] 13 (by decide) (choices 1) [1,2,4,16] r36439 c36439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22019
  · exact u22020
  · exact u22021
  · exact u22022

def r36440 : Route 9 := (fun mask => (mask,id))

def c36440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36440 : Upper (D 7) (R 7) [34,320,40,192,130] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,130] 13 (by decide) (choices 1) [1,4,16] r36440 c36440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22023
  · exact u22024
  · exact u22025

def r36441 : Route 9 := (fun mask => (mask,id))

def c36441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36441 : Upper (D 7) (R 7) [34,320,40,192,132] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192,132] 13 (by decide) (choices 1) [1,2,16] r36441 c36441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22026
  · exact u22027
  · exact u22028

def r36442 : Route 9 := (fun mask => (mask,id))

def c36442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36442 : Upper (D 7) (R 7) [34,320,65,129,130] 13 := by
  apply FastRouting.sound _ _ [34,320,65,129,130] 13 (by decide) (choices 1) [4,8,16] r36442 c36442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22029
  · exact u22030
  · exact u22031

def r36443 : Route 9 := (fun mask => (mask,id))

def c36443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36443 : Upper (D 7) (R 7) [34,320,65,129,132] 13 := by
  apply FastRouting.sound _ _ [34,320,65,129,132] 13 (by decide) (choices 1) [2,8,16] r36443 c36443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22032
  · exact u22033
  · exact u22034

def b36444 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 322 69 137 152 54 118 182 310), lower := (rows 35 322 69 137 152 32 64 128 256), losses := [] }

theorem u36444 : Upper (D 7) (R 7) [34,320,65,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36445 : Route 9 := (fun mask => (mask,id))

def c36445 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36445 : Upper (D 7) (R 7) [34,320,65,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,65,129,160] 13 (by decide) (choices 1) [2,4,8,16] r36445 c36445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22035
  · exact u22036
  · exact u22037
  · exact u22038

def r36446 : Route 9 := (fun mask => (mask,id))

def c36446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36446 : Upper (D 7) (R 7) [34,320,65,130,132] 13 := by
  apply FastRouting.sound _ _ [34,320,65,130,132] 13 (by decide) (choices 1) [1,8,16] r36446 c36446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22039
  · exact u22040
  · exact u22041

def b36447 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 322 69 138 152 53 117 181 309), lower := (rows 35 322 69 138 152 32 64 128 256), losses := [] }

theorem u36447 : Upper (D 7) (R 7) [34,320,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36448 : Route 9 := (fun mask => (mask,id))

def c36448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36448 : Upper (D 7) (R 7) [34,320,65,130,160] 13 := by
  apply FastRouting.sound _ _ [34,320,65,130,160] 13 (by decide) (choices 1) [1,4,8,16] r36448 c36448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22042
  · exact u22043
  · exact u22044
  · exact u22045

def b36449 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 322 69 140 152 51 115 179 307), lower := (rows 35 322 69 140 152 32 64 128 256), losses := [] }

theorem u36449 : Upper (D 7) (R 7) [34,320,65,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36450 : Route 9 := (fun mask => (mask,id))

def c36450 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36450 : Upper (D 7) (R 7) [34,320,65,132,160] 13 := by
  apply FastRouting.sound _ _ [34,320,65,132,160] 13 (by decide) (choices 1) [1,2,8,16] r36450 c36450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22046
  · exact u22047
  · exact u22048
  · exact u22049

def b36451 : PairBound 9 := { available := 39, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 69 152 152 39 103 167 295), lower := (rows 35 322 69 152 152 32 64 128 256), losses := [] }

theorem u36451 : Upper (D 7) (R 7) [34,320,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36452 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 69 152 176 47 79 143 271), lower := (rows 35 322 69 152 176 32 64 128 256), losses := [] }

theorem u36452 : Upper (D 7) (R 7) [34,320,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36453 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 322 70 137 148 57 121 185 313), lower := (rows 35 322 70 137 148 32 64 128 256), losses := [] }

theorem u36453 : Upper (D 7) (R 7) [34,320,66,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36454 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 322 70 137 176 61 93 157 285), lower := (rows 35 322 70 137 176 32 64 128 256), losses := [] }

theorem u36454 : Upper (D 7) (R 7) [34,320,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36455 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 322 70 140 176 57 89 153 281), lower := (rows 35 322 70 140 176 32 64 128 256), losses := [] }

theorem u36455 : Upper (D 7) (R 7) [34,320,66,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36456 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 322 76 137 145 54 118 182 310), lower := (rows 35 322 76 137 145 32 64 128 256), losses := [] }

theorem u36456 : Upper (D 7) (R 7) [34,320,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36457 : Route 9 := (fun mask => (mask,id))

def c36457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36457 : Upper (D 7) (R 7) [34,320,72,129,130] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129,130] 13 (by decide) (choices 1) [1,4,16] r36457 c36457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22050
  · exact u22051
  · exact u22052

def r36458 : Route 9 := (fun mask => (mask,id))

def c36458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36458 : Upper (D 7) (R 7) [34,320,72,129,132] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129,132] 13 (by decide) (choices 1) [1,2,16] r36458 c36458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22053
  · exact u22054
  · exact u22055

def r36459 : Route 9 := (fun mask => (mask,id))

def c36459 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36459 : Upper (D 7) (R 7) [34,320,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129,160] 13 (by decide) (choices 1) [1,2,4,16] r36459 c36459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22056
  · exact u22057
  · exact u22058
  · exact u22059

def r36460 : Route 9 := (fun mask => (mask,id))

def c36460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36460 : Upper (D 7) (R 7) [34,320,72,130,129] 13 := by
  apply FastRouting.sound _ _ [34,320,72,130,129] 13 (by decide) (choices 1) [1,4,16] r36460 c36460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22060
  · exact u22061
  · exact u22062

def r36461 : Route 9 := (fun mask => (mask,id))

def c36461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36461 : Upper (D 7) (R 7) [34,320,72,130,132] 13 := by
  apply FastRouting.sound _ _ [34,320,72,130,132] 13 (by decide) (choices 1) [1,16] r36461 c36461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22063
  · exact u22064

def r36462 : Route 9 := (fun mask => (mask,id))

def c36462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36462 : Upper (D 7) (R 7) [34,320,72,130,160] 13 := by
  apply FastRouting.sound _ _ [34,320,72,130,160] 13 (by decide) (choices 1) [1,4,16] r36462 c36462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22065
  · exact u22066
  · exact u22067

def b36463 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 76 140 145 51 115 179 307), lower := (rows 35 322 76 140 145 32 64 128 256), losses := [] }

theorem u36463 : Upper (D 7) (R 7) [34,320,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36464 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 76 140 146 49 113 177 305), lower := (rows 35 322 76 140 146 32 64 128 256), losses := [] }

theorem u36464 : Upper (D 7) (R 7) [34,320,72,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36465 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 76 140 176 51 83 147 275), lower := (rows 35 322 76 140 176 32 64 128 256), losses := [] }

theorem u36465 : Upper (D 7) (R 7) [34,320,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36466 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 76 152 145 39 103 167 295), lower := (rows 35 322 76 152 145 32 64 128 256), losses := [] }

theorem u36466 : Upper (D 7) (R 7) [34,320,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36467 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 76 152 146 37 101 165 293), lower := (rows 35 322 76 152 146 32 64 128 256), losses := [] }

theorem u36467 : Upper (D 7) (R 7) [34,320,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36468 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 76 152 148 35 99 163 291), lower := (rows 35 322 76 152 148 32 64 128 256), losses := [] }

theorem u36468 : Upper (D 7) (R 7) [34,320,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36469 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 322 76 152 176 39 71 135 263), lower := (rows 35 322 76 152 176 32 64 128 256), losses := [] }

theorem u36469 : Upper (D 7) (R 7) [34,320,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36470 : Route 9 := (fun mask => (mask,id))

def c36470 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36470 : Upper (D 7) (R 7) [34,320,72,160,129] 13 := by
  apply FastRouting.sound _ _ [34,320,72,160,129] 13 (by decide) (choices 1) [1,2,4,16] r36470 c36470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22068
  · exact u22069
  · exact u22070
  · exact u22071

def r36471 : Route 9 := (fun mask => (mask,id))

def c36471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36471 : Upper (D 7) (R 7) [34,320,72,160,130] 13 := by
  apply FastRouting.sound _ _ [34,320,72,160,130] 13 (by decide) (choices 1) [1,4,16] r36471 c36471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22072
  · exact u22073
  · exact u22074

def r36472 : Route 9 := (fun mask => (mask,id))

def c36472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36472 : Upper (D 7) (R 7) [34,320,72,160,132] 13 := by
  apply FastRouting.sound _ _ [34,320,72,160,132] 13 (by decide) (choices 1) [1,2,16] r36472 c36472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22075
  · exact u22076
  · exact u22077

def b36473 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 322 100 137 145 62 94 158 286), lower := (rows 35 322 100 137 145 32 64 128 256), losses := [] }

theorem u36473 : Upper (D 7) (R 7) [34,320,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36474 : Route 9 := (fun mask => (mask,id))

def c36474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36474 : Upper (D 7) (R 7) [34,320,96,129,130] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129,130] 13 (by decide) (choices 1) [1,4,8,16] r36474 c36474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22078
  · exact u22079
  · exact u22080
  · exact u22081

def r36475 : Route 9 := (fun mask => (mask,id))

def c36475 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36475 : Upper (D 7) (R 7) [34,320,96,129,132] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129,132] 13 (by decide) (choices 1) [1,2,8,16] r36475 c36475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22082
  · exact u22083
  · exact u22084
  · exact u22085

def b36476 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 322 100 137 152 55 87 151 279), lower := (rows 35 322 100 137 152 32 64 128 256), losses := [] }

theorem u36476 : Upper (D 7) (R 7) [34,320,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36477 : Route 9 := (fun mask => (mask,id))

def c36477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36477 : Upper (D 7) (R 7) [34,320,96,130,132] 13 := by
  apply FastRouting.sound _ _ [34,320,96,130,132] 13 (by decide) (choices 1) [1,8,16] r36477 c36477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22086
  · exact u22087
  · exact u22088

def b36478 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 322 100 138 152 53 85 149 277), lower := (rows 35 322 100 138 152 32 64 128 256), losses := [] }

theorem u36478 : Upper (D 7) (R 7) [34,320,96,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36479 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 322 100 140 152 51 83 147 275), lower := (rows 35 322 100 140 152 32 64 128 256), losses := [] }

theorem u36479 : Upper (D 7) (R 7) [34,320,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36479
end Delivery.IrregularNine14.P07
