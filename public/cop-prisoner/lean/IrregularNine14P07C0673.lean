import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0484
import IrregularNine14P07C0485
import IrregularNine14P07C0486

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40380 : Route 9 := (fun mask => (mask,id))

def c40380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40380 : Upper (D 7) (R 7) [96,260,40,17,130] 13 := by
  apply FastRouting.sound _ _ [96,260,40,17,130] 13 (by decide) (choices 1) [1,2,64,128] r40380 c40380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29049
  · exact u29050
  · exact u29051
  · exact u29052

def r40381 : Route 9 := (fun mask => (mask,id))

def c40381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40381 : Upper (D 7) (R 7) [96,260,40,17,192] 13 := by
  apply FastRouting.sound _ _ [96,260,40,17,192] 13 (by decide) (choices 1) [1,2,128] r40381 c40381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29053
  · exact u29054
  · exact u29055

def b40382 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 193 },{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 44 26 19 225 193 193 449), lower := (rows 97 262 44 26 19 32 64 128 256), losses := [] }

theorem u40382 : Upper (D 7) (R 7) [96,260,40,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40383 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 44 26 81 163 195 131 387), lower := (rows 97 262 44 26 81 32 64 128 256), losses := [] }

theorem u40383 : Upper (D 7) (R 7) [96,260,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40384 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 44 26 82 161 193 129 385), lower := (rows 97 262 44 26 82 32 64 128 256), losses := [] }

theorem u40384 : Upper (D 7) (R 7) [96,260,40,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40385 : Route 9 := (fun mask => (mask,id))

def c40385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40385 : Upper (D 7) (R 7) [96,260,40,18,129] 13 := by
  apply FastRouting.sound _ _ [96,260,40,18,129] 13 (by decide) (choices 1) [1,2,64,128] r40385 c40385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29056
  · exact u29057
  · exact u29058
  · exact u29059

def b40386 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 44 26 146 225 193 193 449), lower := (rows 97 262 44 26 146 32 64 128 256), losses := [] }

theorem u40386 : Upper (D 7) (R 7) [96,260,40,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40387 : Route 9 := (fun mask => (mask,id))

def c40387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40387 : Upper (D 7) (R 7) [96,260,40,18,192] 13 := by
  apply FastRouting.sound _ _ [96,260,40,18,192] 13 (by decide) (choices 1) [1,2,128] r40387 c40387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29060
  · exact u29061
  · exact u29062

def r40388 : Route 9 := (fun mask => (mask,id))

def c40388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40388 : Upper (D 7) (R 7) [96,260,40,66,3] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,3] 13 (by decide) (choices 1) [1,16,128] r40388 c40388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29063
  · exact u29064
  · exact u29065

def r40389 : Route 9 := (fun mask => (mask,id))

def c40389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40389 : Upper (D 7) (R 7) [96,260,40,66,129] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,129] 13 (by decide) (choices 1) [1,2,16,128] r40389 c40389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29066
  · exact u29067
  · exact u29068
  · exact u29069

def r40390 : Route 9 := (fun mask => (mask,id))

def c40390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40390 : Upper (D 7) (R 7) [96,260,40,66,130] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,130] 13 (by decide) (choices 1) [1,16,128] r40390 c40390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29070
  · exact u29071
  · exact u29072

def r40391 : Route 9 := (fun mask => (mask,id))

def c40391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40391 : Upper (D 7) (R 7) [96,260,40,80,3] 13 := by
  apply FastRouting.sound _ _ [96,260,40,80,3] 13 (by decide) (choices 1) [1,2,128] r40391 c40391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29073
  · exact u29074
  · exact u29075

def r40392 : Route 9 := (fun mask => (mask,id))

def c40392 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40392 : Upper (D 7) (R 7) [96,260,40,80,129] 13 := by
  apply FastRouting.sound _ _ [96,260,40,80,129] 13 (by decide) (choices 1) [1,2,128] r40392 c40392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29076
  · exact u29077
  · exact u29078

def r40393 : Route 9 := (fun mask => (mask,id))

def c40393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40393 : Upper (D 7) (R 7) [96,260,40,80,130] 13 := by
  apply FastRouting.sound _ _ [96,260,40,80,130] 13 (by decide) (choices 1) [1,2,128] r40393 c40393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29079
  · exact u29080
  · exact u29081

def r40394 : Route 9 := (fun mask => (mask,id))

def c40394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40394 : Upper (D 7) (R 7) [96,260,40,129,3] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,3] 13 (by decide) (choices 1) [2,16,64,128] r40394 c40394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29082
  · exact u29083
  · exact u29084
  · exact u29085

def b40395 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 44 137 81 178 210 146 402), lower := (rows 97 262 44 137 81 32 64 128 256), losses := [] }

theorem u40395 : Upper (D 7) (R 7) [96,260,40,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40396 : Route 9 := (fun mask => (mask,id))

def c40396 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40396 : Upper (D 7) (R 7) [96,260,40,129,66] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,66] 13 (by decide) (choices 1) [1,2,16,128] r40396 c40396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29086
  · exact u29087
  · exact u29088
  · exact u29089

def b40397 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 97 262 44 137 145 114 82 210 338), lower := (rows 97 262 44 137 145 32 64 128 256), losses := [] }

theorem u40397 : Upper (D 7) (R 7) [96,260,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40398 : Route 9 := (fun mask => (mask,id))

def c40398 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40398 : Upper (D 7) (R 7) [96,260,40,129,130] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,130] 13 (by decide) (choices 1) [1,2,16,64] r40398 c40398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29090
  · exact u29091
  · exact u29092
  · exact u29093

def r40399 : Route 9 := (fun mask => (mask,id))

def c40399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40399 : Upper (D 7) (R 7) [96,260,40,129,192] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,192] 13 (by decide) (choices 1) [1,2,16] r40399 c40399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29094
  · exact u29095
  · exact u29096

def r40400 : Route 9 := (fun mask => (mask,id))

def c40400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40400 : Upper (D 7) (R 7) [96,260,40,130,3] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,3] 13 (by decide) (choices 1) [1,16,64,128] r40400 c40400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29097
  · exact u29098
  · exact u29099
  · exact u29100

def b40401 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 44 138 81 179 211 147 403), lower := (rows 97 262 44 138 81 32 64 128 256), losses := [] }

theorem u40401 : Upper (D 7) (R 7) [96,260,40,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40402 : Route 9 := (fun mask => (mask,id))

def c40402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40402 : Upper (D 7) (R 7) [96,260,40,130,66] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,66] 13 (by decide) (choices 1) [1,16,128] r40402 c40402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29101
  · exact u29102
  · exact u29103

def r40403 : Route 9 := (fun mask => (mask,id))

def c40403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40403 : Upper (D 7) (R 7) [96,260,40,130,129] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,129] 13 (by decide) (choices 1) [1,2,16,64] r40403 c40403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29104
  · exact u29105
  · exact u29106
  · exact u29107

def b40404 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 97 262 44 138 146 113 81 209 337), lower := (rows 97 262 44 138 146 32 64 128 256), losses := [] }

theorem u40404 : Upper (D 7) (R 7) [96,260,40,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40405 : Route 9 := (fun mask => (mask,id))

def c40405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40405 : Upper (D 7) (R 7) [96,260,40,130,192] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,192] 13 (by decide) (choices 1) [1,2,16] r40405 c40405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29108
  · exact u29109
  · exact u29110

def r40406 : Route 9 := (fun mask => (mask,id))

def c40406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40406 : Upper (D 7) (R 7) [96,260,40,144,3] 13 := by
  apply FastRouting.sound _ _ [96,260,40,144,3] 13 (by decide) (choices 1) [1,2,64,128] r40406 c40406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29111
  · exact u29112
  · exact u29113
  · exact u29114

def b40407 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 44 152 81 163 195 131 387), lower := (rows 97 262 44 152 81 32 64 128 256), losses := [] }

theorem u40407 : Upper (D 7) (R 7) [96,260,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40408 : Route 9 := (fun mask => (mask,id))

def c40408 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40408 : Upper (D 7) (R 7) [96,260,40,144,66] 13 := by
  apply FastRouting.sound _ _ [96,260,40,144,66] 13 (by decide) (choices 1) [1,2,128] r40408 c40408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29115
  · exact u29116
  · exact u29117

def b40409 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 44 152 145 99 67 195 323), lower := (rows 97 262 44 152 145 32 64 128 256), losses := [] }

theorem u40409 : Upper (D 7) (R 7) [96,260,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40410 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 44 152 146 99 67 195 323), lower := (rows 97 262 44 152 146 32 64 128 256), losses := [] }

theorem u40410 : Upper (D 7) (R 7) [96,260,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40411 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 44 152 208 35 67 131 259), lower := (rows 97 262 44 152 208 32 64 128 256), losses := [] }

theorem u40411 : Upper (D 7) (R 7) [96,260,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40412 : Route 9 := (fun mask => (mask,id))

def c40412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40412 : Upper (D 7) (R 7) [96,260,40,192,3] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,3] 13 (by decide) (choices 1) [1,2,16,128] r40412 c40412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29118
  · exact u29119
  · exact u29120
  · exact u29121

def r40413 : Route 9 := (fun mask => (mask,id))

def c40413 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40413 : Upper (D 7) (R 7) [96,260,40,192,129] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,129] 13 (by decide) (choices 1) [1,2,16] r40413 c40413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29122
  · exact u29123
  · exact u29124

def r40414 : Route 9 := (fun mask => (mask,id))

def c40414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40414 : Upper (D 7) (R 7) [96,260,40,192,130] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,130] 13 (by decide) (choices 1) [1,2,16] r40414 c40414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29125
  · exact u29126
  · exact u29127

def b40415 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(4,5),(4,6),(4,7)], upper := (rows 97 262 133 11 26 240 240 240 496), lower := (rows 97 262 133 11 26 32 64 128 256), losses := [] }

theorem u40415 : Upper (D 7) (R 7) [96,260,129,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40416 : Route 9 := (fun mask => (mask,id))

def c40416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u40416 : Upper (D 7) (R 7) [96,260,129,3,34] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,34] 13 (by decide) (choices 1) [8,16,64,128] r40416 c40416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29128
  · exact u29129
  · exact u29130
  · exact u29131

def r40417 : Route 9 := (fun mask => (mask,id))

def c40417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40417 : Upper (D 7) (R 7) [96,260,129,3,40] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,40] 13 (by decide) (choices 1) [2,16,64,128] r40417 c40417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29132
  · exact u29133
  · exact u29134
  · exact u29135

def b40418 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 133 11 112 186 218 154 410), lower := (rows 97 262 133 11 112 32 64 128 256), losses := [] }

theorem u40418 : Upper (D 7) (R 7) [96,260,129,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40419 : Route 9 := (fun mask => (mask,id))

def c40419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40419 : Upper (D 7) (R 7) [96,260,129,3,130] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,130] 13 (by decide) (choices 1) [8,16,64] r40419 c40419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29136
  · exact u29137
  · exact u29138

def r40420 : Route 9 := (fun mask => (mask,id))

def c40420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40420 : Upper (D 7) (R 7) [96,260,129,3,136] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,136] 13 (by decide) (choices 1) [2,16,64] r40420 c40420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29139
  · exact u29140
  · exact u29141

def r40421 : Route 9 := (fun mask => (mask,id))

def c40421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40421 : Upper (D 7) (R 7) [96,260,129,3,160] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,160] 13 (by decide) (choices 1) [2,8,16,64] r40421 c40421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29142
  · exact u29143
  · exact u29144
  · exact u29145

def r40422 : Route 9 := (fun mask => (mask,id))

def c40422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40422 : Upper (D 7) (R 7) [96,260,129,17,10] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,10] 13 (by decide) (choices 1) [2,64,128] r40422 c40422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29146
  · exact u29147
  · exact u29148

def r40423 : Route 9 := (fun mask => (mask,id))

def c40423 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40423 : Upper (D 7) (R 7) [96,260,129,17,34] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,34] 13 (by decide) (choices 1) [2,8,64,128] r40423 c40423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29149
  · exact u29150
  · exact u29151
  · exact u29152

def b40424 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 262 133 25 56 226 194 194 450), lower := (rows 97 262 133 25 56 32 64 128 256), losses := [] }

theorem u40424 : Upper (D 7) (R 7) [96,260,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40425 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 133 25 112 170 202 138 394), lower := (rows 97 262 133 25 112 32 64 128 256), losses := [] }

theorem u40425 : Upper (D 7) (R 7) [96,260,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40426 : Route 9 := (fun mask => (mask,id))

def c40426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40426 : Upper (D 7) (R 7) [96,260,129,17,130] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,130] 13 (by decide) (choices 1) [2,8,64] r40426 c40426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29153
  · exact u29154
  · exact u29155

def b40427 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 97 262 133 25 152 98 98 226 354), lower := (rows 97 262 133 25 152 32 64 128 256), losses := [] }

theorem u40427 : Upper (D 7) (R 7) [96,260,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40428 : Route 9 := (fun mask => (mask,id))

def c40428 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40428 : Upper (D 7) (R 7) [96,260,129,17,160] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,160] 13 (by decide) (choices 1) [2,8,64] r40428 c40428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29156
  · exact u29157
  · exact u29158

def b40429 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 133 26 26 225 225 225 481), lower := (rows 97 262 133 26 26 32 64 128 256), losses := [] }

theorem u40429 : Upper (D 7) (R 7) [96,260,129,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40430 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 133 26 49 234 202 202 458), lower := (rows 97 262 133 26 49 32 64 128 256), losses := [] }

theorem u40430 : Upper (D 7) (R 7) [96,260,129,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40431 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 133 26 50 233 201 201 457), lower := (rows 97 262 133 26 50 32 64 128 256), losses := [] }

theorem u40431 : Upper (D 7) (R 7) [96,260,129,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40432 : Route 9 := (fun mask => (mask,id))

def c40432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40432 : Upper (D 7) (R 7) [96,260,129,18,40] 13 := by
  apply FastRouting.sound _ _ [96,260,129,18,40] 13 (by decide) (choices 1) [1,2,64,128] r40432 c40432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29159
  · exact u29160
  · exact u29161
  · exact u29162

def b40433 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 133 26 112 171 203 139 395), lower := (rows 97 262 133 26 112 32 64 128 256), losses := [] }

theorem u40433 : Upper (D 7) (R 7) [96,260,129,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40434 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 97 262 133 26 145 106 106 234 362), lower := (rows 97 262 133 26 145 32 64 128 256), losses := [] }

theorem u40434 : Upper (D 7) (R 7) [96,260,129,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40435 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 97 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,6)], upper := (rows 97 262 133 26 146 105 105 233 361), lower := (rows 97 262 133 26 146 32 64 128 256), losses := [] }

theorem u40435 : Upper (D 7) (R 7) [96,260,129,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40436 : Route 9 := (fun mask => (mask,id))

def c40436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40436 : Upper (D 7) (R 7) [96,260,129,18,136] 13 := by
  apply FastRouting.sound _ _ [96,260,129,18,136] 13 (by decide) (choices 1) [1,2,64] r40436 c40436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29163
  · exact u29164
  · exact u29165

def r40437 : Route 9 := (fun mask => (mask,id))

def c40437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40437 : Upper (D 7) (R 7) [96,260,129,18,160] 13 := by
  apply FastRouting.sound _ _ [96,260,129,18,160] 13 (by decide) (choices 1) [1,2,8,64] r40437 c40437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29166
  · exact u29167
  · exact u29168
  · exact u29169

def b40438 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 133 41 82 186 218 154 410), lower := (rows 97 262 133 41 82 32 64 128 256), losses := [] }

theorem u40438 : Upper (D 7) (R 7) [96,260,129,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40439 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 133 41 88 178 210 146 402), lower := (rows 97 262 133 41 88 32 64 128 256), losses := [] }

theorem u40439 : Upper (D 7) (R 7) [96,260,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40439
end Delivery.IrregularNine14.P07
