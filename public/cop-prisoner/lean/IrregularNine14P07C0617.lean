import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0383
import IrregularNine14P07C0384
import IrregularNine14P07C0385

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37020 : Route 9 := (fun mask => (mask,id))

def c37020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37020 : Upper (D 7) (R 7) [36,72,65,288,129] 13 := by
  apply FastRouting.sound _ _ [36,72,65,288,129] 13 (by decide) (choices 1) [2,16,128] r37020 c37020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23018
  · exact u23019
  · exact u23020

def r37021 : Route 9 := (fun mask => (mask,id))

def c37021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37021 : Upper (D 7) (R 7) [36,72,65,288,130] 13 := by
  apply FastRouting.sound _ _ [36,72,65,288,130] 13 (by decide) (choices 1) [1,2,16,128] r37021 c37021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23021
  · exact u23022
  · exact u23023
  · exact u23024

def r37022 : Route 9 := (fun mask => (mask,id))

def c37022 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37022 : Upper (D 7) (R 7) [36,72,65,384,3] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,3] 13 (by decide) (choices 1) [2,16,128] r37022 c37022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23025
  · exact u23026
  · exact u23027

def b37023 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 69 392 49 178 210 146 402), lower := (rows 37 74 69 392 49 32 64 128 256), losses := [] }

theorem u37023 : Upper (D 7) (R 7) [36,72,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37024 : Route 9 := (fun mask => (mask,id))

def c37024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37024 : Upper (D 7) (R 7) [36,72,65,384,34] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,34] 13 (by decide) (choices 1) [1,2,16,128] r37024 c37024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23028
  · exact u23029
  · exact u23030
  · exact u23031

def r37025 : Route 9 := (fun mask => (mask,id))

def c37025 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37025 : Upper (D 7) (R 7) [36,72,65,384,129] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,129] 13 (by decide) (choices 1) [2,16] r37025 c37025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23032
  · exact u23033

def r37026 : Route 9 := (fun mask => (mask,id))

def c37026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37026 : Upper (D 7) (R 7) [36,72,65,384,130] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,130] 13 (by decide) (choices 1) [1,2,16] r37026 c37026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23034
  · exact u23035
  · exact u23036

def r37027 : Route 9 := (fun mask => (mask,id))

def c37027 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37027 : Upper (D 7) (R 7) [36,72,65,384,160] 13 := by
  apply FastRouting.sound _ _ [36,72,65,384,160] 13 (by decide) (choices 1) [1,2,16] r37027 c37027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23037
  · exact u23038
  · exact u23039

def b37028 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 354, targets := 1 },{ cop := 4, region := 484, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(3,6)], upper := (rows 37 74 84 137 19 418 482 418 418), lower := (rows 37 74 84 137 19 32 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 28 16 50 0 146 274), good := (rows 45 426 445 137 443 32 0 128 256) }] }

theorem u37028 : Upper (D 7) (R 7) [36,72,80,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37029 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 84 137 49 418 450 386 386), lower := (rows 37 74 84 137 49 32 64 128 256), losses := [] }

theorem u37029 : Upper (D 7) (R 7) [36,72,80,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37030 : Route 9 := (fun mask => (mask,id))

def c37030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37030 : Upper (D 7) (R 7) [36,72,80,129,34] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,34] 13 (by decide) (choices 1) [1,2,128,256] r37030 c37030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23040
  · exact u23041
  · exact u23042
  · exact u23043

def b37031 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 74 84 137 145 290 354 418 290), lower := (rows 37 74 84 137 145 32 64 128 256), losses := [] }

theorem u37031 : Upper (D 7) (R 7) [36,72,80,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37032 : Route 9 := (fun mask => (mask,id))

def c37032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37032 : Upper (D 7) (R 7) [36,72,80,129,130] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,130] 13 (by decide) (choices 1) [1,2,256] r37032 c37032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23044
  · exact u23045
  · exact u23046

def r37033 : Route 9 := (fun mask => (mask,id))

def c37033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37033 : Upper (D 7) (R 7) [36,72,80,129,160] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,160] 13 (by decide) (choices 1) [1,2,256] r37033 c37033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23047
  · exact u23048
  · exact u23049

def r37034 : Route 9 := (fun mask => (mask,id))

def c37034 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37034 : Upper (D 7) (R 7) [36,72,80,129,257] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,257] 13 (by decide) (choices 1) [2,128] r37034 c37034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23050
  · exact u23051

def r37035 : Route 9 := (fun mask => (mask,id))

def c37035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37035 : Upper (D 7) (R 7) [36,72,80,129,258] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,258] 13 (by decide) (choices 1) [1,2,128] r37035 c37035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23052
  · exact u23053
  · exact u23054

def r37036 : Route 9 := (fun mask => (mask,id))

def c37036 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37036 : Upper (D 7) (R 7) [36,72,80,129,288] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,288] 13 (by decide) (choices 1) [1,2,128] r37036 c37036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23055
  · exact u23056
  · exact u23057

def r37037 : Route 9 := (fun mask => (mask,id))

def c37037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37037 : Upper (D 7) (R 7) [36,72,80,129,384] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,384] 13 (by decide) (choices 1) [1,2] r37037 c37037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23058
  · exact u23059

def b37038 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 485, targets := 2 },{ cop := 2, region := 417, targets := 64 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(3,6)], upper := (rows 37 74 84 138 19 417 481 417 417), lower := (rows 37 74 84 138 19 32 64 128 256), losses := [] }

theorem u37038 : Upper (D 7) (R 7) [36,72,80,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37039 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 84 138 49 419 451 387 387), lower := (rows 37 74 84 138 49 32 64 128 256), losses := [] }

theorem u37039 : Upper (D 7) (R 7) [36,72,80,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37040 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(3,5)], upper := (rows 37 74 84 138 50 417 449 385 385), lower := (rows 37 74 84 138 50 32 64 128 256), losses := [] }

theorem u37040 : Upper (D 7) (R 7) [36,72,80,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37041 : Route 9 := (fun mask => (mask,id))

def c37041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37041 : Upper (D 7) (R 7) [36,72,80,130,129] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,129] 13 (by decide) (choices 1) [1,2,256] r37041 c37041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23060
  · exact u23061
  · exact u23062

def b37042 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 74 84 138 146 289 353 417 289), lower := (rows 37 74 84 138 146 32 64 128 256), losses := [] }

theorem u37042 : Upper (D 7) (R 7) [36,72,80,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37043 : Route 9 := (fun mask => (mask,id))

def c37043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37043 : Upper (D 7) (R 7) [36,72,80,130,160] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,160] 13 (by decide) (choices 1) [1,2,256] r37043 c37043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23063
  · exact u23064
  · exact u23065

def r37044 : Route 9 := (fun mask => (mask,id))

def c37044 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37044 : Upper (D 7) (R 7) [36,72,80,130,257] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,257] 13 (by decide) (choices 1) [1,2,128] r37044 c37044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23066
  · exact u23067
  · exact u23068

def r37045 : Route 9 := (fun mask => (mask,id))

def c37045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37045 : Upper (D 7) (R 7) [36,72,80,130,258] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,258] 13 (by decide) (choices 1) [1,128] r37045 c37045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23069
  · exact u23070

def r37046 : Route 9 := (fun mask => (mask,id))

def c37046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37046 : Upper (D 7) (R 7) [36,72,80,130,288] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,288] 13 (by decide) (choices 1) [1,2,128] r37046 c37046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23071
  · exact u23072
  · exact u23073

def r37047 : Route 9 := (fun mask => (mask,id))

def c37047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37047 : Upper (D 7) (R 7) [36,72,80,130,384] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,384] 13 (by decide) (choices 1) [1,2] r37047 c37047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23074
  · exact u23075

def r37048 : Route 9 := (fun mask => (mask,id))

def c37048 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37048 : Upper (D 7) (R 7) [36,72,80,160,3] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,3] 13 (by decide) (choices 1) [1,2,128,256] r37048 c37048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23076
  · exact u23077
  · exact u23078
  · exact u23079

def r37049 : Route 9 := (fun mask => (mask,id))

def c37049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37049 : Upper (D 7) (R 7) [36,72,80,160,129] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,129] 13 (by decide) (choices 1) [1,2,256] r37049 c37049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23080
  · exact u23081
  · exact u23082

def r37050 : Route 9 := (fun mask => (mask,id))

def c37050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37050 : Upper (D 7) (R 7) [36,72,80,160,130] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,130] 13 (by decide) (choices 1) [1,2,256] r37050 c37050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23083
  · exact u23084
  · exact u23085

def r37051 : Route 9 := (fun mask => (mask,id))

def c37051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37051 : Upper (D 7) (R 7) [36,72,80,160,257] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,257] 13 (by decide) (choices 1) [1,2,128] r37051 c37051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23086
  · exact u23087
  · exact u23088

def r37052 : Route 9 := (fun mask => (mask,id))

def c37052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37052 : Upper (D 7) (R 7) [36,72,80,160,258] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,258] 13 (by decide) (choices 1) [1,2,128] r37052 c37052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23089
  · exact u23090
  · exact u23091

def r37053 : Route 9 := (fun mask => (mask,id))

def c37053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37053 : Upper (D 7) (R 7) [36,72,80,160,384] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,384] 13 (by decide) (choices 1) [1,2] r37053 c37053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23092
  · exact u23093

def b37054 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 226, targets := 1 },{ cop := 4, region := 228, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(3,6)], upper := (rows 37 74 84 265 19 162 226 162 418), lower := (rows 37 74 84 265 19 32 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 28 16 50 0 146 274), good := (rows 45 426 445 265 443 32 0 128 256) }] }

theorem u37054 : Upper (D 7) (R 7) [36,72,80,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37055 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 84 265 49 162 194 130 386), lower := (rows 37 74 84 265 49 32 64 128 256), losses := [] }

theorem u37055 : Upper (D 7) (R 7) [36,72,80,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37056 : Route 9 := (fun mask => (mask,id))

def c37056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37056 : Upper (D 7) (R 7) [36,72,80,257,34] 13 := by
  apply FastRouting.sound _ _ [36,72,80,257,34] 13 (by decide) (choices 1) [1,2,128] r37056 c37056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23094
  · exact u23095
  · exact u23096

def r37057 : Route 9 := (fun mask => (mask,id))

def c37057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37057 : Upper (D 7) (R 7) [36,72,80,257,129] 13 := by
  apply FastRouting.sound _ _ [36,72,80,257,129] 13 (by decide) (choices 1) [2,128] r37057 c37057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23097
  · exact u23098

def r37058 : Route 9 := (fun mask => (mask,id))

def c37058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37058 : Upper (D 7) (R 7) [36,72,80,257,130] 13 := by
  apply FastRouting.sound _ _ [36,72,80,257,130] 13 (by decide) (choices 1) [1,2,128] r37058 c37058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23099
  · exact u23100
  · exact u23101

def r37059 : Route 9 := (fun mask => (mask,id))

def c37059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37059 : Upper (D 7) (R 7) [36,72,80,257,160] 13 := by
  apply FastRouting.sound _ _ [36,72,80,257,160] 13 (by decide) (choices 1) [1,2,128] r37059 c37059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23102
  · exact u23103
  · exact u23104

def b37060 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 2, region := 161, targets := 64 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(3,6)], upper := (rows 37 74 84 266 19 161 225 161 417), lower := (rows 37 74 84 266 19 32 64 128 256), losses := [] }

theorem u37060 : Upper (D 7) (R 7) [36,72,80,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37061 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 84 266 49 163 195 131 387), lower := (rows 37 74 84 266 49 32 64 128 256), losses := [] }

theorem u37061 : Upper (D 7) (R 7) [36,72,80,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37062 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(3,5)], upper := (rows 37 74 84 266 50 161 193 129 385), lower := (rows 37 74 84 266 50 32 64 128 256), losses := [] }

theorem u37062 : Upper (D 7) (R 7) [36,72,80,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37063 : Route 9 := (fun mask => (mask,id))

def c37063 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37063 : Upper (D 7) (R 7) [36,72,80,258,129] 13 := by
  apply FastRouting.sound _ _ [36,72,80,258,129] 13 (by decide) (choices 1) [1,2,128] r37063 c37063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23105
  · exact u23106
  · exact u23107

def r37064 : Route 9 := (fun mask => (mask,id))

def c37064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37064 : Upper (D 7) (R 7) [36,72,80,258,130] 13 := by
  apply FastRouting.sound _ _ [36,72,80,258,130] 13 (by decide) (choices 1) [1,128] r37064 c37064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23108
  · exact u23109

def r37065 : Route 9 := (fun mask => (mask,id))

def c37065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37065 : Upper (D 7) (R 7) [36,72,80,258,160] 13 := by
  apply FastRouting.sound _ _ [36,72,80,258,160] 13 (by decide) (choices 1) [1,2,128] r37065 c37065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23110
  · exact u23111
  · exact u23112

def r37066 : Route 9 := (fun mask => (mask,id))

def c37066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37066 : Upper (D 7) (R 7) [36,72,80,288,3] 13 := by
  apply FastRouting.sound _ _ [36,72,80,288,3] 13 (by decide) (choices 1) [1,2,128] r37066 c37066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23113
  · exact u23114
  · exact u23115

def r37067 : Route 9 := (fun mask => (mask,id))

def c37067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37067 : Upper (D 7) (R 7) [36,72,80,288,129] 13 := by
  apply FastRouting.sound _ _ [36,72,80,288,129] 13 (by decide) (choices 1) [1,2,128] r37067 c37067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23116
  · exact u23117
  · exact u23118

def r37068 : Route 9 := (fun mask => (mask,id))

def c37068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37068 : Upper (D 7) (R 7) [36,72,80,288,130] 13 := by
  apply FastRouting.sound _ _ [36,72,80,288,130] 13 (by decide) (choices 1) [1,2,128] r37068 c37068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23119
  · exact u23120
  · exact u23121

def r37069 : Route 9 := (fun mask => (mask,id))

def c37069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37069 : Upper (D 7) (R 7) [36,72,80,384,3] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384,3] 13 (by decide) (choices 1) [1,2,128] r37069 c37069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23122
  · exact u23123
  · exact u23124

def b37070 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 84 392 49 163 195 131 387), lower := (rows 37 74 84 392 49 32 64 128 256), losses := [] }

theorem u37070 : Upper (D 7) (R 7) [36,72,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37071 : Route 9 := (fun mask => (mask,id))

def c37071 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37071 : Upper (D 7) (R 7) [36,72,80,384,34] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384,34] 13 (by decide) (choices 1) [1,2,128] r37071 c37071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23125
  · exact u23126
  · exact u23127

def r37072 : Route 9 := (fun mask => (mask,id))

def c37072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37072 : Upper (D 7) (R 7) [36,72,80,384,129] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384,129] 13 (by decide) (choices 1) [1,2] r37072 c37072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23128
  · exact u23129

def r37073 : Route 9 := (fun mask => (mask,id))

def c37073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37073 : Upper (D 7) (R 7) [36,72,80,384,130] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384,130] 13 (by decide) (choices 1) [1,2] r37073 c37073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23130
  · exact u23131

def r37074 : Route 9 := (fun mask => (mask,id))

def c37074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37074 : Upper (D 7) (R 7) [36,72,80,384,160] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384,160] 13 (by decide) (choices 1) [1,2] r37074 c37074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23132
  · exact u23133

def b37075 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 133 138 19 368 368 496 368), lower := (rows 37 74 133 138 19 32 64 128 256), losses := [] }

theorem u37075 : Upper (D 7) (R 7) [36,72,129,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37076 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 133 138 49 370 338 466 338), lower := (rows 37 74 133 138 49 32 64 128 256), losses := [] }

theorem u37076 : Upper (D 7) (R 7) [36,72,129,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37077 : Route 9 := (fun mask => (mask,id))

def c37077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37077 : Upper (D 7) (R 7) [36,72,129,130,34] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130,34] 13 (by decide) (choices 1) [1,16,64,256] r37077 c37077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23134
  · exact u23135
  · exact u23136
  · exact u23137

def r37078 : Route 9 := (fun mask => (mask,id))

def c37078 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37078 : Upper (D 7) (R 7) [36,72,129,130,96] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130,96] 13 (by decide) (choices 1) [1,2,16,256] r37078 c37078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23138
  · exact u23139
  · exact u23140
  · exact u23141

def r37079 : Route 9 := (fun mask => (mask,id))

def c37079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37079 : Upper (D 7) (R 7) [36,72,129,130,257] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130,257] 13 (by decide) (choices 1) [2,16,64] r37079 c37079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23142
  · exact u23143
  · exact u23144

#print axioms u37079
end Delivery.IrregularNine14.P07
