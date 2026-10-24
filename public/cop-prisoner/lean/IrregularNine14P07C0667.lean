import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0473
import IrregularNine14P07C0474
import IrregularNine14P07C0475

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40020 : Route 9 := (fun mask => (mask,id))

def c40020 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40020 : Upper (D 7) (R 7) [96,257,9,48,130] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,130] 13 (by decide) (choices 1) [2,4,64,128] r40020 c40020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28416
  · exact u28417
  · exact u28418
  · exact u28419

def r40021 : Route 9 := (fun mask => (mask,id))

def c40021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40021 : Upper (D 7) (R 7) [96,257,9,48,132] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,132] 13 (by decide) (choices 1) [2,64,128] r40021 c40021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28420
  · exact u28421
  · exact u28422

def r40022 : Route 9 := (fun mask => (mask,id))

def c40022 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40022 : Upper (D 7) (R 7) [96,257,9,48,192] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,192] 13 (by decide) (choices 1) [2,4,128] r40022 c40022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28423
  · exact u28424
  · exact u28425

def b40023 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 13 104 22 178 210 146 402), lower := (rows 97 259 13 104 22 32 64 128 256), losses := [] }

theorem u40023 : Upper (D 7) (R 7) [96,257,9,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40024 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 13 104 146 182 214 150 406), lower := (rows 97 259 13 104 146 32 64 128 256), losses := [] }

theorem u40024 : Upper (D 7) (R 7) [96,257,9,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40025 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 13 104 148 178 210 146 402), lower := (rows 97 259 13 104 148 32 64 128 256), losses := [] }

theorem u40025 : Upper (D 7) (R 7) [96,257,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40026 : Route 9 := (fun mask => (mask,id))

def c40026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40026 : Upper (D 7) (R 7) [96,257,9,130,6] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,6] 13 (by decide) (choices 1) [16,64,128] r40026 c40026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28426
  · exact u28427
  · exact u28428

def r40027 : Route 9 := (fun mask => (mask,id))

def c40027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40027 : Upper (D 7) (R 7) [96,257,9,130,34] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,34] 13 (by decide) (choices 1) [4,16,64,128] r40027 c40027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28429
  · exact u28430
  · exact u28431
  · exact u28432

def r40028 : Route 9 := (fun mask => (mask,id))

def c40028 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40028 : Upper (D 7) (R 7) [96,257,9,130,36] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,36] 13 (by decide) (choices 1) [2,16,64,128] r40028 c40028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28433
  · exact u28434
  · exact u28435
  · exact u28436

def b40029 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 259 13 138 112 182 214 150 406), lower := (rows 97 259 13 138 112 32 64 128 256), losses := [] }

theorem u40029 : Upper (D 7) (R 7) [96,257,9,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40030 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 97 259 13 138 146 116 116 244 372), lower := (rows 97 259 13 138 146 32 64 128 256), losses := [] }

theorem u40030 : Upper (D 7) (R 7) [96,257,9,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40031 : Route 9 := (fun mask => (mask,id))

def c40031 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40031 : Upper (D 7) (R 7) [96,257,9,130,132] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,132] 13 (by decide) (choices 1) [2,16,64] r40031 c40031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28437
  · exact u28438
  · exact u28439

def r40032 : Route 9 := (fun mask => (mask,id))

def c40032 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40032 : Upper (D 7) (R 7) [96,257,9,130,160] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,160] 13 (by decide) (choices 1) [2,4,16,64] r40032 c40032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28440
  · exact u28441
  · exact u28442
  · exact u28443

def r40033 : Route 9 := (fun mask => (mask,id))

def c40033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40033 : Upper (D 7) (R 7) [96,257,9,132,34] 13 := by
  apply FastRouting.sound _ _ [96,257,9,132,34] 13 (by decide) (choices 1) [2,16,64,128] r40033 c40033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28444
  · exact u28445
  · exact u28446
  · exact u28447

def b40034 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 259 13 140 112 178 210 146 402), lower := (rows 97 259 13 140 112 32 64 128 256), losses := [] }

theorem u40034 : Upper (D 7) (R 7) [96,257,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40035 : Route 9 := (fun mask => (mask,id))

def c40035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40035 : Upper (D 7) (R 7) [96,257,9,132,130] 13 := by
  apply FastRouting.sound _ _ [96,257,9,132,130] 13 (by decide) (choices 1) [2,16,64] r40035 c40035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28448
  · exact u28449
  · exact u28450

def r40036 : Route 9 := (fun mask => (mask,id))

def c40036 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40036 : Upper (D 7) (R 7) [96,257,9,132,160] 13 := by
  apply FastRouting.sound _ _ [96,257,9,132,160] 13 (by decide) (choices 1) [2,16,64] r40036 c40036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28451
  · exact u28452
  · exact u28453

def r40037 : Route 9 := (fun mask => (mask,id))

def c40037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40037 : Upper (D 7) (R 7) [96,257,9,144,6] 13 := by
  apply FastRouting.sound _ _ [96,257,9,144,6] 13 (by decide) (choices 1) [2,64,128] r40037 c40037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28454
  · exact u28455
  · exact u28456

def r40038 : Route 9 := (fun mask => (mask,id))

def c40038 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40038 : Upper (D 7) (R 7) [96,257,9,144,34] 13 := by
  apply FastRouting.sound _ _ [96,257,9,144,34] 13 (by decide) (choices 1) [2,4,64,128] r40038 c40038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28457
  · exact u28458
  · exact u28459
  · exact u28460

def r40039 : Route 9 := (fun mask => (mask,id))

def c40039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40039 : Upper (D 7) (R 7) [96,257,9,144,36] 13 := by
  apply FastRouting.sound _ _ [96,257,9,144,36] 13 (by decide) (choices 1) [2,64,128] r40039 c40039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28461
  · exact u28462
  · exact u28463

def b40040 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 259 13 152 112 166 198 134 390), lower := (rows 97 259 13 152 112 32 64 128 256), losses := [] }

theorem u40040 : Upper (D 7) (R 7) [96,257,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40041 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 13 152 146 102 102 230 358), lower := (rows 97 259 13 152 146 32 64 128 256), losses := [] }

theorem u40041 : Upper (D 7) (R 7) [96,257,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40042 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 13 152 148 98 98 226 354), lower := (rows 97 259 13 152 148 32 64 128 256), losses := [] }

theorem u40042 : Upper (D 7) (R 7) [96,257,9,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40043 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 13 152 176 102 70 198 326), lower := (rows 97 259 13 152 176 32 64 128 256), losses := [] }

theorem u40043 : Upper (D 7) (R 7) [96,257,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40044 : Route 9 := (fun mask => (mask,id))

def c40044 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40044 : Upper (D 7) (R 7) [96,257,9,160,6] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,6] 13 (by decide) (choices 1) [2,16,64,128] r40044 c40044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28464
  · exact u28465
  · exact u28466
  · exact u28467

def r40045 : Route 9 := (fun mask => (mask,id))

def c40045 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40045 : Upper (D 7) (R 7) [96,257,9,160,66] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,66] 13 (by decide) (choices 1) [2,4,16,128] r40045 c40045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28468
  · exact u28469
  · exact u28470
  · exact u28471

def r40046 : Route 9 := (fun mask => (mask,id))

def c40046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40046 : Upper (D 7) (R 7) [96,257,9,160,68] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,68] 13 (by decide) (choices 1) [2,16,128] r40046 c40046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28472
  · exact u28473
  · exact u28474

def r40047 : Route 9 := (fun mask => (mask,id))

def c40047 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40047 : Upper (D 7) (R 7) [96,257,9,160,130] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,130] 13 (by decide) (choices 1) [2,4,16,64] r40047 c40047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28475
  · exact u28476
  · exact u28477
  · exact u28478

def b40048 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 97 259 13 168 148 114 82 210 338), lower := (rows 97 259 13 168 148 32 64 128 256), losses := [] }

theorem u40048 : Upper (D 7) (R 7) [96,257,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40049 : Route 9 := (fun mask => (mask,id))

def c40049 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40049 : Upper (D 7) (R 7) [96,257,9,160,192] 13 := by
  apply FastRouting.sound _ _ [96,257,9,160,192] 13 (by decide) (choices 1) [2,4,16] r40049 c40049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28479
  · exact u28480
  · exact u28481

def b40050 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 14 145 240 240 240 496), lower := (rows 97 259 14 14 145 32 64 128 256), losses := [] }

theorem u40050 : Upper (D 7) (R 7) [96,257,10,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40051 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 14 176 241 209 209 465), lower := (rows 97 259 14 14 176 32 64 128 256), losses := [] }

theorem u40051 : Upper (D 7) (R 7) [96,257,10,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40052 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 26 52 225 193 193 449), lower := (rows 97 259 14 26 52 32 64 128 256), losses := [] }

theorem u40052 : Upper (D 7) (R 7) [96,257,10,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40053 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 224 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 26 145 228 228 228 484), lower := (rows 97 259 14 26 145 32 64 128 256), losses := [] }

theorem u40053 : Upper (D 7) (R 7) [96,257,10,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40054 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 26 148 225 225 225 481), lower := (rows 97 259 14 26 148 32 64 128 256), losses := [] }

theorem u40054 : Upper (D 7) (R 7) [96,257,10,18,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40055 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 26 176 229 197 197 453), lower := (rows 97 259 14 26 176 32 64 128 256), losses := [] }

theorem u40055 : Upper (D 7) (R 7) [96,257,10,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40056 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 259 14 28 49 226 194 194 450), lower := (rows 97 259 14 28 49 32 64 128 256), losses := [] }

theorem u40056 : Upper (D 7) (R 7) [96,257,10,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40057 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 28 50 225 193 193 449), lower := (rows 97 259 14 28 50 32 64 128 256), losses := [] }

theorem u40057 : Upper (D 7) (R 7) [96,257,10,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40058 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 259 14 28 112 163 195 131 387), lower := (rows 97 259 14 28 112 32 64 128 256), losses := [] }

theorem u40058 : Upper (D 7) (R 7) [96,257,10,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40059 : Route 9 := (fun mask => (mask,id))

def c40059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40059 : Upper (D 7) (R 7) [96,257,10,20,129] 13 := by
  apply FastRouting.sound _ _ [96,257,10,20,129] 13 (by decide) (choices 1) [2,64,128] r40059 c40059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28482
  · exact u28483
  · exact u28484

def b40060 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 28 146 225 225 225 481), lower := (rows 97 259 14 28 146 32 64 128 256), losses := [] }

theorem u40060 : Upper (D 7) (R 7) [96,257,10,20,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40061 : Route 9 := (fun mask => (mask,id))

def c40061 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40061 : Upper (D 7) (R 7) [96,257,10,20,160] 13 := by
  apply FastRouting.sound _ _ [96,257,10,20,160] 13 (by decide) (choices 1) [1,2,64,128] r40061 c40061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28485
  · exact u28486
  · exact u28487
  · exact u28488

def b40062 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 14 41 82 180 212 148 404), lower := (rows 97 259 14 41 82 32 64 128 256), losses := [] }

theorem u40062 : Upper (D 7) (R 7) [96,257,10,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40063 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 14 41 84 178 210 146 402), lower := (rows 97 259 14 41 84 32 64 128 256), losses := [] }

theorem u40063 : Upper (D 7) (R 7) [96,257,10,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40064 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 14 41 146 244 212 212 468), lower := (rows 97 259 14 41 146 32 64 128 256), losses := [] }

theorem u40064 : Upper (D 7) (R 7) [96,257,10,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40065 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 14 41 148 242 210 210 466), lower := (rows 97 259 14 41 148 32 64 128 256), losses := [] }

theorem u40065 : Upper (D 7) (R 7) [96,257,10,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40066 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 259 14 41 208 182 214 150 406), lower := (rows 97 259 14 41 208 32 64 128 256), losses := [] }

theorem u40066 : Upper (D 7) (R 7) [96,257,10,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40067 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 42 84 177 209 145 401), lower := (rows 97 259 14 42 84 32 64 128 256), losses := [] }

theorem u40067 : Upper (D 7) (R 7) [96,257,10,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40068 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 42 145 244 212 212 468), lower := (rows 97 259 14 42 145 32 64 128 256), losses := [] }

theorem u40068 : Upper (D 7) (R 7) [96,257,10,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40069 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 42 148 241 209 209 465), lower := (rows 97 259 14 42 148 32 64 128 256), losses := [] }

theorem u40069 : Upper (D 7) (R 7) [96,257,10,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40070 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 259 14 42 208 181 213 149 405), lower := (rows 97 259 14 42 208 32 64 128 256), losses := [] }

theorem u40070 : Upper (D 7) (R 7) [96,257,10,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40071 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,6),(2,6),(3,6),(4,1)], upper := (rows 97 259 14 44 81 178 210 146 402), lower := (rows 97 259 14 44 81 32 64 128 256), losses := [] }

theorem u40071 : Upper (D 7) (R 7) [96,257,10,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40072 : Route 9 := (fun mask => (mask,id))

def c40072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40072 : Upper (D 7) (R 7) [96,257,10,36,66] 13 := by
  apply FastRouting.sound _ _ [96,257,10,36,66] 13 (by decide) (choices 1) [1,16,128] r40072 c40072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28489
  · exact u28490
  · exact u28491

def r40073 : Route 9 := (fun mask => (mask,id))

def c40073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40073 : Upper (D 7) (R 7) [96,257,10,36,129] 13 := by
  apply FastRouting.sound _ _ [96,257,10,36,129] 13 (by decide) (choices 1) [2,16,64,128] r40073 c40073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28492
  · exact u28493
  · exact u28494
  · exact u28495

def r40074 : Route 9 := (fun mask => (mask,id))

def c40074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40074 : Upper (D 7) (R 7) [96,257,10,36,130] 13 := by
  apply FastRouting.sound _ _ [96,257,10,36,130] 13 (by decide) (choices 1) [1,16,64,128] r40074 c40074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28496
  · exact u28497
  · exact u28498
  · exact u28499

def r40075 : Route 9 := (fun mask => (mask,id))

def c40075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40075 : Upper (D 7) (R 7) [96,257,10,36,192] 13 := by
  apply FastRouting.sound _ _ [96,257,10,36,192] 13 (by decide) (choices 1) [1,2,16,128] r40075 c40075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28500
  · exact u28501
  · exact u28502
  · exact u28503

def b40076 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 259 14 56 81 166 198 134 390), lower := (rows 97 259 14 56 81 32 64 128 256), losses := [] }

theorem u40076 : Upper (D 7) (R 7) [96,257,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40077 : Route 9 := (fun mask => (mask,id))

def c40077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40077 : Upper (D 7) (R 7) [96,257,10,48,66] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,66] 13 (by decide) (choices 1) [1,4,128] r40077 c40077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28504
  · exact u28505
  · exact u28506

def r40078 : Route 9 := (fun mask => (mask,id))

def c40078 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40078 : Upper (D 7) (R 7) [96,257,10,48,68] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,68] 13 (by decide) (choices 1) [1,2,128] r40078 c40078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28507
  · exact u28508
  · exact u28509

def r40079 : Route 9 := (fun mask => (mask,id))

def c40079 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40079 : Upper (D 7) (R 7) [96,257,10,48,129] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,129] 13 (by decide) (choices 1) [2,4,64,128] r40079 c40079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28510
  · exact u28511
  · exact u28512
  · exact u28513

#print axioms u40079
end Delivery.IrregularNine14.P07
