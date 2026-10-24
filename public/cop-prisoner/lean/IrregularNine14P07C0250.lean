import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0046

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15000 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 48, targets := 192 },{ cop := 4, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(4,6),(4,7)], upper := (rows 7 266 100 137 50 33 208 208 464), lower := (rows 7 266 100 137 50 33 64 128 256), losses := [] }

theorem u15000 : Upper (D 7) (R 7) [6,264,96,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15001 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 }], pairs := [(4,0),(4,6),(4,7)], upper := (rows 7 266 100 137 50 48 193 193 449), lower := (rows 7 266 100 137 50 48 64 128 256), losses := [] }

theorem u15001 : Upper (D 7) (R 7) [6,264,96,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15001 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15002 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 137 50 96 209 145 401), lower := (rows 7 266 100 137 50 96 64 128 256), losses := [] }

theorem u15002 : Upper (D 7) (R 7) [6,264,96,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15003 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,6)], upper := (rows 7 266 100 137 50 160 81 209 337), lower := (rows 7 266 100 137 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 22 314 100 168 50 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 18 168 0 128 256), good := (rows 23 314 36 169 50 160 0 160 256) }] }

theorem u15003 : Upper (D 7) (R 7) [6,264,96,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15004 : Route 9 := (fun mask => (mask,id))

def c15004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15004 : Upper (D 7) (R 7) [6,264,96,129,130,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129,130,1] 13 (by decide) (choices 1) [16,32] r15004 c15004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2783
  · exact u2784

theorem m15005_1 : Upper (D 7) (R 7) [6,264,96,129,130,16,1] 13 :=
  permutation_upper _ _ _ [6,264,96,129,130,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2783

def r15005 : Route 9 := (fun mask => (mask,id))

def c15005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15005 : Upper (D 7) (R 7) [6,264,96,129,130,16] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129,130,16] 13 (by decide) (choices 1) [1,32] r15005 c15005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m15005_1
  · exact u2785

def b15006 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 137 146 96 113 177 305), lower := (rows 7 266 100 137 146 96 64 128 256), losses := [] }

theorem u15006 : Upper (D 7) (R 7) [6,264,96,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15007 : Route 9 := (fun mask => (mask,id))

def c15007 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15007 : Upper (D 7) (R 7) [6,264,96,129,160,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129,160,1] 13 (by decide) (choices 1) [2,16] r15007 c15007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2786
  · exact u2787

def r15008 : Route 9 := (fun mask => (mask,id))

def c15008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15008 : Upper (D 7) (R 7) [6,264,96,129,160,2] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129,160,2] 13 (by decide) (choices 1) [1,16] r15008 c15008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2788
  · exact u2789

def b15009 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 100 137 176 48 67 195 323), lower := (rows 7 266 100 137 176 48 64 128 256), losses := [] }

theorem u15009 : Upper (D 7) (R 7) [6,264,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15009 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15010 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 137 176 96 83 147 275), lower := (rows 7 266 100 137 176 96 64 128 256), losses := [] }

theorem u15010 : Upper (D 7) (R 7) [6,264,96,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15011 : Route 9 := (fun mask => (mask,id))

def c15011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15011 : Upper (D 7) (R 7) [6,264,96,130,129,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,130,129,1] 13 (by decide) (choices 1) [16,32] r15011 c15011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2790
  · exact u2791

def b15012 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 100, targets := 128 }], pairs := [(2,1),(2,7),(4,1)], upper := (rows 7 266 100 138 145 48 97 225 353), lower := (rows 7 266 100 138 145 48 64 128 256), losses := [] }

theorem u15012 : Upper (D 7) (R 7) [6,264,96,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15012 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15013 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 138 145 96 113 177 305), lower := (rows 7 266 100 138 145 96 64 128 256), losses := [] }

theorem u15013 : Upper (D 7) (R 7) [6,264,96,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15014 : Route 9 := (fun mask => (mask,id))

def c15014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15014 : Upper (D 7) (R 7) [6,264,96,130,160,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,130,160,1] 13 (by decide) (choices 1) [1,16] r15014 c15014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2792
  · exact u2793

def b15015 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 100 138 176 48 65 193 321), lower := (rows 7 266 100 138 176 48 64 128 256), losses := [] }

theorem u15015 : Upper (D 7) (R 7) [6,264,96,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15015 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15016 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 138 176 96 81 145 273), lower := (rows 7 266 100 138 176 96 64 128 256), losses := [] }

theorem u15016 : Upper (D 7) (R 7) [6,264,96,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15017 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 7 266 100 152 49 33 194 194 450), lower := (rows 7 266 100 152 49 33 64 128 256), losses := [] }

theorem u15017 : Upper (D 7) (R 7) [6,264,96,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15018 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 48, targets := 192 },{ cop := 4, region := 204, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 266 100 152 49 34 193 193 449), lower := (rows 7 266 100 152 49 34 64 128 256), losses := [] }

theorem u15018 : Upper (D 7) (R 7) [6,264,96,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15019 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 152 49 96 195 131 387), lower := (rows 7 266 100 152 49 96 64 128 256), losses := [] }

theorem u15019 : Upper (D 7) (R 7) [6,264,96,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15020 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,5)], upper := (rows 7 266 100 152 49 160 67 195 323), lower := (rows 7 266 100 152 49 160 64 128 256), losses := [{ target := 7, region := (rows 9 10 20 8 16 32 75 0 267), good := (rows 327 331 100 351 373 32 64 0 256) }] }

theorem u15020 : Upper (D 7) (R 7) [6,264,96,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15021 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 48, targets := 192 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 266 100 152 50 33 193 193 449), lower := (rows 7 266 100 152 50 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 53 24 16 33 97 161 289), good := (rows 485 264 484 156 508 485 64 128 256) }] }

theorem u15021 : Upper (D 7) (R 7) [6,264,96,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15022 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 152 50 96 193 129 385), lower := (rows 7 266 100 152 50 96 64 128 256), losses := [] }

theorem u15022 : Upper (D 7) (R 7) [6,264,96,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15023 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 69, targets := 128 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,0)], upper := (rows 7 266 100 152 50 160 65 193 321), lower := (rows 7 266 100 152 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 22 314 100 184 50 160 64 160 256) }] }

theorem u15023 : Upper (D 7) (R 7) [6,264,96,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15024 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 36, targets := 130 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(2,7),(3,6)], upper := (rows 7 266 100 168 81 33 210 146 402), lower := (rows 7 266 100 168 81 33 64 128 256), losses := [] }

theorem u15024 : Upper (D 7) (R 7) [6,264,96,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15025 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6),(4,1),(4,5)], upper := (rows 7 266 100 168 81 34 209 145 401), lower := (rows 7 266 100 168 81 34 64 128 256), losses := [] }

theorem u15025 : Upper (D 7) (R 7) [6,264,96,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15026 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 266 100 168 81 48 195 131 387), lower := (rows 7 266 100 168 81 48 64 128 256), losses := [] }

theorem u15026 : Upper (D 7) (R 7) [6,264,96,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15026 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15027 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 266 100 168 81 160 83 147 275), lower := (rows 7 266 100 168 81 160 64 128 256), losses := [] }

theorem u15027 : Upper (D 7) (R 7) [6,264,96,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15028 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 37, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 7 266 100 168 82 33 209 145 401), lower := (rows 7 266 100 168 82 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 97 161 289), good := (rows 471 282 452 474 82 465 64 128 256) }] }

theorem u15028 : Upper (D 7) (R 7) [6,264,96,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15029 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 266 100 168 82 48 193 129 385), lower := (rows 7 266 100 168 82 48 64 128 256), losses := [] }

theorem u15029 : Upper (D 7) (R 7) [6,264,96,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15029 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15030 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 266 100 168 82 160 81 145 273), lower := (rows 7 266 100 168 82 160 64 128 256), losses := [] }

theorem u15030 : Upper (D 7) (R 7) [6,264,96,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15031 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(4,5)], upper := (rows 7 266 100 168 145 33 82 210 338), lower := (rows 7 266 100 168 145 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 49 0 73 137 265), good := (rows 471 458 84 474 465 465 64 128 256) }] }

theorem u15031 : Upper (D 7) (R 7) [6,264,96,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15032 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(3,0),(3,6),(4,1),(4,5)], upper := (rows 7 266 100 168 145 34 81 209 337), lower := (rows 7 266 100 168 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 38 298 100 168 184 34 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 35 0 128 256), good := (rows 39 298 36 168 185 34 0 128 256) }] }

theorem u15032 : Upper (D 7) (R 7) [6,264,96,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15033 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 266 100 168 145 48 67 195 323), lower := (rows 7 266 100 168 145 48 64 128 256), losses := [] }

theorem u15033 : Upper (D 7) (R 7) [6,264,96,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15033 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15034 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 168 145 96 83 147 275), lower := (rows 7 266 100 168 145 96 64 128 256), losses := [] }

theorem u15034 : Upper (D 7) (R 7) [6,264,96,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15035 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 7 266 100 168 146 33 81 209 337), lower := (rows 7 266 100 168 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 97 161 289), good := (rows 471 282 452 474 146 465 64 128 256) }] }

theorem u15035 : Upper (D 7) (R 7) [6,264,96,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15036 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 266 100 168 146 48 65 193 321), lower := (rows 7 266 100 168 146 48 64 128 256), losses := [] }

theorem u15036 : Upper (D 7) (R 7) [6,264,96,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15036 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15037 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 168 146 96 81 145 273), lower := (rows 7 266 100 168 146 96 64 128 256), losses := [] }

theorem u15037 : Upper (D 7) (R 7) [6,264,96,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15038 : Route 9 := (fun mask => (mask,id))

def c15038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15038 : Upper (D 7) (R 7) [6,264,96,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,160,192,1] 13 (by decide) (choices 1) [1,2,16] r15038 c15038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2794
  · exact u2795
  · exact u2796

def r15039 : Route 9 := (fun mask => (mask,id))

def c15039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15039 : Upper (D 7) (R 7) [6,264,96,160,192,2] 13 := by
  apply FastRouting.sound _ _ [6,264,96,160,192,2] 13 (by decide) (choices 1) [1,16] r15039 c15039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2797
  · exact u2798

def b15040 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 266 100 168 208 48 67 131 259), lower := (rows 7 266 100 168 208 48 64 128 256), losses := [] }

theorem u15040 : Upper (D 7) (R 7) [6,264,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15040 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15041 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 290 13 56 81 34 192 192 448), lower := (rows 7 290 13 56 81 34 64 128 256), losses := [] }

theorem u15041 : Upper (D 7) (R 7) [6,288,9,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15042 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 44, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 7 290 13 56 81 96 194 130 386), lower := (rows 7 290 13 56 81 96 64 128 256), losses := [] }

theorem u15042 : Upper (D 7) (R 7) [6,288,9,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15043 : Route 9 := (fun mask => (mask,id))

def c15043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15043 : Upper (D 7) (R 7) [6,288,9,48,65,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,48,65,128] 13 (by decide) (choices 1) [2,128] r15043 c15043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2799
  · exact u2800

def b15044 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 13 56 82 33 192 192 448), lower := (rows 7 290 13 56 82 33 64 128 256), losses := [] }

theorem u15044 : Upper (D 7) (R 7) [6,288,9,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15045 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 45, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 7 290 13 56 82 96 193 129 385), lower := (rows 7 290 13 56 82 96 64 128 256), losses := [] }

theorem u15045 : Upper (D 7) (R 7) [6,288,9,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15046 : Route 9 := (fun mask => (mask,id))

def c15046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15046 : Upper (D 7) (R 7) [6,288,9,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,48,66,128] 13 (by decide) (choices 1) [1,128] r15046 c15046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2801
  · exact u2802

def b15047 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 290 13 56 208 33 194 194 450), lower := (rows 7 290 13 56 208 33 64 128 256), losses := [] }

theorem u15047 : Upper (D 7) (R 7) [6,288,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15048 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 13 56 208 34 193 193 449), lower := (rows 7 290 13 56 208 34 64 128 256), losses := [] }

theorem u15048 : Upper (D 7) (R 7) [6,288,9,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15049 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 290 13 56 208 96 195 131 387), lower := (rows 7 290 13 56 208 96 64 128 256), losses := [] }

theorem u15049 : Upper (D 7) (R 7) [6,288,9,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15050 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 290 13 88 145 34 224 224 480), lower := (rows 7 290 13 88 145 34 64 128 256), losses := [] }

theorem u15050 : Upper (D 7) (R 7) [6,288,9,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15051 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 7 290 13 88 145 96 226 162 418), lower := (rows 7 290 13 88 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 34 4 8 17 32 0 162 290), good := (rows 407 418 29 24 145 418 0 128 256) }] }

theorem u15051 : Upper (D 7) (R 7) [6,288,9,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15052 : Route 9 := (fun mask => (mask,id))

def c15052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15052 : Upper (D 7) (R 7) [6,288,9,80,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,129,128] 13 (by decide) (choices 1) [2,32] r15052 c15052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2803
  · exact u2804

def b15053 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 290 13 88 146 33 224 224 480), lower := (rows 7 290 13 88 146 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 103 167 295), good := (rows 485 480 493 88 472 481 64 128 256) }] }

theorem u15053 : Upper (D 7) (R 7) [6,288,9,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15054 : Route 9 := (fun mask => (mask,id))

def c15054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15054 : Upper (D 7) (R 7) [6,288,9,80,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,130,64] 13 (by decide) (choices 1) [1,32,128] r15054 c15054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2805
  · exact u2806
  · exact u2807

def r15055 : Route 9 := (fun mask => (mask,id))

def c15055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15055 : Upper (D 7) (R 7) [6,288,9,80,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,130,128] 13 (by decide) (choices 1) [1,32] r15055 c15055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2808
  · exact u2809

def r15056 : Route 9 := (fun mask => (mask,id))

def c15056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15056 : Upper (D 7) (R 7) [6,288,9,80,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,160,1] 13 (by decide) (choices 1) [2,128] r15056 c15056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2810
  · exact u2811

def r15057 : Route 9 := (fun mask => (mask,id))

def c15057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15057 : Upper (D 7) (R 7) [6,288,9,80,160,2] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,160,2] 13 (by decide) (choices 1) [1,128] r15057 c15057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2812
  · exact u2813

def r15058 : Route 9 := (fun mask => (mask,id))

def c15058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15058 : Upper (D 7) (R 7) [6,288,9,80,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,160,64] 13 (by decide) (choices 1) [1,2,128] r15058 c15058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2814
  · exact u2815
  · exact u2816

def b15059 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 13 88 176 160 67 195 323), lower := (rows 7 290 13 88 176 160 64 128 256), losses := [] }

theorem u15059 : Upper (D 7) (R 7) [6,288,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15059
end Delivery.IrregularNine14.P07
