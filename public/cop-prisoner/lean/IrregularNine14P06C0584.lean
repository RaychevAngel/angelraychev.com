import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0311
import IrregularNine14P06C0312

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35040 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 133 42 84 355 323 451 323), lower := (rows 25 38 133 42 84 32 64 128 256), losses := [] }

theorem u35040 : Upper (D 6) (R 6) [24,36,129,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35041 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 38 133 42 273 102 70 198 326), lower := (rows 25 38 133 42 273 32 64 128 256), losses := [] }

theorem u35041 : Upper (D 6) (R 6) [24,36,129,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35042 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 133 42 274 101 69 197 325), lower := (rows 25 38 133 42 274 32 64 128 256), losses := [] }

theorem u35042 : Upper (D 6) (R 6) [24,36,129,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35043 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 133 42 276 99 67 195 323), lower := (rows 25 38 133 42 276 32 64 128 256), losses := [] }

theorem u35043 : Upper (D 6) (R 6) [24,36,129,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35044 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 133 42 336 103 71 199 327), lower := (rows 25 38 133 42 336 32 64 128 256), losses := [] }

theorem u35044 : Upper (D 6) (R 6) [24,36,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35045 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 362, targets := 1 },{ cop := 1, region := 8, targets := 2 }], pairs := [(1,0),(3,0),(3,1)], upper := (rows 25 38 133 44 81 354 322 450 322), lower := (rows 25 38 133 44 81 32 64 128 256), losses := [] }

theorem u35045 : Upper (D 6) (R 6) [24,36,129,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35046 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 133 44 82 355 323 451 323), lower := (rows 25 38 133 44 82 32 64 128 256), losses := [] }

theorem u35046 : Upper (D 6) (R 6) [24,36,129,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35047 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 1, region := 8, targets := 2 }], pairs := [(1,0),(3,0),(3,1)], upper := (rows 25 38 133 44 273 98 66 194 322), lower := (rows 25 38 133 44 273 32 64 128 256), losses := [] }

theorem u35047 : Upper (D 6) (R 6) [24,36,129,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35048 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 133 44 274 99 67 195 323), lower := (rows 25 38 133 44 274 32 64 128 256), losses := [] }

theorem u35048 : Upper (D 6) (R 6) [24,36,129,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35049 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 133 44 336 99 67 195 323), lower := (rows 25 38 133 44 336 32 64 128 256), losses := [] }

theorem u35049 : Upper (D 6) (R 6) [24,36,129,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35050 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 133 73 82 294 358 422 294), lower := (rows 25 38 133 73 82 32 64 128 256), losses := [] }

theorem u35050 : Upper (D 6) (R 6) [24,36,129,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35051 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 133 73 84 290 354 418 290), lower := (rows 25 38 133 73 84 32 64 128 256), losses := [] }

theorem u35051 : Upper (D 6) (R 6) [24,36,129,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35052 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 133 73 112 294 326 390 262), lower := (rows 25 38 133 73 112 32 64 128 256), losses := [] }

theorem u35052 : Upper (D 6) (R 6) [24,36,129,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35053 : Route 9 := (fun mask => (mask,id))

def c35053 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35053 : Upper (D 6) (R 6) [24,36,129,65,258] 13 := by
  apply FastRouting.sound _ _ [24,36,129,65,258] 13 (by decide) (choices 1) [2,4,64] r35053 c35053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18684
  · exact u18685
  · exact u18686

def r35054 : Route 9 := (fun mask => (mask,id))

def c35054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35054 : Upper (D 6) (R 6) [24,36,129,65,260] 13 := by
  apply FastRouting.sound _ _ [24,36,129,65,260] 13 (by decide) (choices 1) [2,64] r35054 c35054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18687
  · exact u18688

def r35055 : Route 9 := (fun mask => (mask,id))

def c35055 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35055 : Upper (D 6) (R 6) [24,36,129,65,288] 13 := by
  apply FastRouting.sound _ _ [24,36,129,65,288] 13 (by decide) (choices 1) [2,4,64] r35055 c35055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18689
  · exact u18690
  · exact u18691

def b35056 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 133 73 336 38 102 166 294), lower := (rows 25 38 133 73 336 32 64 128 256), losses := [] }

theorem u35056 : Upper (D 6) (R 6) [24,36,129,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35057 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 38 133 74 82 293 357 421 293), lower := (rows 25 38 133 74 82 32 64 128 256), losses := [] }

theorem u35057 : Upper (D 6) (R 6) [24,36,129,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35058 : Route 9 := (fun mask => (mask,id))

def c35058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35058 : Upper (D 6) (R 6) [24,36,129,66,68] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,68] 13 (by decide) (choices 1) [1,2,256] r35058 c35058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18692
  · exact u18693
  · exact u18694

def r35059 : Route 9 := (fun mask => (mask,id))

def c35059 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35059 : Upper (D 6) (R 6) [24,36,129,66,96] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,96] 13 (by decide) (choices 1) [1,2,4,256] r35059 c35059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18695
  · exact u18696
  · exact u18697
  · exact u18698

def r35060 : Route 9 := (fun mask => (mask,id))

def c35060 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35060 : Upper (D 6) (R 6) [24,36,129,66,257] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,257] 13 (by decide) (choices 1) [2,4,64] r35060 c35060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18699
  · exact u18700
  · exact u18701

def r35061 : Route 9 := (fun mask => (mask,id))

def c35061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35061 : Upper (D 6) (R 6) [24,36,129,66,258] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,258] 13 (by decide) (choices 1) [1,4,64] r35061 c35061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18702
  · exact u18703
  · exact u18704

def r35062 : Route 9 := (fun mask => (mask,id))

def c35062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35062 : Upper (D 6) (R 6) [24,36,129,66,260] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,260] 13 (by decide) (choices 1) [1,2,64] r35062 c35062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18705
  · exact u18706
  · exact u18707

def r35063 : Route 9 := (fun mask => (mask,id))

def c35063 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35063 : Upper (D 6) (R 6) [24,36,129,66,288] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,288] 13 (by decide) (choices 1) [1,2,4,64] r35063 c35063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18708
  · exact u18709
  · exact u18710
  · exact u18711

def r35064 : Route 9 := (fun mask => (mask,id))

def c35064 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35064 : Upper (D 6) (R 6) [24,36,129,66,320] 13 := by
  apply FastRouting.sound _ _ [24,36,129,66,320] 13 (by decide) (choices 1) [1,2,4] r35064 c35064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18712
  · exact u18713
  · exact u18714

def r35065 : Route 9 := (fun mask => (mask,id))

def c35065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35065 : Upper (D 6) (R 6) [24,36,129,68,96] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,96] 13 (by decide) (choices 1) [1,2,256] r35065 c35065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18715
  · exact u18716
  · exact u18717

def r35066 : Route 9 := (fun mask => (mask,id))

def c35066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35066 : Upper (D 6) (R 6) [24,36,129,68,257] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,257] 13 (by decide) (choices 1) [2,64] r35066 c35066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18718
  · exact u18719

def r35067 : Route 9 := (fun mask => (mask,id))

def c35067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35067 : Upper (D 6) (R 6) [24,36,129,68,258] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,258] 13 (by decide) (choices 1) [1,2,64] r35067 c35067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18720
  · exact u18721
  · exact u18722

def r35068 : Route 9 := (fun mask => (mask,id))

def c35068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35068 : Upper (D 6) (R 6) [24,36,129,68,288] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,288] 13 (by decide) (choices 1) [1,2,64] r35068 c35068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18723
  · exact u18724
  · exact u18725

def r35069 : Route 9 := (fun mask => (mask,id))

def c35069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35069 : Upper (D 6) (R 6) [24,36,129,68,320] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,320] 13 (by decide) (choices 1) [1,2] r35069 c35069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18726
  · exact u18727

def r35070 : Route 9 := (fun mask => (mask,id))

def c35070 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35070 : Upper (D 6) (R 6) [24,36,129,96,257] 13 := by
  apply FastRouting.sound _ _ [24,36,129,96,257] 13 (by decide) (choices 1) [2,4,64] r35070 c35070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18728
  · exact u18729
  · exact u18730

def r35071 : Route 9 := (fun mask => (mask,id))

def c35071 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35071 : Upper (D 6) (R 6) [24,36,129,96,258] 13 := by
  apply FastRouting.sound _ _ [24,36,129,96,258] 13 (by decide) (choices 1) [1,2,4,64] r35071 c35071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18731
  · exact u18732
  · exact u18733
  · exact u18734

def r35072 : Route 9 := (fun mask => (mask,id))

def c35072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35072 : Upper (D 6) (R 6) [24,36,129,96,260] 13 := by
  apply FastRouting.sound _ _ [24,36,129,96,260] 13 (by decide) (choices 1) [1,2,64] r35072 c35072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18735
  · exact u18736
  · exact u18737

def r35073 : Route 9 := (fun mask => (mask,id))

def c35073 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35073 : Upper (D 6) (R 6) [24,36,129,96,320] 13 := by
  apply FastRouting.sound _ _ [24,36,129,96,320] 13 (by decide) (choices 1) [1,2,4] r35073 c35073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18738
  · exact u18739
  · exact u18740

def b35074 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 134 11 21 352 352 480 352), lower := (rows 25 38 134 11 21 32 64 128 256), losses := [] }

theorem u35074 : Upper (D 6) (R 6) [24,36,130,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35075 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 134 11 49 356 324 452 324), lower := (rows 25 38 134 11 49 32 64 128 256), losses := [] }

theorem u35075 : Upper (D 6) (R 6) [24,36,130,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35076 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 134 11 52 353 321 449 321), lower := (rows 25 38 134 11 52 32 64 128 256), losses := [] }

theorem u35076 : Upper (D 6) (R 6) [24,36,130,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35077 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 11 81 356 356 484 356), lower := (rows 25 38 134 11 81 32 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 38 70 134 262), good := (rows 25 484 484 505 81 32 64 128 256) }] }

theorem u35077 : Upper (D 6) (R 6) [24,36,130,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35078 : Route 9 := (fun mask => (mask,id))

def c35078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35078 : Upper (D 6) (R 6) [24,36,130,3,68] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,68] 13 (by decide) (choices 1) [1,64,256] r35078 c35078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18741
  · exact u18742
  · exact u18743

def r35079 : Route 9 := (fun mask => (mask,id))

def c35079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35079 : Upper (D 6) (R 6) [24,36,130,3,96] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,96] 13 (by decide) (choices 1) [1,4,64,256] r35079 c35079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18744
  · exact u18745
  · exact u18746
  · exact u18747

def b35080 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 230, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 11 273 100 100 228 356), lower := (rows 25 38 134 11 273 32 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 38 70 134 262), good := (rows 25 484 484 505 273 32 64 128 256) }] }

theorem u35080 : Upper (D 6) (R 6) [24,36,130,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35081 : Route 9 := (fun mask => (mask,id))

def c35081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35081 : Upper (D 6) (R 6) [24,36,130,3,260] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,260] 13 (by decide) (choices 1) [1,64] r35081 c35081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18748
  · exact u18749

def r35082 : Route 9 := (fun mask => (mask,id))

def c35082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35082 : Upper (D 6) (R 6) [24,36,130,3,288] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,288] 13 (by decide) (choices 1) [1,4,64] r35082 c35082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18750
  · exact u18751
  · exact u18752

def r35083 : Route 9 := (fun mask => (mask,id))

def c35083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35083 : Upper (D 6) (R 6) [24,36,130,3,320] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,320] 13 (by decide) (choices 1) [1,4,64] r35083 c35083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18753
  · exact u18754
  · exact u18755

def b35084 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 25, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 134 13 49 354 322 450 322), lower := (rows 25 38 134 13 49 32 64 128 256), losses := [] }

theorem u35084 : Upper (D 6) (R 6) [24,36,130,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35085 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 134 13 50 353 321 449 321), lower := (rows 25 38 134 13 50 32 64 128 256), losses := [] }

theorem u35085 : Upper (D 6) (R 6) [24,36,130,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35086 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 486, targets := 1 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 25 38 134 13 81 354 354 482 354), lower := (rows 25 38 134 13 81 32 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 24 38 70 134 262), good := (rows 25 482 482 505 81 32 64 128 256) }] }

theorem u35086 : Upper (D 6) (R 6) [24,36,130,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35087 : Route 9 := (fun mask => (mask,id))

def c35087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35087 : Upper (D 6) (R 6) [24,36,130,5,66] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,66] 13 (by decide) (choices 1) [1,64,256] r35087 c35087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18756
  · exact u18757
  · exact u18758

def r35088 : Route 9 := (fun mask => (mask,id))

def c35088 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35088 : Upper (D 6) (R 6) [24,36,130,5,96] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,96] 13 (by decide) (choices 1) [1,2,64,256] r35088 c35088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18759
  · exact u18760
  · exact u18761
  · exact u18762

def b35089 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 230, targets := 1 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 25 38 134 13 273 98 98 226 354), lower := (rows 25 38 134 13 273 32 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 24 38 70 134 262), good := (rows 25 482 482 505 273 32 64 128 256) }] }

theorem u35089 : Upper (D 6) (R 6) [24,36,130,5,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35090 : Route 9 := (fun mask => (mask,id))

def c35090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35090 : Upper (D 6) (R 6) [24,36,130,5,258] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,258] 13 (by decide) (choices 1) [1,64] r35090 c35090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18763
  · exact u18764

def r35091 : Route 9 := (fun mask => (mask,id))

def c35091 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35091 : Upper (D 6) (R 6) [24,36,130,5,288] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,288] 13 (by decide) (choices 1) [1,2,64] r35091 c35091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18765
  · exact u18766
  · exact u18767

def r35092 : Route 9 := (fun mask => (mask,id))

def c35092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35092 : Upper (D 6) (R 6) [24,36,130,5,320] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,320] 13 (by decide) (choices 1) [1,2,64] r35092 c35092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18768
  · exact u18769
  · exact u18770

def b35093 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 369, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 14 49 353 321 449 321), lower := (rows 25 38 134 14 49 32 64 128 256), losses := [] }

theorem u35093 : Upper (D 6) (R 6) [24,36,130,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35094 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 369, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 14 81 353 353 481 353), lower := (rows 25 38 134 14 81 32 64 128 256), losses := [] }

theorem u35094 : Upper (D 6) (R 6) [24,36,130,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35095 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 369, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 14 112 353 321 449 321), lower := (rows 25 38 134 14 112 32 64 128 256), losses := [] }

theorem u35095 : Upper (D 6) (R 6) [24,36,130,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35096 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 369, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 14 273 97 97 225 353), lower := (rows 25 38 134 14 273 32 64 128 256), losses := [] }

theorem u35096 : Upper (D 6) (R 6) [24,36,130,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35097 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 369, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 14 304 97 65 193 321), lower := (rows 25 38 134 14 304 32 64 128 256), losses := [] }

theorem u35097 : Upper (D 6) (R 6) [24,36,130,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35098 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 369, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 14 336 97 97 225 353), lower := (rows 25 38 134 14 336 32 64 128 256), losses := [] }

theorem u35098 : Upper (D 6) (R 6) [24,36,130,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35099 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 134 41 81 358 326 454 326), lower := (rows 25 38 134 41 81 32 64 128 256), losses := [] }

theorem u35099 : Upper (D 6) (R 6) [24,36,130,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35099
end Delivery.IrregularNine14.P06
