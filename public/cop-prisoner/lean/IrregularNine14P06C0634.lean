import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0394
import IrregularNine14P06C0395
import IrregularNine14P06C0396

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38040 : Route 9 := (fun mask => (mask,id))

def c38040 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38040 : Upper (D 6) (R 6) [34,136,48,65,260] 13 := by
  apply FastRouting.sound _ _ [34,136,48,65,260] 13 (by decide) (choices 1) [1,2,4,64] r38040 c38040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23672
  · exact u23673
  · exact u23674
  · exact u23675

def r38041 : Route 9 := (fun mask => (mask,id))

def c38041 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38041 : Upper (D 6) (R 6) [34,136,48,65,320] 13 := by
  apply FastRouting.sound _ _ [34,136,48,65,320] 13 (by decide) (choices 1) [1,2,4] r38041 c38041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23676
  · exact u23677
  · exact u23678

def b38042 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 20, targets := 2 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 74 21 357 325 453 325), lower := (rows 35 138 52 74 21 32 64 128 256), losses := [] }

theorem u38042 : Upper (D 6) (R 6) [34,136,48,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38043 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 74 81 293 325 389 261), lower := (rows 35 138 52 74 81 32 64 128 256), losses := [] }

theorem u38043 : Upper (D 6) (R 6) [34,136,48,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38044 : Route 9 := (fun mask => (mask,id))

def c38044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38044 : Upper (D 6) (R 6) [34,136,48,66,68] 13 := by
  apply FastRouting.sound _ _ [34,136,48,66,68] 13 (by decide) (choices 1) [1,4,256] r38044 c38044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23679
  · exact u23680
  · exact u23681

def r38045 : Route 9 := (fun mask => (mask,id))

def c38045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38045 : Upper (D 6) (R 6) [34,136,48,66,257] 13 := by
  apply FastRouting.sound _ _ [34,136,48,66,257] 13 (by decide) (choices 1) [1,4,64] r38045 c38045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23682
  · exact u23683
  · exact u23684

def r38046 : Route 9 := (fun mask => (mask,id))

def c38046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38046 : Upper (D 6) (R 6) [34,136,48,66,260] 13 := by
  apply FastRouting.sound _ _ [34,136,48,66,260] 13 (by decide) (choices 1) [1,4,64] r38046 c38046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23685
  · exact u23686
  · exact u23687

def r38047 : Route 9 := (fun mask => (mask,id))

def c38047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38047 : Upper (D 6) (R 6) [34,136,48,66,320] 13 := by
  apply FastRouting.sound _ _ [34,136,48,66,320] 13 (by decide) (choices 1) [1,4] r38047 c38047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23688
  · exact u23689

def b38048 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 35 138 52 76 19 357 325 453 325), lower := (rows 35 138 52 76 19 32 64 128 256), losses := [] }

theorem u38048 : Upper (D 6) (R 6) [34,136,48,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38049 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 76 21 355 323 451 323), lower := (rows 35 138 52 76 21 32 64 128 256), losses := [] }

theorem u38049 : Upper (D 6) (R 6) [34,136,48,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38050 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 20, targets := 1 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 35 138 52 76 22 353 321 449 321), lower := (rows 35 138 52 76 22 32 64 128 256), losses := [] }

theorem u38050 : Upper (D 6) (R 6) [34,136,48,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38051 : Route 9 := (fun mask => (mask,id))

def c38051 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38051 : Upper (D 6) (R 6) [34,136,48,68,65] 13 := by
  apply FastRouting.sound _ _ [34,136,48,68,65] 13 (by decide) (choices 1) [1,2,4,256] r38051 c38051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23690
  · exact u23691
  · exact u23692
  · exact u23693

def b38052 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 52 76 82 293 325 389 261), lower := (rows 35 138 52 76 82 32 64 128 256), losses := [] }

theorem u38052 : Upper (D 6) (R 6) [34,136,48,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38053 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 52 76 84 291 323 387 259), lower := (rows 35 138 52 76 84 32 64 128 256), losses := [] }

theorem u38053 : Upper (D 6) (R 6) [34,136,48,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38054 : Route 9 := (fun mask => (mask,id))

def c38054 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38054 : Upper (D 6) (R 6) [34,136,48,68,257] 13 := by
  apply FastRouting.sound _ _ [34,136,48,68,257] 13 (by decide) (choices 1) [1,2,4,64] r38054 c38054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23694
  · exact u23695
  · exact u23696
  · exact u23697

def r38055 : Route 9 := (fun mask => (mask,id))

def c38055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38055 : Upper (D 6) (R 6) [34,136,48,68,258] 13 := by
  apply FastRouting.sound _ _ [34,136,48,68,258] 13 (by decide) (choices 1) [1,4,64] r38055 c38055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23698
  · exact u23699
  · exact u23700

def r38056 : Route 9 := (fun mask => (mask,id))

def c38056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38056 : Upper (D 6) (R 6) [34,136,48,68,260] 13 := by
  apply FastRouting.sound _ _ [34,136,48,68,260] 13 (by decide) (choices 1) [1,2,64] r38056 c38056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23701
  · exact u23702
  · exact u23703

def r38057 : Route 9 := (fun mask => (mask,id))

def c38057 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38057 : Upper (D 6) (R 6) [34,136,48,68,320] 13 := by
  apply FastRouting.sound _ _ [34,136,48,68,320] 13 (by decide) (choices 1) [1,2,4] r38057 c38057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23704
  · exact u23705
  · exact u23706

def b38058 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 35 138 52 265 19 100 68 196 324), lower := (rows 35 138 52 265 19 32 64 128 256), losses := [] }

theorem u38058 : Upper (D 6) (R 6) [34,136,48,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38059 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 265 21 102 70 198 326), lower := (rows 35 138 52 265 21 32 64 128 256), losses := [] }

theorem u38059 : Upper (D 6) (R 6) [34,136,48,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38060 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 20, targets := 1 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 35 138 52 265 22 101 69 197 325), lower := (rows 35 138 52 265 22 32 64 128 256), losses := [] }

theorem u38060 : Upper (D 6) (R 6) [34,136,48,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38061 : Route 9 := (fun mask => (mask,id))

def c38061 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38061 : Upper (D 6) (R 6) [34,136,48,257,65] 13 := by
  apply FastRouting.sound _ _ [34,136,48,257,65] 13 (by decide) (choices 1) [2,4,64] r38061 c38061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23707
  · exact u23708
  · exact u23709

def r38062 : Route 9 := (fun mask => (mask,id))

def c38062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38062 : Upper (D 6) (R 6) [34,136,48,257,66] 13 := by
  apply FastRouting.sound _ _ [34,136,48,257,66] 13 (by decide) (choices 1) [1,4,64] r38062 c38062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23710
  · exact u23711
  · exact u23712

def r38063 : Route 9 := (fun mask => (mask,id))

def c38063 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38063 : Upper (D 6) (R 6) [34,136,48,257,68] 13 := by
  apply FastRouting.sound _ _ [34,136,48,257,68] 13 (by decide) (choices 1) [1,2,4,64] r38063 c38063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23713
  · exact u23714
  · exact u23715
  · exact u23716

def b38064 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 20, targets := 2 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 266 21 101 69 197 325), lower := (rows 35 138 52 266 21 32 64 128 256), losses := [] }

theorem u38064 : Upper (D 6) (R 6) [34,136,48,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38065 : Route 9 := (fun mask => (mask,id))

def c38065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38065 : Upper (D 6) (R 6) [34,136,48,258,65] 13 := by
  apply FastRouting.sound _ _ [34,136,48,258,65] 13 (by decide) (choices 1) [1,4,64] r38065 c38065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23717
  · exact u23718
  · exact u23719

def r38066 : Route 9 := (fun mask => (mask,id))

def c38066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38066 : Upper (D 6) (R 6) [34,136,48,258,68] 13 := by
  apply FastRouting.sound _ _ [34,136,48,258,68] 13 (by decide) (choices 1) [1,4,64] r38066 c38066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23720
  · exact u23721
  · exact u23722

def b38067 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 35 138 52 268 19 101 69 197 325), lower := (rows 35 138 52 268 19 32 64 128 256), losses := [] }

theorem u38067 : Upper (D 6) (R 6) [34,136,48,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38068 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 268 21 99 67 195 323), lower := (rows 35 138 52 268 21 32 64 128 256), losses := [] }

theorem u38068 : Upper (D 6) (R 6) [34,136,48,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38069 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 20, targets := 1 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 35 138 52 268 22 97 65 193 321), lower := (rows 35 138 52 268 22 32 64 128 256), losses := [] }

theorem u38069 : Upper (D 6) (R 6) [34,136,48,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38070 : Route 9 := (fun mask => (mask,id))

def c38070 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38070 : Upper (D 6) (R 6) [34,136,48,260,65] 13 := by
  apply FastRouting.sound _ _ [34,136,48,260,65] 13 (by decide) (choices 1) [1,2,4,64] r38070 c38070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23723
  · exact u23724
  · exact u23725
  · exact u23726

def r38071 : Route 9 := (fun mask => (mask,id))

def c38071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38071 : Upper (D 6) (R 6) [34,136,48,260,66] 13 := by
  apply FastRouting.sound _ _ [34,136,48,260,66] 13 (by decide) (choices 1) [1,4,64] r38071 c38071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23727
  · exact u23728
  · exact u23729

def r38072 : Route 9 := (fun mask => (mask,id))

def c38072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38072 : Upper (D 6) (R 6) [34,136,48,260,68] 13 := by
  apply FastRouting.sound _ _ [34,136,48,260,68] 13 (by decide) (choices 1) [1,2,64] r38072 c38072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23730
  · exact u23731
  · exact u23732

def b38073 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 35 138 52 328 19 101 69 197 325), lower := (rows 35 138 52 328 19 32 64 128 256), losses := [] }

theorem u38073 : Upper (D 6) (R 6) [34,136,48,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38074 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 328 21 103 71 199 327), lower := (rows 35 138 52 328 21 32 64 128 256), losses := [] }

theorem u38074 : Upper (D 6) (R 6) [34,136,48,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38075 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 20, targets := 1 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 35 138 52 328 22 101 69 197 325), lower := (rows 35 138 52 328 22 32 64 128 256), losses := [] }

theorem u38075 : Upper (D 6) (R 6) [34,136,48,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38076 : Route 9 := (fun mask => (mask,id))

def c38076 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38076 : Upper (D 6) (R 6) [34,136,48,320,65] 13 := by
  apply FastRouting.sound _ _ [34,136,48,320,65] 13 (by decide) (choices 1) [1,2,4] r38076 c38076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23733
  · exact u23734
  · exact u23735

def r38077 : Route 9 := (fun mask => (mask,id))

def c38077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38077 : Upper (D 6) (R 6) [34,136,48,320,66] 13 := by
  apply FastRouting.sound _ _ [34,136,48,320,66] 13 (by decide) (choices 1) [1,4] r38077 c38077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23736
  · exact u23737

def r38078 : Route 9 := (fun mask => (mask,id))

def c38078 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38078 : Upper (D 6) (R 6) [34,136,48,320,68] 13 := by
  apply FastRouting.sound _ _ [34,136,48,320,68] 13 (by decide) (choices 1) [1,2,4] r38078 c38078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23738
  · exact u23739
  · exact u23740

def b38079 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 96 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 35 138 70 13 21 368 368 496 368), lower := (rows 35 138 70 13 21 32 64 128 256), losses := [] }

theorem u38079 : Upper (D 6) (R 6) [34,136,66,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38080 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 70 13 49 372 340 468 340), lower := (rows 35 138 70 13 49 32 64 128 256), losses := [] }

theorem u38080 : Upper (D 6) (R 6) [34,136,66,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38081 : Route 9 := (fun mask => (mask,id))

def c38081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u38081 : Upper (D 6) (R 6) [34,136,66,5,36] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5,36] 13 (by decide) (choices 1) [1,16,64,256] r38081 c38081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23741
  · exact u23742
  · exact u23743
  · exact u23744

def r38082 : Route 9 := (fun mask => (mask,id))

def c38082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38082 : Upper (D 6) (R 6) [34,136,66,5,96] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5,96] 13 (by decide) (choices 1) [1,4,16,256] r38082 c38082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23745
  · exact u23746
  · exact u23747
  · exact u23748

def r38083 : Route 9 := (fun mask => (mask,id))

def c38083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38083 : Upper (D 6) (R 6) [34,136,66,5,257] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5,257] 13 (by decide) (choices 1) [4,16,64] r38083 c38083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23749
  · exact u23750
  · exact u23751

def r38084 : Route 9 := (fun mask => (mask,id))

def c38084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38084 : Upper (D 6) (R 6) [34,136,66,5,288] 13 := by
  apply FastRouting.sound _ _ [34,136,66,5,288] 13 (by decide) (choices 1) [1,4,16,64] r38084 c38084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23752
  · exact u23753
  · exact u23754
  · exact u23755

def b38085 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 70 25 21 356 356 484 356), lower := (rows 35 138 70 25 21 32 64 128 256), losses := [] }

theorem u38085 : Upper (D 6) (R 6) [34,136,66,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38086 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 70 25 49 356 324 452 324), lower := (rows 35 138 70 25 49 32 64 128 256), losses := [] }

theorem u38086 : Upper (D 6) (R 6) [34,136,66,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38087 : Route 9 := (fun mask => (mask,id))

def c38087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u38087 : Upper (D 6) (R 6) [34,136,66,17,36] 13 := by
  apply FastRouting.sound _ _ [34,136,66,17,36] 13 (by decide) (choices 1) [1,4,64,256] r38087 c38087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23756
  · exact u23757
  · exact u23758
  · exact u23759

def b38088 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 70 25 81 292 356 420 292), lower := (rows 35 138 70 25 81 32 64 128 256), losses := [] }

theorem u38088 : Upper (D 6) (R 6) [34,136,66,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38089 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 70 25 84 293 357 421 293), lower := (rows 35 138 70 25 84 32 64 128 256), losses := [] }

theorem u38089 : Upper (D 6) (R 6) [34,136,66,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38090 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 2, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 138 70 25 112 293 325 389 261), lower := (rows 35 138 70 25 112 32 64 128 256), losses := [] }

theorem u38090 : Upper (D 6) (R 6) [34,136,66,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38091 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 70 25 273 100 100 228 356), lower := (rows 35 138 70 25 273 32 64 128 256), losses := [] }

theorem u38091 : Upper (D 6) (R 6) [34,136,66,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38092 : Route 9 := (fun mask => (mask,id))

def c38092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38092 : Upper (D 6) (R 6) [34,136,66,17,260] 13 := by
  apply FastRouting.sound _ _ [34,136,66,17,260] 13 (by decide) (choices 1) [1,4,64] r38092 c38092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23760
  · exact u23761
  · exact u23762

def r38093 : Route 9 := (fun mask => (mask,id))

def c38093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38093 : Upper (D 6) (R 6) [34,136,66,17,288] 13 := by
  apply FastRouting.sound _ _ [34,136,66,17,288] 13 (by decide) (choices 1) [1,4,64] r38093 c38093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23763
  · exact u23764
  · exact u23765

def r38094 : Route 9 := (fun mask => (mask,id))

def c38094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38094 : Upper (D 6) (R 6) [34,136,66,17,320] 13 := by
  apply FastRouting.sound _ _ [34,136,66,17,320] 13 (by decide) (choices 1) [1,4] r38094 c38094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23766
  · exact u23767

def b38095 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 138 70 44 21 369 337 465 337), lower := (rows 35 138 70 44 21 32 64 128 256), losses := [] }

theorem u38095 : Upper (D 6) (R 6) [34,136,66,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38096 : Route 9 := (fun mask => (mask,id))

def c38096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38096 : Upper (D 6) (R 6) [34,136,66,36,65] 13 := by
  apply FastRouting.sound _ _ [34,136,66,36,65] 13 (by decide) (choices 1) [1,4,16,256] r38096 c38096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23768
  · exact u23769
  · exact u23770
  · exact u23771

def b38097 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 70 44 84 305 337 401 273), lower := (rows 35 138 70 44 84 32 64 128 256), losses := [] }

theorem u38097 : Upper (D 6) (R 6) [34,136,66,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38098 : Route 9 := (fun mask => (mask,id))

def c38098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38098 : Upper (D 6) (R 6) [34,136,66,36,257] 13 := by
  apply FastRouting.sound _ _ [34,136,66,36,257] 13 (by decide) (choices 1) [1,4,16,64] r38098 c38098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23772
  · exact u23773
  · exact u23774
  · exact u23775

def r38099 : Route 9 := (fun mask => (mask,id))

def c38099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38099 : Upper (D 6) (R 6) [34,136,66,36,260] 13 := by
  apply FastRouting.sound _ _ [34,136,66,36,260] 13 (by decide) (choices 1) [1,16,64] r38099 c38099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23776
  · exact u23777
  · exact u23778

#print axioms u38099
end Delivery.IrregularNine14.P06
