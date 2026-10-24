import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0667
import IrregularNine14P06C0668
import IrregularNine14P06C0669
import IrregularNine14P06C0670
import IrregularNine14P06C0671

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r43500 : Route 9 := (fun mask => (mask,id))

def c43500 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43500 : Upper (D 6) (R 6) [40,132,288,17] 13 := by
  apply FastRouting.sound _ _ [40,132,288,17] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43500 c43500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40025
  · exact u40026
  · exact u40027
  · exact u40028
  · exact u40029
  · exact u40030

def r43501 : Route 9 := (fun mask => (mask,id))

def c43501 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43501 : Upper (D 6) (R 6) [40,132,288,18] 13 := by
  apply FastRouting.sound _ _ [40,132,288,18] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43501 c43501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40031
  · exact u40032
  · exact u40033
  · exact u40034
  · exact u40035
  · exact u40036

def r43502 : Route 9 := (fun mask => (mask,id))

def c43502 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43502 : Upper (D 6) (R 6) [40,132,288,20] 13 := by
  apply FastRouting.sound _ _ [40,132,288,20] 13 (by decide) (choices 2) [3,65,66] r43502 c43502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40037
  · exact u40038
  · exact u40039

def r43503 : Route 9 := (fun mask => (mask,id))

def c43503 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43503 : Upper (D 6) (R 6) [40,132,288,65] 13 := by
  apply FastRouting.sound _ _ [40,132,288,65] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43503 c43503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40040
  · exact u40041
  · exact u40042
  · exact u40043
  · exact u40044
  · exact u40045

def r43504 : Route 9 := (fun mask => (mask,id))

def c43504 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43504 : Upper (D 6) (R 6) [40,132,288,66] 13 := by
  apply FastRouting.sound _ _ [40,132,288,66] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43504 c43504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40046
  · exact u40047
  · exact u40048
  · exact u40049
  · exact u40050
  · exact u40051

def r43505 : Route 9 := (fun mask => (mask,id))

def c43505 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43505 : Upper (D 6) (R 6) [40,132,288,68] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68] 13 (by decide) (choices 2) [3,65,66] r43505 c43505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40052
  · exact u40053
  · exact u40054

def r43506 : Route 9 := (fun mask => (mask,id))

def c43506 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43506 : Upper (D 6) (R 6) [40,132,288,80] 13 := by
  apply FastRouting.sound _ _ [40,132,288,80] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43506 c43506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40055
  · exact u40056
  · exact u40057
  · exact u40058
  · exact u40059
  · exact u40060

def r43507 : Route 9 := (fun mask => (mask,id))

def c43507 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43507 : Upper (D 6) (R 6) [40,132,320,3] 13 := by
  apply FastRouting.sound _ _ [40,132,320,3] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43507 c43507
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40061
  · exact u40062
  · exact u40063
  · exact u40064
  · exact u40065
  · exact u40066
  · exact u40067
  · exact u40068
  · exact u40069
  · exact u40070

def r43508 : Route 9 := (fun mask => (mask,id))

def c43508 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43508 : Upper (D 6) (R 6) [40,132,320,5] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5] 13 (by decide) (choices 2) [3,33,34,65,66,96] r43508 c43508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40071
  · exact u40072
  · exact u40073
  · exact u40074
  · exact u40075
  · exact u40076

def b43509 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 134 324 14 115 115 115 243 371), lower := (rows 41 134 324 14 16 32 64 128 256), losses := [] }

theorem u43509 : Upper (D 6) (R 6) [40,132,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43510 : Route 9 := (fun mask => (mask,id))

def c43510 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43510 : Upper (D 6) (R 6) [40,132,320,17] 13 := by
  apply FastRouting.sound _ _ [40,132,320,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43510 c43510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40077
  · exact u40078
  · exact u40079
  · exact u40080
  · exact u40081
  · exact u40082
  · exact u40083
  · exact u40084
  · exact u40085
  · exact u40086

def r43511 : Route 9 := (fun mask => (mask,id))

def c43511 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43511 : Upper (D 6) (R 6) [40,132,320,18] 13 := by
  apply FastRouting.sound _ _ [40,132,320,18] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43511 c43511
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40087
  · exact u40088
  · exact u40089
  · exact u40090
  · exact u40091
  · exact u40092
  · exact u40093
  · exact u40094
  · exact u40095
  · exact u40096

def r43512 : Route 9 := (fun mask => (mask,id))

def c43512 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43512 : Upper (D 6) (R 6) [40,132,320,20] 13 := by
  apply FastRouting.sound _ _ [40,132,320,20] 13 (by decide) (choices 2) [3,33,34,65,66,96] r43512 c43512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40097
  · exact u40098
  · exact u40099
  · exact u40100
  · exact u40101
  · exact u40102

def b43513 : PairBound 9 := { available := 87, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 41 87 119 87 215 343), lower := (rows 41 134 324 41 16 32 64 128 256), losses := [] }

theorem u43513 : Upper (D 6) (R 6) [40,132,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43514 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 324 42 87 119 87 215 343), lower := (rows 41 134 324 42 16 32 64 128 256), losses := [] }

theorem u43514 : Upper (D 6) (R 6) [40,132,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43515 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 324 44 83 115 83 211 339), lower := (rows 41 134 324 44 16 32 64 128 256), losses := [] }

theorem u43515 : Upper (D 6) (R 6) [40,132,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43516 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 324 56 87 103 71 199 327), lower := (rows 41 134 324 56 16 32 64 128 256), losses := [] }

theorem u43516 : Upper (D 6) (R 6) [40,132,320,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43517 : Route 9 := (fun mask => (mask,id))

def c43517 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43517 : Upper (D 6) (R 6) [40,132,320,65] 13 := by
  apply FastRouting.sound _ _ [40,132,320,65] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43517 c43517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40103
  · exact u40104
  · exact u40105
  · exact u40106
  · exact u40107
  · exact u40108

def r43518 : Route 9 := (fun mask => (mask,id))

def c43518 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43518 : Upper (D 6) (R 6) [40,132,320,66] 13 := by
  apply FastRouting.sound _ _ [40,132,320,66] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43518 c43518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40109
  · exact u40110
  · exact u40111
  · exact u40112
  · exact u40113
  · exact u40114

def b43519 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 134 324 76 51 51 115 179 307), lower := (rows 41 134 324 76 16 32 64 128 256), losses := [] }

theorem u43519 : Upper (D 6) (R 6) [40,132,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43520 : Route 9 := (fun mask => (mask,id))

def c43520 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43520 : Upper (D 6) (R 6) [40,132,320,80] 13 := by
  apply FastRouting.sound _ _ [40,132,320,80] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43520 c43520
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40115
  · exact u40116
  · exact u40117
  · exact u40118
  · exact u40119
  · exact u40120

def b43521 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 134 324 104 23 55 87 151 279), lower := (rows 41 134 324 104 16 32 64 128 256), losses := [] }

theorem u43521 : Upper (D 6) (R 6) [40,132,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43522 : Route 9 := (fun mask => (mask,id))

def c43522 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43522 : Upper (D 6) (R 6) [40,144,288,3] 13 := by
  apply FastRouting.sound _ _ [40,144,288,3] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43522 c43522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40121
  · exact u40122
  · exact u40123
  · exact u40124
  · exact u40125
  · exact u40126

def b43523 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 292 13 87 103 71 199 327), lower := (rows 41 146 292 13 16 32 64 128 256), losses := [] }

theorem u43523 : Upper (D 6) (R 6) [40,144,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43524 : Route 9 := (fun mask => (mask,id))

def c43524 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43524 : Upper (D 6) (R 6) [40,144,288,6] 13 := by
  apply FastRouting.sound _ _ [40,144,288,6] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43524 c43524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40127
  · exact u40128
  · exact u40129
  · exact u40130
  · exact u40131
  · exact u40132

def r43525 : Route 9 := (fun mask => (mask,id))

def c43525 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43525 : Upper (D 6) (R 6) [40,144,288,65] 13 := by
  apply FastRouting.sound _ _ [40,144,288,65] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43525 c43525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40133
  · exact u40134
  · exact u40135
  · exact u40136
  · exact u40137
  · exact u40138

def r43526 : Route 9 := (fun mask => (mask,id))

def c43526 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43526 : Upper (D 6) (R 6) [40,144,288,66] 13 := by
  apply FastRouting.sound _ _ [40,144,288,66] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43526 c43526
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40139
  · exact u40140
  · exact u40141
  · exact u40142
  · exact u40143
  · exact u40144

def r43527 : Route 9 := (fun mask => (mask,id))

def c43527 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43527 : Upper (D 6) (R 6) [40,144,288,68] 13 := by
  apply FastRouting.sound _ _ [40,144,288,68] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43527 c43527
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40145
  · exact u40146
  · exact u40147
  · exact u40148
  · exact u40149
  · exact u40150

def r43528 : Route 9 := (fun mask => (mask,id))

def c43528 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43528 : Upper (D 6) (R 6) [40,144,320,3] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43528 c43528
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40151
  · exact u40152
  · exact u40153
  · exact u40154
  · exact u40155
  · exact u40156
  · exact u40157
  · exact u40158
  · exact u40159
  · exact u40160

def r43529 : Route 9 := (fun mask => (mask,id))

def c43529 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43529 : Upper (D 6) (R 6) [40,144,320,5] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43529 c43529
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40161
  · exact u40162
  · exact u40163
  · exact u40164
  · exact u40165
  · exact u40166
  · exact u40167
  · exact u40168
  · exact u40169
  · exact u40170

def r43530 : Route 9 := (fun mask => (mask,id))

def c43530 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43530 : Upper (D 6) (R 6) [40,144,320,6] 13 := by
  apply FastRouting.sound _ _ [40,144,320,6] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43530 c43530
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40171
  · exact u40172
  · exact u40173
  · exact u40174
  · exact u40175
  · exact u40176
  · exact u40177
  · exact u40178
  · exact u40179
  · exact u40180

def b43531 : PairBound 9 := { available := 71, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 324 41 87 103 71 199 327), lower := (rows 41 146 324 41 16 32 64 128 256), losses := [] }

theorem u43531 : Upper (D 6) (R 6) [40,144,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43532 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 146 324 42 87 103 71 199 327), lower := (rows 41 146 324 42 16 32 64 128 256), losses := [] }

theorem u43532 : Upper (D 6) (R 6) [40,144,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43533 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 146 324 44 87 103 71 199 327), lower := (rows 41 146 324 44 16 32 64 128 256), losses := [] }

theorem u43533 : Upper (D 6) (R 6) [40,144,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43534 : Route 9 := (fun mask => (mask,id))

def c43534 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43534 : Upper (D 6) (R 6) [40,144,320,65] 13 := by
  apply FastRouting.sound _ _ [40,144,320,65] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43534 c43534
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40181
  · exact u40182
  · exact u40183
  · exact u40184
  · exact u40185
  · exact u40186

def r43535 : Route 9 := (fun mask => (mask,id))

def c43535 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43535 : Upper (D 6) (R 6) [40,144,320,66] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43535 c43535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40187
  · exact u40188
  · exact u40189
  · exact u40190
  · exact u40191
  · exact u40192

def b43536 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 146 324 76 55 39 103 167 295), lower := (rows 41 146 324 76 16 32 64 128 256), losses := [] }

theorem u43536 : Upper (D 6) (R 6) [40,144,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43537 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 146 324 104 23 39 71 135 263), lower := (rows 41 146 324 104 16 32 64 128 256), losses := [] }

theorem u43537 : Upper (D 6) (R 6) [40,144,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43538 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 162 324 11 87 119 87 215 343), lower := (rows 41 162 324 11 16 32 64 128 256), losses := [] }

theorem u43538 : Upper (D 6) (R 6) [40,160,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43539 : Route 9 := (fun mask => (mask,id))

def c43539 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43539 : Upper (D 6) (R 6) [40,160,320,5] 13 := by
  apply FastRouting.sound _ _ [40,160,320,5] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43539 c43539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40193
  · exact u40194
  · exact u40195
  · exact u40196
  · exact u40197
  · exact u40198

def r43540 : Route 9 := (fun mask => (mask,id))

def c43540 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43540 : Upper (D 6) (R 6) [40,160,320,6] 13 := by
  apply FastRouting.sound _ _ [40,160,320,6] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43540 c43540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40199
  · exact u40200
  · exact u40201
  · exact u40202
  · exact u40203
  · exact u40204

def r43541 : Route 9 := (fun mask => (mask,id))

def c43541 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43541 : Upper (D 6) (R 6) [40,160,320,17] 13 := by
  apply FastRouting.sound _ _ [40,160,320,17] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43541 c43541
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40205
  · exact u40206
  · exact u40207
  · exact u40208
  · exact u40209
  · exact u40210

def r43542 : Route 9 := (fun mask => (mask,id))

def c43542 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43542 : Upper (D 6) (R 6) [40,160,320,18] 13 := by
  apply FastRouting.sound _ _ [40,160,320,18] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43542 c43542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40211
  · exact u40212
  · exact u40213
  · exact u40214
  · exact u40215
  · exact u40216

def r43543 : Route 9 := (fun mask => (mask,id))

def c43543 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43543 : Upper (D 6) (R 6) [40,160,320,20] 13 := by
  apply FastRouting.sound _ _ [40,160,320,20] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43543 c43543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40217
  · exact u40218
  · exact u40219
  · exact u40220
  · exact u40221
  · exact u40222

def r43544 : Route 9 := (fun mask => (mask,id))

def c43544 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43544 : Upper (D 6) (R 6) [40,160,320,65] 13 := by
  apply FastRouting.sound _ _ [40,160,320,65] 13 (by decide) (choices 2) [3,5,6] r43544 c43544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40223
  · exact u40224
  · exact u40225

def r43545 : Route 9 := (fun mask => (mask,id))

def c43545 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43545 : Upper (D 6) (R 6) [40,160,320,66] 13 := by
  apply FastRouting.sound _ _ [40,160,320,66] 13 (by decide) (choices 2) [3,5,6] r43545 c43545
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40226
  · exact u40227
  · exact u40228

def b43546 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 162 324 76 23 55 87 151 279), lower := (rows 41 162 324 76 16 32 64 128 256), losses := [] }

theorem u43546 : Upper (D 6) (R 6) [40,160,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43547 : Route 9 := (fun mask => (mask,id))

def c43547 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43547 : Upper (D 6) (R 6) [40,160,320,80] 13 := by
  apply FastRouting.sound _ _ [40,160,320,80] 13 (by decide) (choices 2) [3,5,6] r43547 c43547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40229
  · exact u40230
  · exact u40231

def r43548 : Route 9 := (fun mask => (mask,id))

def c43548 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43548 : Upper (D 6) (R 6) [40,192,320,3] 13 := by
  apply FastRouting.sound _ _ [40,192,320,3] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43548 c43548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40232
  · exact u40233
  · exact u40234
  · exact u40235
  · exact u40236
  · exact u40237

theorem m43549_5 : Upper (D 6) (R 6) [40,192,320,6,5] 13 :=
  permutation_upper _ _ _ [40,192,320,6,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40238

theorem m43549_36 : Upper (D 6) (R 6) [40,192,320,6,36] 13 :=
  permutation_upper _ _ _ [40,192,320,6,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40241

def r43549 : Route 9 := (fun mask => (mask,id))

def c43549 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43549 : Upper (D 6) (R 6) [40,192,320,6] 13 := by
  apply FastRouting.sound _ _ [40,192,320,6] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43549 c43549
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40238
  · exact m43549_5
  · exact u40239
  · exact u40240
  · exact u40241
  · exact m43549_36

theorem m43550_5 : Upper (D 6) (R 6) [40,192,320,17,5] 13 :=
  permutation_upper _ _ _ [40,192,320,17,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40242

theorem m43550_36 : Upper (D 6) (R 6) [40,192,320,17,36] 13 :=
  permutation_upper _ _ _ [40,192,320,17,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40245

def r43550 : Route 9 := (fun mask => (mask,id))

def c43550 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43550 : Upper (D 6) (R 6) [40,192,320,17] 13 := by
  apply FastRouting.sound _ _ [40,192,320,17] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43550 c43550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40242
  · exact m43550_5
  · exact u40243
  · exact u40244
  · exact u40245
  · exact m43550_36

def r43551 : Route 9 := (fun mask => (mask,id))

def c43551 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43551 : Upper (D 6) (R 6) [40,192,320,18] 13 := by
  apply FastRouting.sound _ _ [40,192,320,18] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43551 c43551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40246
  · exact u40247
  · exact u40248
  · exact u40249
  · exact u40250
  · exact u40251

def b43552 : PairBound 9 := { available := 23, camps := [{ cop := 5, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 194 324 41 23 55 87 151 279), lower := (rows 41 194 324 41 16 32 64 128 256), losses := [] }

theorem u43552 : Upper (D 6) (R 6) [40,192,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43553 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 194 324 42 23 55 87 151 279), lower := (rows 41 194 324 42 16 32 64 128 256), losses := [] }

theorem u43553 : Upper (D 6) (R 6) [40,192,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43554 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 41 194 324 56 23 39 71 135 263), lower := (rows 41 194 324 56 16 32 64 128 256), losses := [] }

theorem u43554 : Upper (D 6) (R 6) [40,192,320,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43555_12 : Upper (D 6) (R 6) [96,129,257,6,12] 13 :=
  permutation_upper _ _ _ [96,129,257,6,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40253

theorem m43555_36 : Upper (D 6) (R 6) [96,129,257,6,36] 13 :=
  permutation_upper _ _ _ [96,129,257,6,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40254

def r43555 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43555 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43555 : Upper (D 6) (R 6) [96,129,257,6] 13 := by
  apply FastRouting.sound _ _ [96,129,257,6] 13 (by decide) (choices 2) [6,10,12,34,36,40,96] r43555 c43555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40252
  · exact u40253
  · exact m43555_12
  · exact u40254
  · exact m43555_36
  · exact u40255
  · exact u40256

theorem m43556_6 : Upper (D 6) (R 6) [96,129,257,18,6] 13 :=
  permutation_upper _ _ _ [96,129,257,6,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40253

def r43556 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43556 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43556 : Upper (D 6) (R 6) [96,129,257,18] 13 := by
  apply FastRouting.sound _ _ [96,129,257,18] 13 (by decide) (choices 2) [6,10,12,34,36,40,96] r43556 c43556
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43556_6
  · exact u40257
  · exact u40258
  · exact u40259
  · exact u40260
  · exact u40261
  · exact u40262

theorem m43557_6 : Upper (D 6) (R 6) [96,129,257,34,6] 13 :=
  permutation_upper _ _ _ [96,129,257,6,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40254

theorem m43557_10 : Upper (D 6) (R 6) [96,129,257,34,10] 13 :=
  permutation_upper _ _ _ [96,129,257,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40259

theorem m43557_12 : Upper (D 6) (R 6) [96,129,257,34,12] 13 :=
  permutation_upper _ _ _ [96,129,257,18,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40260

def r43557 : Route 9 := (fun mask => (mask,id))

def c43557 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43557 : Upper (D 6) (R 6) [96,129,257,34] 13 := by
  apply FastRouting.sound _ _ [96,129,257,34] 13 (by decide) (choices 2) [6,10,12,66,68,72] r43557 c43557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43557_6
  · exact m43557_10
  · exact m43557_12
  · exact u40263
  · exact u40264
  · exact u40265

theorem m43558_6 : Upper (D 6) (R 6) [96,129,257,48,6] 13 :=
  permutation_upper _ _ _ [96,129,257,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40255

theorem m43558_10 : Upper (D 6) (R 6) [96,129,257,48,10] 13 :=
  permutation_upper _ _ _ [96,129,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40261

theorem m43558_12 : Upper (D 6) (R 6) [96,129,257,48,12] 13 :=
  permutation_upper _ _ _ [96,129,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40261

theorem m43558_66 : Upper (D 6) (R 6) [96,129,257,48,66] 13 :=
  permutation_upper _ _ _ [96,129,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40265

theorem m43558_68 : Upper (D 6) (R 6) [96,129,257,48,68] 13 :=
  permutation_upper _ _ _ [96,129,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40265

def r43558 : Route 9 := (fun mask => (mask,id))

def c43558 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43558 : Upper (D 6) (R 6) [96,129,257,48] 13 := by
  apply FastRouting.sound _ _ [96,129,257,48] 13 (by decide) (choices 2) [6,10,12,66,68,72] r43558 c43558
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43558_6
  · exact m43558_10
  · exact m43558_12
  · exact m43558_66
  · exact m43558_68
  · exact u40266

def b43559 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 6 },{ cop := 3, region := 1, targets := 2 }], pairs := [(0,1),(3,1),(3,2)], upper := (rows 97 131 261 104 30 62 94 158 286), lower := (rows 97 131 261 104 16 32 64 128 256), losses := [] }

theorem u43559 : Upper (D 6) (R 6) [96,129,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u43559
end Delivery.IrregularNine14.P06
