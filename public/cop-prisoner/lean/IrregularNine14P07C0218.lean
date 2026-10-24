import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0027
import IrregularNine14P07C0028

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13080 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 69 328 49 48 194 130 386), lower := (rows 7 42 69 328 49 48 64 128 256), losses := [] }

theorem u13080 : Upper (D 7) (R 7) [6,40,65,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13080 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13081 : Route 9 := (fun mask => (mask,id))

def c13081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13081 : Upper (D 7) (R 7) [6,40,65,320,33,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320,33,128] 13 (by decide) (choices 1) [2,16,128] r13081 c13081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1645
  · exact u1646
  · exact u1647

def b13082 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 328 145 34 240 176 432), lower := (rows 7 42 69 328 145 34 64 128 256), losses := [] }

theorem u13082 : Upper (D 7) (R 7) [6,40,65,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13083 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 7 42 69 328 145 48 226 162 418), lower := (rows 7 42 69 328 145 48 64 128 256), losses := [] }

theorem u13083 : Upper (D 7) (R 7) [6,40,65,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13083 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13084 : Route 9 := (fun mask => (mask,id))

def c13084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13084 : Upper (D 7) (R 7) [6,40,65,320,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320,129,128] 13 (by decide) (choices 1) [2,16,32] r13084 c13084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1648
  · exact u1649
  · exact u1650

def b13085 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 328 146 33 240 176 432), lower := (rows 7 42 69 328 146 33 64 128 256), losses := [] }

theorem u13085 : Upper (D 7) (R 7) [6,40,65,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13086 : Route 9 := (fun mask => (mask,id))

def c13086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13086 : Upper (D 7) (R 7) [6,40,65,320,130,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320,130,16] 13 (by decide) (choices 1) [1,32,128] r13086 c13086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1651
  · exact u1652
  · exact u1653

def r13087 : Route 9 := (fun mask => (mask,id))

def c13087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13087 : Upper (D 7) (R 7) [6,40,65,320,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320,130,128] 13 (by decide) (choices 1) [1,16,32] r13087 c13087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1654
  · exact u1655
  · exact u1656

def b13088 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 328 176 33 210 146 402), lower := (rows 7 42 69 328 176 33 64 128 256), losses := [] }

theorem u13088 : Upper (D 7) (R 7) [6,40,65,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13089 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 328 176 34 209 145 401), lower := (rows 7 42 69 328 176 34 64 128 256), losses := [] }

theorem u13089 : Upper (D 7) (R 7) [6,40,65,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13090 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 328 176 48 195 131 387), lower := (rows 7 42 69 328 176 48 64 128 256), losses := [] }

theorem u13090 : Upper (D 7) (R 7) [6,40,65,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13090 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13091 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 328 176 160 83 147 275), lower := (rows 7 42 69 328 176 160 64 128 256), losses := [] }

theorem u13091 : Upper (D 7) (R 7) [6,40,65,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13092 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 42 69 392 49 34 208 208 464), lower := (rows 7 42 69 392 49 34 64 128 256), losses := [] }

theorem u13092 : Upper (D 7) (R 7) [6,40,65,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13093 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 42 69 392 49 48 194 194 450), lower := (rows 7 42 69 392 49 48 64 128 256), losses := [] }

theorem u13093 : Upper (D 7) (R 7) [6,40,65,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13093 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13094 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 48, targets := 130 },{ cop := 4, region := 394, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,7)], upper := (rows 7 42 69 392 49 96 210 146 402), lower := (rows 7 42 69 392 49 96 64 128 256), losses := [] }

theorem u13094 : Upper (D 7) (R 7) [6,40,65,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13095 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 392 49 160 82 210 338), lower := (rows 7 42 69 392 49 160 64 128 256), losses := [] }

theorem u13095 : Upper (D 7) (R 7) [6,40,65,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13096 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 7 42 69 392 112 33 210 146 402), lower := (rows 7 42 69 392 112 33 64 128 256), losses := [] }

theorem u13096 : Upper (D 7) (R 7) [6,40,65,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13097 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 392 112 34 209 145 401), lower := (rows 7 42 69 392 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 20 43 64 128 256), good := (rows 54 42 116 426 112 34 64 128 256) }] }

theorem u13097 : Upper (D 7) (R 7) [6,40,65,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13098 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 392 112 48 195 131 387), lower := (rows 7 42 69 392 112 48 64 128 256), losses := [] }

theorem u13098 : Upper (D 7) (R 7) [6,40,65,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13098 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13099 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 392 112 160 83 147 275), lower := (rows 7 42 69 392 112 160 64 128 256), losses := [] }

theorem u13099 : Upper (D 7) (R 7) [6,40,65,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13100 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 69 392 145 34 112 240 368), lower := (rows 7 42 69 392 145 34 64 128 256), losses := [] }

theorem u13100 : Upper (D 7) (R 7) [6,40,65,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13101 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 42 69 392 145 48 98 226 354), lower := (rows 7 42 69 392 145 48 64 128 256), losses := [] }

theorem u13101 : Upper (D 7) (R 7) [6,40,65,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13101 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13102 : Route 9 := (fun mask => (mask,id))

def c13102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13102 : Upper (D 7) (R 7) [6,40,65,384,129,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,129,64] 13 (by decide) (choices 1) [2,16,32] r13102 c13102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1657
  · exact u1658
  · exact u1659

def b13103 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 42 69 392 146 33 112 240 368), lower := (rows 7 42 69 392 146 33 64 128 256), losses := [] }

theorem u13103 : Upper (D 7) (R 7) [6,40,65,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13104 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 69 392 146 48 97 225 353), lower := (rows 7 42 69 392 146 48 64 128 256), losses := [] }

theorem u13104 : Upper (D 7) (R 7) [6,40,65,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13104 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13105 : Route 9 := (fun mask => (mask,id))

def c13105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13105 : Upper (D 7) (R 7) [6,40,65,384,130,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,130,64] 13 (by decide) (choices 1) [1,16,32] r13105 c13105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1660
  · exact u1661
  · exact u1662

def r13106 : Route 9 := (fun mask => (mask,id))

def c13106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13106 : Upper (D 7) (R 7) [6,40,65,384,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,160,1] 13 (by decide) (choices 1) [2,16] r13106 c13106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1663
  · exact u1664

def b13107 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 42 69 392 176 34 81 209 337), lower := (rows 7 42 69 392 176 34 64 128 256), losses := [] }

theorem u13107 : Upper (D 7) (R 7) [6,40,65,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13108 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 69 392 176 48 67 195 323), lower := (rows 7 42 69 392 176 48 64 128 256), losses := [] }

theorem u13108 : Upper (D 7) (R 7) [6,40,65,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13108 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13109 : Route 9 := (fun mask => (mask,id))

def c13109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13109 : Upper (D 7) (R 7) [6,40,65,384,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,160,64] 13 (by decide) (choices 1) [1,2,16] r13109 c13109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1665
  · exact u1666
  · exact u1667

def r13110 : Route 9 := (fun mask => (mask,id))

def c13110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13110 : Upper (D 7) (R 7) [6,40,65,384,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,192,1] 13 (by decide) (choices 1) [2,16,32] r13110 c13110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1668
  · exact u1669
  · exact u1670

def r13111 : Route 9 := (fun mask => (mask,id))

def c13111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13111 : Upper (D 7) (R 7) [6,40,65,384,192,2] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,192,2] 13 (by decide) (choices 1) [1,16,32] r13111 c13111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1671
  · exact u1672
  · exact u1673

def r13112 : Route 9 := (fun mask => (mask,id))

def c13112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13112 : Upper (D 7) (R 7) [6,40,65,384,192,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,192,16] 13 (by decide) (choices 1) [1,2,32] r13112 c13112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1674
  · exact u1675
  · exact u1676

def b13113 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 73 146 33 480 416 416), lower := (rows 7 42 84 73 146 33 64 128 256), losses := [] }

theorem u13113 : Upper (D 7) (R 7) [6,40,80,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13114 : Route 9 := (fun mask => (mask,id))

def c13114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u13114 : Upper (D 7) (R 7) [6,40,80,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,130,128] 13 (by decide) (choices 1) [1,32,256] r13114 c13114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1677
  · exact u1678
  · exact u1679

def b13115 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 488, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 7 42 84 73 146 288 225 161 417), lower := (rows 7 42 84 73 146 288 64 128 256), losses := [] }

theorem u13115 : Upper (D 7) (R 7) [6,40,80,65,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13115 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13116 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 73 176 33 450 386 386), lower := (rows 7 42 84 73 176 33 64 128 256), losses := [] }

theorem u13116 : Upper (D 7) (R 7) [6,40,80,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13117 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 456, targets := 2 }], pairs := [(0,7),(1,7),(3,1),(3,7)], upper := (rows 7 42 84 73 176 34 449 385 385), lower := (rows 7 42 84 73 176 34 64 128 256), losses := [] }

theorem u13117 : Upper (D 7) (R 7) [6,40,80,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13118 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 84 73 176 160 323 387 259), lower := (rows 7 42 84 73 176 160 64 128 256), losses := [] }

theorem u13118 : Upper (D 7) (R 7) [6,40,80,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13119 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,6),(3,5),(4,6)], upper := (rows 7 42 84 73 176 288 195 131 387), lower := (rows 7 42 84 73 176 288 64 128 256), losses := [] }

theorem u13119 : Upper (D 7) (R 7) [6,40,80,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13119 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13120 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 73 274 33 224 160 416), lower := (rows 7 42 84 73 274 33 64 128 256), losses := [] }

theorem u13120 : Upper (D 7) (R 7) [6,40,80,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13121 : Route 9 := (fun mask => (mask,id))

def c13121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13121 : Upper (D 7) (R 7) [6,40,80,65,258,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,258,128] 13 (by decide) (choices 1) [1,32,128] r13121 c13121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1680
  · exact u1681
  · exact u1682

def b13122 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 73 304 33 194 130 386), lower := (rows 7 42 84 73 304 33 64 128 256), losses := [] }

theorem u13122 : Upper (D 7) (R 7) [6,40,80,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13123 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,7),(1,7),(3,1),(3,7)], upper := (rows 7 42 84 73 304 34 193 129 385), lower := (rows 7 42 84 73 304 34 64 128 256), losses := [] }

theorem u13123 : Upper (D 7) (R 7) [6,40,80,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13124 : Route 9 := (fun mask => (mask,id))

def c13124 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13124 : Upper (D 7) (R 7) [6,40,80,65,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,288,128] 13 (by decide) (choices 1) [1,2,128] r13124 c13124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1683
  · exact u1684
  · exact u1685

def b13125 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 73 400 33 226 162 418), lower := (rows 7 42 84 73 400 33 64 128 256), losses := [] }

theorem u13125 : Upper (D 7) (R 7) [6,40,80,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13126 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 7 42 84 73 400 34 225 161 417), lower := (rows 7 42 84 73 400 34 64 128 256), losses := [] }

theorem u13126 : Upper (D 7) (R 7) [6,40,80,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13127 : Route 9 := (fun mask => (mask,id))

def c13127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13127 : Upper (D 7) (R 7) [6,40,80,65,384,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,384,128] 13 (by decide) (choices 1) [1,2,32] r13127 c13127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1686
  · exact u1687
  · exact u1688

def b13128 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 84 74 145 33 480 416 416), lower := (rows 7 42 84 74 145 33 64 128 256), losses := [] }

theorem u13128 : Upper (D 7) (R 7) [6,40,80,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13129 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(2,1),(4,1),(4,6)], upper := (rows 7 42 84 74 145 160 353 417 289), lower := (rows 7 42 84 74 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 176 64 128 256), good := (rows 14 42 126 74 176 160 64 160 256) }] }

theorem u13129 : Upper (D 7) (R 7) [6,40,80,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13130 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 84 74 145 288 225 161 417), lower := (rows 7 42 84 74 145 288 64 128 256), losses := [] }

theorem u13130 : Upper (D 7) (R 7) [6,40,80,66,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13130 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13131 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 84 74 273 33 224 160 416), lower := (rows 7 42 84 74 273 33 64 128 256), losses := [] }

theorem u13131 : Upper (D 7) (R 7) [6,40,80,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13132 : Route 9 := (fun mask => (mask,id))

def c13132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13132 : Upper (D 7) (R 7) [6,40,80,66,257,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,66,257,128] 13 (by decide) (choices 1) [1,32,128] r13132 c13132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1689
  · exact u1690
  · exact u1691

def b13133 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 84 74 400 33 225 161 417), lower := (rows 7 42 84 74 400 33 64 128 256), losses := [] }

theorem u13133 : Upper (D 7) (R 7) [6,40,80,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13134 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(2,1),(4,1),(4,6)], upper := (rows 7 42 84 74 400 160 97 161 289), lower := (rows 7 42 84 74 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 176 64 128 256), good := (rows 14 42 126 74 432 160 64 160 256) }] }

theorem u13134 : Upper (D 7) (R 7) [6,40,80,66,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13135 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,6)], upper := (rows 7 42 84 137 176 33 322 450 322), lower := (rows 7 42 84 137 176 33 64 128 256), losses := [] }

theorem u13135 : Upper (D 7) (R 7) [6,40,80,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13136 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 42 84 137 176 34 321 449 321), lower := (rows 7 42 84 137 176 34 64 128 256), losses := [] }

theorem u13136 : Upper (D 7) (R 7) [6,40,80,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13137 : Route 9 := (fun mask => (mask,id))

def c13137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u13137 : Upper (D 7) (R 7) [6,40,80,129,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160,64] 13 (by decide) (choices 1) [1,2,256] r13137 c13137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1692
  · exact u1693
  · exact u1694

def r13138 : Route 9 := (fun mask => (mask,id))

def c13138 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13138 : Upper (D 7) (R 7) [6,40,80,129,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160,256] 13 (by decide) (choices 1) [1,2] r13138 c13138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1695
  · exact u1696

def b13139 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 7 42 84 137 273 34 224 224 480), lower := (rows 7 42 84 137 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 123 187 315), good := (rows 486 490 468 490 500 482 64 128 256) }] }

theorem u13139 : Upper (D 7) (R 7) [6,40,80,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13139
end Delivery.IrregularNine14.P07
