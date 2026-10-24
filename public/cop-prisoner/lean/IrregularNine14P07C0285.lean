import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0068

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17100 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 152 49 96 323 387 259), lower := (rows 13 98 134 152 49 96 64 128 256), losses := [] }

theorem u17100 : Upper (D 7) (R 7) [12,96,130,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17101 : Route 9 := (fun mask => (mask,id))

def c17101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17101 : Upper (D 7) (R 7) [12,96,130,144,33,256] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,33,256] 13 (by decide) (choices 1) [1,2] r17101 c17101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4090
  · exact u4091

def b17102 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(4,7)], upper := (rows 13 98 134 152 273 33 98 226 354), lower := (rows 13 98 134 152 273 33 64 128 256), losses := [] }

theorem u17102 : Upper (D 7) (R 7) [12,96,130,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17103_1 : Upper (D 7) (R 7) [12,96,130,144,257,2,1] 13 :=
  permutation_upper _ _ _ [12,96,130,144,257,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4092

def r17103 : Route 9 := (fun mask => (mask,id))

def c17103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17103 : Upper (D 7) (R 7) [12,96,130,144,257,2] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,257,2] 13 (by decide) (choices 1) [1,32] r17103 c17103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17103_1
  · exact u4093

def b17104 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 152 273 96 99 163 291), lower := (rows 13 98 134 152 273 96 64 128 256), losses := [] }

theorem u17104 : Upper (D 7) (R 7) [12,96,130,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17105 : Route 9 := (fun mask => (mask,id))

def c17105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17105 : Upper (D 7) (R 7) [12,96,130,144,258,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,258,1] 13 (by decide) (choices 1) [1,32] r17105 c17105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4094
  · exact u4095

def b17106 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 152 274 96 97 161 289), lower := (rows 13 98 134 152 274 96 64 128 256), losses := [] }

theorem u17106 : Upper (D 7) (R 7) [12,96,130,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17107 : Route 9 := (fun mask => (mask,id))

def c17107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17107 : Upper (D 7) (R 7) [12,96,130,144,288,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,288,1] 13 (by decide) (choices 1) [1,2] r17107 c17107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4096
  · exact u4097

def r17108 : Route 9 := (fun mask => (mask,id))

def c17108 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17108 : Upper (D 7) (R 7) [12,96,130,144,288,2] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,288,2] 13 (by decide) (choices 1) [1] r17108 c17108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u4098

def b17109 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 152 304 96 67 131 259), lower := (rows 13 98 134 152 304 96 64 128 256), losses := [] }

theorem u17109 : Upper (D 7) (R 7) [12,96,130,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17110 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 134 168 81 33 338 402 274), lower := (rows 13 98 134 168 81 33 64 128 256), losses := [] }

theorem u17110 : Upper (D 7) (R 7) [12,96,130,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17111 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 0, region := 370, targets := 128 }], pairs := [(1,7),(4,1),(4,5),(4,7)], upper := (rows 13 98 134 168 81 34 337 401 273), lower := (rows 13 98 134 168 81 34 64 128 256), losses := [] }

theorem u17111 : Upper (D 7) (R 7) [12,96,130,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17112 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 134 168 81 48 323 387 259), lower := (rows 13 98 134 168 81 48 64 128 256), losses := [] }

theorem u17112 : Upper (D 7) (R 7) [12,96,130,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17112 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17113 : Route 9 := (fun mask => (mask,id))

def c17113 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17113 : Upper (D 7) (R 7) [12,96,130,160,65,256] 13 := by
  apply FastRouting.sound _ _ [12,96,130,160,65,256] 13 (by decide) (choices 1) [1,2,16] r17113 c17113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4099
  · exact u4100
  · exact u4101

def b17114 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 134 168 273 33 82 210 338), lower := (rows 13 98 134 168 273 33 64 128 256), losses := [] }

theorem u17114 : Upper (D 7) (R 7) [12,96,130,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17115 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 0, region := 370, targets := 128 }], pairs := [(1,7),(4,1),(4,5),(4,7)], upper := (rows 13 98 134 168 273 34 81 209 337), lower := (rows 13 98 134 168 273 34 64 128 256), losses := [] }

theorem u17115 : Upper (D 7) (R 7) [12,96,130,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17116 : Route 9 := (fun mask => (mask,id))

def c17116 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17116 : Upper (D 7) (R 7) [12,96,130,160,257,16] 13 := by
  apply FastRouting.sound _ _ [12,96,130,160,257,16] 13 (by decide) (choices 1) [1,2] r17116 c17116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4102
  · exact u4103

def b17117 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 168 273 96 83 147 275), lower := (rows 13 98 134 168 273 96 64 128 256), losses := [] }

theorem u17117 : Upper (D 7) (R 7) [12,96,130,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17118 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 134 168 274 33 81 209 337), lower := (rows 13 98 134 168 274 33 64 128 256), losses := [] }

theorem u17118 : Upper (D 7) (R 7) [12,96,130,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17119 : Route 9 := (fun mask => (mask,id))

def c17119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17119 : Upper (D 7) (R 7) [12,96,130,160,258,16] 13 := by
  apply FastRouting.sound _ _ [12,96,130,160,258,16] 13 (by decide) (choices 1) [1] r17119 c17119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u4104

def b17120 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 168 274 96 81 145 273), lower := (rows 13 98 134 168 274 96 64 128 256), losses := [] }

theorem u17120 : Upper (D 7) (R 7) [12,96,130,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17121 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 134 168 336 33 83 147 275), lower := (rows 13 98 134 168 336 33 64 128 256), losses := [] }

theorem u17121 : Upper (D 7) (R 7) [12,96,130,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17122 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 0, region := 370, targets := 128 }], pairs := [(1,7),(4,1),(4,5),(4,7)], upper := (rows 13 98 134 168 336 34 81 145 273), lower := (rows 13 98 134 168 336 34 64 128 256), losses := [] }

theorem u17122 : Upper (D 7) (R 7) [12,96,130,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17123 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 134 168 336 48 67 131 259), lower := (rows 13 98 134 168 336 48 64 128 256), losses := [] }

theorem u17123 : Upper (D 7) (R 7) [12,96,130,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17123 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17124 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 13 98 134 265 19 48 224 224 480), lower := (rows 13 98 134 265 19 48 64 128 256), losses := [] }

theorem u17124 : Upper (D 7) (R 7) [12,96,130,257,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17124 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17125 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 265 19 96 240 176 432), lower := (rows 13 98 134 265 19 96 64 128 256), losses := [] }

theorem u17125 : Upper (D 7) (R 7) [12,96,130,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17126_16 : Upper (D 7) (R 7) [12,96,130,257,3,128,16] 13 :=
  permutation_upper _ _ _ [12,96,130,257,3,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4105

theorem m17126_32 : Upper (D 7) (R 7) [12,96,130,257,3,128,32] 13 :=
  permutation_upper _ _ _ [12,96,130,257,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4106

def r17126 : Route 9 := (fun mask => (mask,id))

def c17126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17126 : Upper (D 7) (R 7) [12,96,130,257,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,130,257,3,128] 13 (by decide) (choices 1) [16,32] r17126 c17126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17126_16
  · exact m17126_32

def b17127 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 4, region := 456, targets := 34 }], pairs := [(1,0),(2,0),(3,1),(3,5)], upper := (rows 13 98 134 265 49 34 208 208 464), lower := (rows 13 98 134 265 49 34 64 128 256), losses := [] }

theorem u17127 : Upper (D 7) (R 7) [12,96,130,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17128 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 13 98 134 265 49 48 194 194 450), lower := (rows 13 98 134 265 49 48 64 128 256), losses := [] }

theorem u17128 : Upper (D 7) (R 7) [12,96,130,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17128 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17129 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 265 49 96 210 146 402), lower := (rows 13 98 134 265 49 96 64 128 256), losses := [] }

theorem u17129 : Upper (D 7) (R 7) [12,96,130,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17130 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 4, region := 330, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 134 265 49 160 82 210 338), lower := (rows 13 98 134 265 49 160 64 128 256), losses := [] }

theorem u17130 : Upper (D 7) (R 7) [12,96,130,257,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17131 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 13 98 134 265 176 33 82 210 338), lower := (rows 13 98 134 265 176 33 64 128 256), losses := [] }

theorem u17131 : Upper (D 7) (R 7) [12,96,130,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17132 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,6)], upper := (rows 13 98 134 265 176 34 81 209 337), lower := (rows 13 98 134 265 176 34 64 128 256), losses := [] }

theorem u17132 : Upper (D 7) (R 7) [12,96,130,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17133 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 134 265 176 48 67 195 323), lower := (rows 13 98 134 265 176 48 64 128 256), losses := [] }

theorem u17133 : Upper (D 7) (R 7) [12,96,130,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17133 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17134 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 265 176 96 83 147 275), lower := (rows 13 98 134 265 176 96 64 128 256), losses := [] }

theorem u17134 : Upper (D 7) (R 7) [12,96,130,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17135 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 48, targets := 64 }], pairs := [(1,0),(2,0),(3,0),(4,6)], upper := (rows 13 98 134 266 49 33 208 208 464), lower := (rows 13 98 134 266 49 33 64 128 256), losses := [] }

theorem u17135 : Upper (D 7) (R 7) [12,96,130,258,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17136 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 134 266 49 48 193 193 449), lower := (rows 13 98 134 266 49 48 64 128 256), losses := [] }

theorem u17136 : Upper (D 7) (R 7) [12,96,130,258,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17136 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17137 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 266 49 96 209 145 401), lower := (rows 13 98 134 266 49 96 64 128 256), losses := [] }

theorem u17137 : Upper (D 7) (R 7) [12,96,130,258,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17138 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 330, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 13 98 134 266 49 160 81 209 337), lower := (rows 13 98 134 266 49 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 164 0 128 256), good := (rows 61 34 166 266 49 160 0 160 256) }] }

theorem u17138 : Upper (D 7) (R 7) [12,96,130,258,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17139 : Route 9 := (fun mask => (mask,id))

def c17139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17139 : Upper (D 7) (R 7) [12,96,130,258,129,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,258,129,1] 13 (by decide) (choices 1) [16,32] r17139 c17139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4107
  · exact u4108

def b17140 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,7),(3,7),(4,1)], upper := (rows 13 98 134 266 145 48 97 225 353), lower := (rows 13 98 134 266 145 48 64 128 256), losses := [] }

theorem u17140 : Upper (D 7) (R 7) [12,96,130,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17140 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17141 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 266 145 96 113 177 305), lower := (rows 13 98 134 266 145 96 64 128 256), losses := [] }

theorem u17141 : Upper (D 7) (R 7) [12,96,130,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17142 : Route 9 := (fun mask => (mask,id))

def c17142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17142 : Upper (D 7) (R 7) [12,96,130,258,160,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,258,160,1] 13 (by decide) (choices 1) [1,16] r17142 c17142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4109
  · exact u4110

def b17143 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 134 266 176 48 65 193 321), lower := (rows 13 98 134 266 176 48 64 128 256), losses := [] }

theorem u17143 : Upper (D 7) (R 7) [12,96,130,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17143 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17144 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 266 176 96 81 145 273), lower := (rows 13 98 134 266 176 96 64 128 256), losses := [] }

theorem u17144 : Upper (D 7) (R 7) [12,96,130,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17145 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(3,1)], upper := (rows 13 98 134 280 19 33 224 224 480), lower := (rows 13 98 134 280 19 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 54 24 16 32 98 162 290), good := (rows 12 486 454 284 478 486 64 128 256) }] }

theorem u17145 : Upper (D 7) (R 7) [12,96,130,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17146 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 280 19 96 225 161 417), lower := (rows 13 98 134 280 19 96 64 128 256), losses := [] }

theorem u17146 : Upper (D 7) (R 7) [12,96,130,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17147_1 : Upper (D 7) (R 7) [12,96,130,272,3,128,1] 13 :=
  permutation_upper _ _ _ [12,96,130,272,3,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4111

theorem m17147_32 : Upper (D 7) (R 7) [12,96,130,272,3,128,32] 13 :=
  permutation_upper _ _ _ [12,96,130,272,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4112

def r17147 : Route 9 := (fun mask => (mask,id))

def c17147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17147 : Upper (D 7) (R 7) [12,96,130,272,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,130,272,3,128] 13 (by decide) (choices 1) [1,32] r17147 c17147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17147_1
  · exact m17147_32

def b17148 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 13 98 134 280 49 33 194 194 450), lower := (rows 13 98 134 280 49 33 64 128 256), losses := [] }

theorem u17148 : Upper (D 7) (R 7) [12,96,130,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17149 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 456, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 13 98 134 280 49 34 193 193 449), lower := (rows 13 98 134 280 49 34 64 128 256), losses := [] }

theorem u17149 : Upper (D 7) (R 7) [12,96,130,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17150 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 280 49 96 195 131 387), lower := (rows 13 98 134 280 49 96 64 128 256), losses := [] }

theorem u17150 : Upper (D 7) (R 7) [12,96,130,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17151 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 330, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 13 98 134 280 49 160 67 195 323), lower := (rows 13 98 134 280 49 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 164 64 128 256), good := (rows 61 96 164 280 49 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 17 164 0 128 256), good := (rows 61 34 166 280 49 160 0 160 256) }] }

theorem u17151 : Upper (D 7) (R 7) [12,96,130,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17152 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 134 280 145 33 98 226 354), lower := (rows 13 98 134 280 145 33 64 128 256), losses := [] }

theorem u17152 : Upper (D 7) (R 7) [12,96,130,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17153_1 : Upper (D 7) (R 7) [12,96,130,272,129,2,1] 13 :=
  permutation_upper _ _ _ [12,96,130,272,129,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4113

def r17153 : Route 9 := (fun mask => (mask,id))

def c17153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17153 : Upper (D 7) (R 7) [12,96,130,272,129,2] 13 := by
  apply FastRouting.sound _ _ [12,96,130,272,129,2] 13 (by decide) (choices 1) [1,32] r17153 c17153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17153_1
  · exact u4114

def b17154 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 280 145 96 99 163 291), lower := (rows 13 98 134 280 145 96 64 128 256), losses := [] }

theorem u17154 : Upper (D 7) (R 7) [12,96,130,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17155 : Route 9 := (fun mask => (mask,id))

def c17155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17155 : Upper (D 7) (R 7) [12,96,130,272,160,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,272,160,1] 13 (by decide) (choices 1) [1,2] r17155 c17155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4115
  · exact u4116

def b17156 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,6)], upper := (rows 13 98 134 280 176 34 65 193 321), lower := (rows 13 98 134 280 176 34 64 128 256), losses := [] }

theorem u17156 : Upper (D 7) (R 7) [12,96,130,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17157 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 280 176 96 67 131 259), lower := (rows 13 98 134 280 176 96 64 128 256), losses := [] }

theorem u17157 : Upper (D 7) (R 7) [12,96,130,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17158 : Route 9 := (fun mask => (mask,id))

def c17158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17158 : Upper (D 7) (R 7) [12,96,130,288,3,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,3,1] 13 (by decide) (choices 1) [16,128] r17158 c17158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4117
  · exact u4118

def r17159 : Route 9 := (fun mask => (mask,id))

def c17159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17159 : Upper (D 7) (R 7) [12,96,130,288,3,16] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,3,16] 13 (by decide) (choices 1) [1,128] r17159 c17159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4119
  · exact u4120

#print axioms u17159
end Delivery.IrregularNine14.P07
