import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0184
import IrregularNine14P07C0185

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29100 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 262 44 138 19 160 81 209 337), lower := (rows 97 262 44 138 19 160 64 128 256), losses := [] }

theorem u29100 : Upper (D 7) (R 7) [96,260,40,130,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29101 : Route 9 := (fun mask => (mask,id))

def c29101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29101 : Upper (D 7) (R 7) [96,260,40,130,66,1] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,66,1] 13 (by decide) (choices 1) [1,16,128] r29101 c29101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11071
  · exact u11072
  · exact u11073

def b29102 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 138 82 48 193 129 385), lower := (rows 97 262 44 138 82 48 64 128 256), losses := [] }

theorem u29102 : Upper (D 7) (R 7) [96,260,40,130,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29102 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29103 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 262 44 138 82 160 81 145 273), lower := (rows 97 262 44 138 82 160 64 128 256), losses := [] }

theorem u29103 : Upper (D 7) (R 7) [96,260,40,130,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29104 : Route 9 := (fun mask => (mask,id))

def c29104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29104 : Upper (D 7) (R 7) [96,260,40,130,129,1] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,129,1] 13 (by decide) (choices 1) [2,16] r29104 c29104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11074
  · exact u11075

def b29105 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,0),(2,6),(2,7),(4,1)], upper := (rows 97 262 44 138 145 34 81 209 337), lower := (rows 97 262 44 138 145 34 64 128 256), losses := [] }

theorem u29105 : Upper (D 7) (R 7) [96,260,40,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29106 : Route 9 := (fun mask => (mask,id))

def c29106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29106 : Upper (D 7) (R 7) [96,260,40,130,129,16] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,129,16] 13 (by decide) (choices 1) [1,2] r29106 c29106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11076
  · exact u11077

def b29107 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 138 145 96 83 147 275), lower := (rows 97 262 44 138 145 96 64 128 256), losses := [] }

theorem u29107 : Upper (D 7) (R 7) [96,260,40,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29108 : Route 9 := (fun mask => (mask,id))

def c29108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29108 : Upper (D 7) (R 7) [96,260,40,130,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,192,1] 13 (by decide) (choices 1) [1,2,16] r29108 c29108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11078
  · exact u11079
  · exact u11080

def b29109 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 36, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,0),(2,6),(2,7),(4,1)], upper := (rows 97 262 44 138 208 34 81 145 273), lower := (rows 97 262 44 138 208 34 64 128 256), losses := [] }

theorem u29109 : Upper (D 7) (R 7) [96,260,40,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29110 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 138 208 48 67 131 259), lower := (rows 97 262 44 138 208 48 64 128 256), losses := [] }

theorem u29110 : Upper (D 7) (R 7) [96,260,40,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29110 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29111 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 4, region := 200, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 97 262 44 152 19 33 194 194 450), lower := (rows 97 262 44 152 19 33 64 128 256), losses := [] }

theorem u29111 : Upper (D 7) (R 7) [96,260,40,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29112 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 200, targets := 34 },{ cop := 2, region := 193, targets := 2 }], pairs := [(0,1),(2,0),(3,1),(3,5)], upper := (rows 97 262 44 152 19 34 193 193 449), lower := (rows 97 262 44 152 19 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 50 64 128 256), good := (rows 96 294 44 188 50 34 64 128 256) }] }

theorem u29112 : Upper (D 7) (R 7) [96,260,40,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29113 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 152 19 96 195 131 387), lower := (rows 97 262 44 152 19 96 64 128 256), losses := [] }

theorem u29113 : Upper (D 7) (R 7) [96,260,40,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29114 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 262 44 152 19 160 67 195 323), lower := (rows 97 262 44 152 19 160 64 128 256), losses := [] }

theorem u29114 : Upper (D 7) (R 7) [96,260,40,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29115 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 152 82 33 195 131 387), lower := (rows 97 262 44 152 82 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 121 64 128 256), good := (rows 97 260 44 189 113 33 97 128 256) },{ target := 7, region := (rows 81 2 12 8 16 121 64 0 256), good := (rows 97 262 44 61 115 33 97 0 256) }] }

theorem u29115 : Upper (D 7) (R 7) [96,260,40,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29116 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 193, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,0),(3,1)], upper := (rows 97 262 44 152 82 34 193 129 385), lower := (rows 97 262 44 152 82 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 50 64 128 256), good := (rows 96 294 44 188 114 34 64 128 256) },{ target := 1, region := (rows 37 0 4 24 16 32 103 167 295), good := (rows 481 453 493 152 472 481 64 128 256) }] }

theorem u29116 : Upper (D 7) (R 7) [96,260,40,144,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29117 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 262 44 152 82 160 67 131 259), lower := (rows 97 262 44 152 82 160 64 128 256), losses := [] }

theorem u29117 : Upper (D 7) (R 7) [96,260,40,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29118 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 200 19 33 210 146 402), lower := (rows 97 262 44 200 19 33 64 128 256), losses := [] }

theorem u29118 : Upper (D 7) (R 7) [96,260,40,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29119 : Route 9 := (fun mask => (mask,id))

def c29119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29119 : Upper (D 7) (R 7) [96,260,40,192,3,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,3,2] 13 (by decide) (choices 1) [1,16,128] r29119 c29119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11081
  · exact u11082
  · exact u11083

def r29120 : Route 9 := (fun mask => (mask,id))

def c29120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29120 : Upper (D 7) (R 7) [96,260,40,192,3,16] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,3,16] 13 (by decide) (choices 1) [1,2,128] r29120 c29120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11084
  · exact u11085
  · exact u11086

def b29121 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 262 44 200 19 160 83 147 275), lower := (rows 97 262 44 200 19 160 64 128 256), losses := [] }

theorem u29121 : Upper (D 7) (R 7) [96,260,40,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29122 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 97 262 44 200 145 33 82 146 274), lower := (rows 97 262 44 200 145 33 64 128 256), losses := [] }

theorem u29122 : Upper (D 7) (R 7) [96,260,40,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29123 : Route 9 := (fun mask => (mask,id))

def c29123 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29123 : Upper (D 7) (R 7) [96,260,40,192,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,129,2] 13 (by decide) (choices 1) [1,2,16] r29123 c29123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11087
  · exact u11088
  · exact u11089

def b29124 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 262 44 200 145 48 67 131 259), lower := (rows 97 262 44 200 145 48 64 128 256), losses := [] }

theorem u29124 : Upper (D 7) (R 7) [96,260,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29124 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29125 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 200 146 33 83 147 275), lower := (rows 97 262 44 200 146 33 64 128 256), losses := [] }

theorem u29125 : Upper (D 7) (R 7) [96,260,40,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29126 : Route 9 := (fun mask => (mask,id))

def c29126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29126 : Upper (D 7) (R 7) [96,260,40,192,130,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,130,2] 13 (by decide) (choices 1) [1,16] r29126 c29126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11090
  · exact u11091

def r29127 : Route 9 := (fun mask => (mask,id))

def c29127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29127 : Upper (D 7) (R 7) [96,260,40,192,130,16] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,130,16] 13 (by decide) (choices 1) [1,2] r29127 c29127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11092
  · exact u11093

def b29128 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 48, targets := 192 },{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(4,6),(4,7)], upper := (rows 97 262 133 11 50 40 208 208 464), lower := (rows 97 262 133 11 50 40 64 128 256), losses := [] }

theorem u29128 : Upper (D 7) (R 7) [96,260,129,3,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29128 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29129 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 133 11 50 48 200 200 456), lower := (rows 97 262 133 11 50 48 64 128 256), losses := [] }

theorem u29129 : Upper (D 7) (R 7) [96,260,129,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29129 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29130 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 11 50 96 216 152 408), lower := (rows 97 262 133 11 50 96 64 128 256), losses := [] }

theorem u29130 : Upper (D 7) (R 7) [96,260,129,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29131 : PairBound 9 := { available := 88, camps := [{ cop := 4, region := 73, targets := 128 },{ cop := 3, region := 240, targets := 1 }], pairs := [(0,7),(3,7),(4,0),(4,6)], upper := (rows 97 262 133 11 50 160 88 216 344), lower := (rows 97 262 133 11 50 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 18 164 0 128 256), good := (rows 33 310 165 27 50 160 0 160 256) }] }

theorem u29131 : Upper (D 7) (R 7) [96,260,129,3,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29132 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 48, targets := 192 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(4,6),(4,7)], upper := (rows 97 262 133 11 56 34 208 208 464), lower := (rows 97 262 133 11 56 34 64 128 256), losses := [] }

theorem u29132 : Upper (D 7) (R 7) [96,260,129,3,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29133 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 133 11 56 48 194 194 450), lower := (rows 97 262 133 11 56 48 64 128 256), losses := [] }

theorem u29133 : Upper (D 7) (R 7) [96,260,129,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29133 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29134 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 11 56 96 210 146 402), lower := (rows 97 262 133 11 56 96 64 128 256), losses := [] }

theorem u29134 : Upper (D 7) (R 7) [96,260,129,3,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29135 : Route 9 := (fun mask => (mask,id))

def c29135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29135 : Upper (D 7) (R 7) [96,260,129,3,40,128] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,40,128] 13 (by decide) (choices 1) [2,16] r29135 c29135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11094
  · exact u11095

def b29136 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 3, region := 240, targets := 1 }], pairs := [(0,7),(3,7),(4,0)], upper := (rows 97 262 133 11 146 40 112 240 368), lower := (rows 97 262 133 11 146 40 64 128 256), losses := [] }

theorem u29136 : Upper (D 7) (R 7) [96,260,129,3,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29136 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29137 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 3, region := 240, targets := 1 }], pairs := [(0,7),(3,7),(4,0)], upper := (rows 97 262 133 11 146 48 104 232 360), lower := (rows 97 262 133 11 146 48 64 128 256), losses := [] }

theorem u29137 : Upper (D 7) (R 7) [96,260,129,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29137 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29138 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 11 146 96 120 184 312), lower := (rows 97 262 133 11 146 96 64 128 256), losses := [] }

theorem u29138 : Upper (D 7) (R 7) [96,260,129,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29139 : Route 9 := (fun mask => (mask,id))

def c29139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29139 : Upper (D 7) (R 7) [96,260,129,3,136,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,136,2] 13 (by decide) (choices 1) [16,32] r29139 c29139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11096
  · exact u11097

theorem m29140_2 : Upper (D 7) (R 7) [96,260,129,3,136,16,2] 13 :=
  permutation_upper _ _ _ [96,260,129,3,136,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11096

def r29140 : Route 9 := (fun mask => (mask,id))

def c29140 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29140 : Upper (D 7) (R 7) [96,260,129,3,136,16] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,136,16] 13 (by decide) (choices 1) [2,32] r29140 c29140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29140_2
  · exact u11098

def b29141 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 11 152 96 114 178 306), lower := (rows 97 262 133 11 152 96 64 128 256), losses := [] }

theorem u29141 : Upper (D 7) (R 7) [96,260,129,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29142 : Route 9 := (fun mask => (mask,id))

def c29142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29142 : Upper (D 7) (R 7) [96,260,129,3,160,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,160,2] 13 (by decide) (choices 1) [8,16] r29142 c29142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11099
  · exact u11100

def r29143 : Route 9 := (fun mask => (mask,id))

def c29143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29143 : Upper (D 7) (R 7) [96,260,129,3,160,8] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,160,8] 13 (by decide) (choices 1) [2,16] r29143 c29143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11101
  · exact u11102

def b29144 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 133 11 176 48 74 202 330), lower := (rows 97 262 133 11 176 48 64 128 256), losses := [] }

theorem u29144 : Upper (D 7) (R 7) [96,260,129,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29144 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29145 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 11 176 96 90 154 282), lower := (rows 97 262 133 11 176 96 64 128 256), losses := [] }

theorem u29145 : Upper (D 7) (R 7) [96,260,129,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29146 : Route 9 := (fun mask => (mask,id))

def c29146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u29146 : Upper (D 7) (R 7) [96,260,129,17,10,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,10,2] 13 (by decide) (choices 1) [32,128] r29146 c29146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11103
  · exact u11104

def b29147 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 25 26 96 226 162 418), lower := (rows 97 262 133 25 26 96 64 128 256), losses := [] }

theorem u29147 : Upper (D 7) (R 7) [96,260,129,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m29148_2 : Upper (D 7) (R 7) [96,260,129,17,10,128,2] 13 :=
  permutation_upper _ _ _ [96,260,129,17,10,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11104

theorem m29148_32 : Upper (D 7) (R 7) [96,260,129,17,10,128,32] 13 :=
  permutation_upper _ _ _ [96,260,129,17,10,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11105

def r29148 : Route 9 := (fun mask => (mask,id))

def c29148 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29148 : Upper (D 7) (R 7) [96,260,129,17,10,128] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,10,128] 13 (by decide) (choices 1) [2,32] r29148 c29148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29148_2
  · exact m29148_32

def b29149 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 201, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 97 262 133 25 50 34 200 200 456), lower := (rows 97 262 133 25 50 34 64 128 256), losses := [] }

theorem u29149 : Upper (D 7) (R 7) [96,260,129,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29150 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 322, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 97 262 133 25 50 40 194 194 450), lower := (rows 97 262 133 25 50 40 64 128 256), losses := [] }

theorem u29150 : Upper (D 7) (R 7) [96,260,129,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29150 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29151 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 25 50 96 202 138 394), lower := (rows 97 262 133 25 50 96 64 128 256), losses := [] }

theorem u29151 : Upper (D 7) (R 7) [96,260,129,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29152 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 73, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,7)], upper := (rows 97 262 133 25 50 160 74 202 330), lower := (rows 97 262 133 25 50 160 64 128 256), losses := [] }

theorem u29152 : Upper (D 7) (R 7) [96,260,129,17,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29153 : Route 9 := (fun mask => (mask,id))

def c29153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29153 : Upper (D 7) (R 7) [96,260,129,17,130,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,130,2] 13 (by decide) (choices 1) [8,32] r29153 c29153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11106
  · exact u11107

theorem m29154_2 : Upper (D 7) (R 7) [96,260,129,17,130,8,2] 13 :=
  permutation_upper _ _ _ [96,260,129,17,130,2,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11106

def r29154 : Route 9 := (fun mask => (mask,id))

def c29154 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29154 : Upper (D 7) (R 7) [96,260,129,17,130,8] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,130,8] 13 (by decide) (choices 1) [2,32] r29154 c29154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29154_2
  · exact u11108

def b29155 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 25 146 96 106 170 298), lower := (rows 97 262 133 25 146 96 64 128 256), losses := [] }

theorem u29155 : Upper (D 7) (R 7) [96,260,129,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29156 : Route 9 := (fun mask => (mask,id))

def c29156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29156 : Upper (D 7) (R 7) [96,260,129,17,160,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,17,160,2] 13 (by decide) (choices 1) [2,8] r29156 c29156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11109
  · exact u11110

def b29157 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 97 262 133 25 176 40 66 194 322), lower := (rows 97 262 133 25 176 40 64 128 256), losses := [] }

theorem u29157 : Upper (D 7) (R 7) [96,260,129,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29157 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29158 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 25 176 96 74 138 266), lower := (rows 97 262 133 25 176 96 64 128 256), losses := [] }

theorem u29158 : Upper (D 7) (R 7) [96,260,129,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29159 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(2,5)], upper := (rows 97 262 133 26 56 33 194 194 450), lower := (rows 97 262 133 26 56 33 64 128 256), losses := [] }

theorem u29159 : Upper (D 7) (R 7) [96,260,129,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29159
end Delivery.IrregularNine14.P07
