import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0047
import IrregularNine14P07C0048

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15120 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 44 25 82 33 192 192 448), lower := (rows 7 290 44 25 82 33 64 128 256), losses := [] }

theorem u15120 : Upper (D 7) (R 7) [6,288,40,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15121 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 290 44 25 82 96 193 129 385), lower := (rows 7 290 44 25 82 96 64 128 256), losses := [] }

theorem u15121 : Upper (D 7) (R 7) [6,288,40,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15122 : Route 9 := (fun mask => (mask,id))

def c15122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15122 : Upper (D 7) (R 7) [6,288,40,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,40,17,66,128] 13 (by decide) (choices 1) [1,128] r15122 c15122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2871
  · exact u2872

def b15123 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 290 44 25 208 33 194 194 450), lower := (rows 7 290 44 25 208 33 64 128 256), losses := [] }

theorem u15123 : Upper (D 7) (R 7) [6,288,40,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15124 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 44 25 208 34 193 193 449), lower := (rows 7 290 44 25 208 34 64 128 256), losses := [] }

theorem u15124 : Upper (D 7) (R 7) [6,288,40,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15125 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 7 290 44 25 208 96 195 131 387), lower := (rows 7 290 44 25 208 96 64 128 256), losses := [] }

theorem u15125 : Upper (D 7) (R 7) [6,288,40,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15126 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 44 26 208 33 193 193 449), lower := (rows 7 290 44 26 208 33 64 128 256), losses := [] }

theorem u15126 : Upper (D 7) (R 7) [6,288,40,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15127 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 7 290 44 26 208 96 193 129 385), lower := (rows 7 290 44 26 208 96 64 128 256), losses := [] }

theorem u15127 : Upper (D 7) (R 7) [6,288,40,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15128 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 290 44 73 82 33 208 144 400), lower := (rows 7 290 44 73 82 33 64 128 256), losses := [] }

theorem u15128 : Upper (D 7) (R 7) [6,288,40,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15129 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 44 73 82 48 193 129 385), lower := (rows 7 290 44 73 82 48 64 128 256), losses := [] }

theorem u15129 : Upper (D 7) (R 7) [6,288,40,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15129 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15130 : Route 9 := (fun mask => (mask,id))

def c15130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15130 : Upper (D 7) (R 7) [6,288,40,65,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65,66,128] 13 (by decide) (choices 1) [1,16,128] r15130 c15130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2873
  · exact u2874
  · exact u2875

def b15131 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 44 73 145 34 208 208 464), lower := (rows 7 290 44 73 145 34 64 128 256), losses := [] }

theorem u15131 : Upper (D 7) (R 7) [6,288,40,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15132 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 290 44 73 145 48 194 194 450), lower := (rows 7 290 44 73 145 48 64 128 256), losses := [] }

theorem u15132 : Upper (D 7) (R 7) [6,288,40,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15132 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15133 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 290 44 73 145 96 210 146 402), lower := (rows 7 290 44 73 145 96 64 128 256), losses := [] }

theorem u15133 : Upper (D 7) (R 7) [6,288,40,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15134 : Route 9 := (fun mask => (mask,id))

def c15134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15134 : Upper (D 7) (R 7) [6,288,40,65,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65,129,128] 13 (by decide) (choices 1) [2,16] r15134 c15134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2876
  · exact u2877

def b15135 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 290 44 73 146 33 208 208 464), lower := (rows 7 290 44 73 146 33 64 128 256), losses := [] }

theorem u15135 : Upper (D 7) (R 7) [6,288,40,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15136 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 290 44 73 146 48 193 193 449), lower := (rows 7 290 44 73 146 48 64 128 256), losses := [] }

theorem u15136 : Upper (D 7) (R 7) [6,288,40,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15136 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15137 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 290 44 73 146 96 209 145 401), lower := (rows 7 290 44 73 146 96 64 128 256), losses := [] }

theorem u15137 : Upper (D 7) (R 7) [6,288,40,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15138 : Route 9 := (fun mask => (mask,id))

def c15138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15138 : Upper (D 7) (R 7) [6,288,40,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65,130,128] 13 (by decide) (choices 1) [1,16] r15138 c15138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2878
  · exact u2879

def b15139 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 290 44 73 208 33 210 146 402), lower := (rows 7 290 44 73 208 33 64 128 256), losses := [] }

theorem u15139 : Upper (D 7) (R 7) [6,288,40,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15140 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 44 73 208 34 209 145 401), lower := (rows 7 290 44 73 208 34 64 128 256), losses := [] }

theorem u15140 : Upper (D 7) (R 7) [6,288,40,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15141 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 290 44 73 208 48 195 131 387), lower := (rows 7 290 44 73 208 48 64 128 256), losses := [] }

theorem u15141 : Upper (D 7) (R 7) [6,288,40,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15141 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15142 : Route 9 := (fun mask => (mask,id))

def c15142 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15142 : Upper (D 7) (R 7) [6,288,40,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65,192,128] 13 (by decide) (choices 1) [1,2,16] r15142 c15142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2880
  · exact u2881
  · exact u2882

def b15143 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 44 74 145 33 208 208 464), lower := (rows 7 290 44 74 145 33 64 128 256), losses := [] }

theorem u15143 : Upper (D 7) (R 7) [6,288,40,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15144 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 290 44 74 145 48 193 193 449), lower := (rows 7 290 44 74 145 48 64 128 256), losses := [] }

theorem u15144 : Upper (D 7) (R 7) [6,288,40,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15144 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15145 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,6),(1,6),(3,5),(4,6)], upper := (rows 7 290 44 74 145 96 209 145 401), lower := (rows 7 290 44 74 145 96 64 128 256), losses := [] }

theorem u15145 : Upper (D 7) (R 7) [6,288,40,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15146 : Route 9 := (fun mask => (mask,id))

def c15146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15146 : Upper (D 7) (R 7) [6,288,40,66,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,40,66,129,128] 13 (by decide) (choices 1) [1,16] r15146 c15146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2883
  · exact u2884

def b15147 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 44 74 208 33 209 145 401), lower := (rows 7 290 44 74 208 33 64 128 256), losses := [] }

theorem u15147 : Upper (D 7) (R 7) [6,288,40,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15148 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 290 44 74 208 48 193 129 385), lower := (rows 7 290 44 74 208 48 64 128 256), losses := [] }

theorem u15148 : Upper (D 7) (R 7) [6,288,40,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15148 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15149 : Route 9 := (fun mask => (mask,id))

def c15149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15149 : Upper (D 7) (R 7) [6,288,40,66,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,40,66,192,128] 13 (by decide) (choices 1) [1,16] r15149 c15149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2885
  · exact u2886

def b15150 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 7 290 44 88 145 33 194 194 450), lower := (rows 7 290 44 88 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 38 4 24 16 32 103 167 295), good := (rows 454 482 494 88 472 482 64 128 256) }] }

theorem u15150 : Upper (D 7) (R 7) [6,288,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15151 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 44 88 145 34 193 193 449), lower := (rows 7 290 44 88 145 34 64 128 256), losses := [] }

theorem u15151 : Upper (D 7) (R 7) [6,288,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15152 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 290 44 88 145 96 195 131 387), lower := (rows 7 290 44 88 145 96 64 128 256), losses := [] }

theorem u15152 : Upper (D 7) (R 7) [6,288,40,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15153 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 290 44 88 145 160 67 195 323), lower := (rows 7 290 44 88 145 160 64 128 256), losses := [] }

theorem u15153 : Upper (D 7) (R 7) [6,288,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15154 : Route 9 := (fun mask => (mask,id))

def c15154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15154 : Upper (D 7) (R 7) [6,288,40,80,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,40,80,130,1] 13 (by decide) (choices 1) [1,128] r15154 c15154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2887
  · exact u2888

def b15155 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 290 44 88 146 96 193 129 385), lower := (rows 7 290 44 88 146 96 64 128 256), losses := [] }

theorem u15155 : Upper (D 7) (R 7) [6,288,40,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15156 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 290 44 88 146 160 65 193 321), lower := (rows 7 290 44 88 146 160 64 128 256), losses := [] }

theorem u15156 : Upper (D 7) (R 7) [6,288,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15157 : Route 9 := (fun mask => (mask,id))

def c15157 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15157 : Upper (D 7) (R 7) [6,288,40,192,65,1] 13 := by
  apply FastRouting.sound _ _ [6,288,40,192,65,1] 13 (by decide) (choices 1) [2,16,128] r15157 c15157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2889
  · exact u2890
  · exact u2891

def b15158 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 44 200 81 34 209 145 401), lower := (rows 7 290 44 200 81 34 64 128 256), losses := [] }

theorem u15158 : Upper (D 7) (R 7) [6,288,40,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15159 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 290 44 200 81 48 195 131 387), lower := (rows 7 290 44 200 81 48 64 128 256), losses := [] }

theorem u15159 : Upper (D 7) (R 7) [6,288,40,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15159 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15160 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 44 200 81 160 83 147 275), lower := (rows 7 290 44 200 81 160 64 128 256), losses := [] }

theorem u15160 : Upper (D 7) (R 7) [6,288,40,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15161 : Route 9 := (fun mask => (mask,id))

def c15161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15161 : Upper (D 7) (R 7) [6,288,40,192,66,1] 13 := by
  apply FastRouting.sound _ _ [6,288,40,192,66,1] 13 (by decide) (choices 1) [1,16,128] r15161 c15161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2892
  · exact u2893
  · exact u2894

def b15162 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 290 44 200 82 48 193 129 385), lower := (rows 7 290 44 200 82 48 64 128 256), losses := [] }

theorem u15162 : Upper (D 7) (R 7) [6,288,40,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15162 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15163 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 44 200 82 160 81 145 273), lower := (rows 7 290 44 200 82 160 64 128 256), losses := [] }

theorem u15163 : Upper (D 7) (R 7) [6,288,40,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15164 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 290 69 25 112 34 200 136 392), lower := (rows 7 290 69 25 112 34 64 128 256), losses := [] }

theorem u15164 : Upper (D 7) (R 7) [6,288,65,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15165 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 56, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 7 290 69 25 112 40 194 130 386), lower := (rows 7 290 69 25 112 40 64 128 256), losses := [] }

theorem u15165 : Upper (D 7) (R 7) [6,288,65,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15165 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15166 : Route 9 := (fun mask => (mask,id))

def c15166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15166 : Upper (D 7) (R 7) [6,288,65,17,96,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,96,128] 13 (by decide) (choices 1) [2,8,128] r15166 c15166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2895
  · exact u2896
  · exact u2897

def b15167 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 290 69 25 146 40 224 224 480), lower := (rows 7 290 69 25 146 40 64 128 256), losses := [] }

theorem u15167 : Upper (D 7) (R 7) [6,288,65,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15167 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15168 : Route 9 := (fun mask => (mask,id))

def c15168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15168 : Upper (D 7) (R 7) [6,288,65,17,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,130,64] 13 (by decide) (choices 1) [8,32,128] r15168 c15168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2898
  · exact u2899
  · exact u2900

def r15169 : Route 9 := (fun mask => (mask,id))

def c15169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15169 : Upper (D 7) (R 7) [6,288,65,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,130,128] 13 (by decide) (choices 1) [8,32] r15169 c15169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2901
  · exact u2902

def b15170 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 290 69 25 152 34 224 224 480), lower := (rows 7 290 69 25 152 34 64 128 256), losses := [] }

theorem u15170 : Upper (D 7) (R 7) [6,288,65,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15171 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,6),(4,0)], upper := (rows 7 290 69 25 152 96 226 162 418), lower := (rows 7 290 69 25 152 96 64 128 256), losses := [{ target := 6, region := (rows 1 34 4 13 17 32 0 162 290), good := (rows 415 418 29 25 152 418 0 128 256) }] }

theorem u15171 : Upper (D 7) (R 7) [6,288,65,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15172 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 290 69 25 152 160 98 226 354), lower := (rows 7 290 69 25 152 160 64 128 256), losses := [] }

theorem u15172 : Upper (D 7) (R 7) [6,288,65,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15173 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 290 69 25 176 34 200 200 456), lower := (rows 7 290 69 25 176 34 64 128 256), losses := [] }

theorem u15173 : Upper (D 7) (R 7) [6,288,65,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15174 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 290 69 25 176 40 194 194 450), lower := (rows 7 290 69 25 176 40 64 128 256), losses := [] }

theorem u15174 : Upper (D 7) (R 7) [6,288,65,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15174 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15175 : Route 9 := (fun mask => (mask,id))

def c15175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15175 : Upper (D 7) (R 7) [6,288,65,17,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,160,64] 13 (by decide) (choices 1) [2,8,128] r15175 c15175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2903
  · exact u2904
  · exact u2905

def b15176 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 69 25 176 160 74 202 330), lower := (rows 7 290 69 25 176 160 64 128 256), losses := [] }

theorem u15176 : Upper (D 7) (R 7) [6,288,65,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15177 : PairBound 9 := { available := 168, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 290 69 25 208 34 232 168 424), lower := (rows 7 290 69 25 208 34 64 128 256), losses := [] }

theorem u15177 : Upper (D 7) (R 7) [6,288,65,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15178 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 25 208 40 226 162 418), lower := (rows 7 290 69 25 208 40 64 128 256), losses := [] }

theorem u15178 : Upper (D 7) (R 7) [6,288,65,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15178 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15179 : Route 9 := (fun mask => (mask,id))

def c15179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15179 : Upper (D 7) (R 7) [6,288,65,17,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,192,128] 13 (by decide) (choices 1) [2,8,32] r15179 c15179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2906
  · exact u2907
  · exact u2908

#print axioms u15179
end Delivery.IrregularNine14.P07
