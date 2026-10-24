import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0252
import IrregularNine14P07C0253

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32100 : Route 9 := (fun mask => (mask,id))

def c32100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32100 : Upper (D 7) (R 7) [6,288,40,65,129] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65,129] 13 (by decide) (choices 1) [2,16,64,128] r32100 c32100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15131
  · exact u15132
  · exact u15133
  · exact u15134

def r32101 : Route 9 := (fun mask => (mask,id))

def c32101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32101 : Upper (D 7) (R 7) [6,288,40,65,130] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65,130] 13 (by decide) (choices 1) [1,16,64,128] r32101 c32101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15135
  · exact u15136
  · exact u15137
  · exact u15138

def r32102 : Route 9 := (fun mask => (mask,id))

def c32102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32102 : Upper (D 7) (R 7) [6,288,40,65,192] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65,192] 13 (by decide) (choices 1) [1,2,16,128] r32102 c32102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15139
  · exact u15140
  · exact u15141
  · exact u15142

def b32103 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(3,5),(4,1),(4,5)], upper := (rows 7 290 44 74 81 177 209 145 401), lower := (rows 7 290 44 74 81 32 64 128 256), losses := [] }

theorem u32103 : Upper (D 7) (R 7) [6,288,40,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32104 : Route 9 := (fun mask => (mask,id))

def c32104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32104 : Upper (D 7) (R 7) [6,288,40,66,129] 13 := by
  apply FastRouting.sound _ _ [6,288,40,66,129] 13 (by decide) (choices 1) [1,16,64,128] r32104 c32104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15143
  · exact u15144
  · exact u15145
  · exact u15146

def r32105 : Route 9 := (fun mask => (mask,id))

def c32105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32105 : Upper (D 7) (R 7) [6,288,40,66,192] 13 := by
  apply FastRouting.sound _ _ [6,288,40,66,192] 13 (by decide) (choices 1) [1,16,128] r32105 c32105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15147
  · exact u15148
  · exact u15149

def b32106 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 290 44 88 19 225 193 193 449), lower := (rows 7 290 44 88 19 32 64 128 256), losses := [] }

theorem u32106 : Upper (D 7) (R 7) [6,288,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32107 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 290 44 88 81 163 195 131 387), lower := (rows 7 290 44 88 81 32 64 128 256), losses := [] }

theorem u32107 : Upper (D 7) (R 7) [6,288,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32108 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 290 44 88 82 161 193 129 385), lower := (rows 7 290 44 88 82 32 64 128 256), losses := [] }

theorem u32108 : Upper (D 7) (R 7) [6,288,40,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32109 : Route 9 := (fun mask => (mask,id))

def c32109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32109 : Upper (D 7) (R 7) [6,288,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,288,40,80,129] 13 (by decide) (choices 1) [1,2,64,128] r32109 c32109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15150
  · exact u15151
  · exact u15152
  · exact u15153

def r32110 : Route 9 := (fun mask => (mask,id))

def c32110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32110 : Upper (D 7) (R 7) [6,288,40,80,130] 13 := by
  apply FastRouting.sound _ _ [6,288,40,80,130] 13 (by decide) (choices 1) [1,64,128] r32110 c32110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15154
  · exact u15155
  · exact u15156

def b32111 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 290 44 88 208 163 195 131 387), lower := (rows 7 290 44 88 208 32 64 128 256), losses := [] }

theorem u32111 : Upper (D 7) (R 7) [6,288,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32112 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 290 44 200 19 241 209 209 465), lower := (rows 7 290 44 200 19 32 64 128 256), losses := [] }

theorem u32112 : Upper (D 7) (R 7) [6,288,40,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32113 : Route 9 := (fun mask => (mask,id))

def c32113 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32113 : Upper (D 7) (R 7) [6,288,40,192,65] 13 := by
  apply FastRouting.sound _ _ [6,288,40,192,65] 13 (by decide) (choices 1) [1,2,16,128] r32113 c32113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15157
  · exact u15158
  · exact u15159
  · exact u15160

def r32114 : Route 9 := (fun mask => (mask,id))

def c32114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32114 : Upper (D 7) (R 7) [6,288,40,192,66] 13 := by
  apply FastRouting.sound _ _ [6,288,40,192,66] 13 (by decide) (choices 1) [1,16,128] r32114 c32114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15161
  · exact u15162
  · exact u15163

def b32115 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 290 44 200 208 51 83 147 275), lower := (rows 7 290 44 200 208 32 64 128 256), losses := [] }

theorem u32115 : Upper (D 7) (R 7) [6,288,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32116 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 290 69 11 56 240 208 208 464), lower := (rows 7 290 69 11 56 32 64 128 256), losses := [] }

theorem u32116 : Upper (D 7) (R 7) [6,288,65,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32117 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 290 69 11 88 176 240 176 432), lower := (rows 7 290 69 11 88 32 64 128 256), losses := [] }

theorem u32117 : Upper (D 7) (R 7) [6,288,65,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32118 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 290 69 11 112 184 216 152 408), lower := (rows 7 290 69 11 112 32 64 128 256), losses := [] }

theorem u32118 : Upper (D 7) (R 7) [6,288,65,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32119 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 290 69 11 152 240 240 240 496), lower := (rows 7 290 69 11 152 32 64 128 256), losses := [] }

theorem u32119 : Upper (D 7) (R 7) [6,288,65,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32120 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 290 69 11 176 248 216 216 472), lower := (rows 7 290 69 11 176 32 64 128 256), losses := [] }

theorem u32120 : Upper (D 7) (R 7) [6,288,65,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32121 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 290 69 11 208 184 248 184 440), lower := (rows 7 290 69 11 208 32 64 128 256), losses := [] }

theorem u32121 : Upper (D 7) (R 7) [6,288,65,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32122 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 69 25 26 224 224 224 480), lower := (rows 7 290 69 25 26 32 64 128 256), losses := [] }

theorem u32122 : Upper (D 7) (R 7) [6,288,65,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32123 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 290 69 25 50 232 200 200 456), lower := (rows 7 290 69 25 50 32 64 128 256), losses := [] }

theorem u32123 : Upper (D 7) (R 7) [6,288,65,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32124 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,0)], upper := (rows 7 290 69 25 56 226 194 194 450), lower := (rows 7 290 69 25 56 32 64 128 256), losses := [] }

theorem u32124 : Upper (D 7) (R 7) [6,288,65,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32125 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 25 82 168 232 168 424), lower := (rows 7 290 69 25 82 32 64 128 256), losses := [] }

theorem u32125 : Upper (D 7) (R 7) [6,288,65,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32126 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 7 290 69 25 88 162 226 162 418), lower := (rows 7 290 69 25 88 32 64 128 256), losses := [] }

theorem u32126 : Upper (D 7) (R 7) [6,288,65,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32127 : Route 9 := (fun mask => (mask,id))

def c32127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32127 : Upper (D 7) (R 7) [6,288,65,17,96] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,96] 13 (by decide) (choices 1) [2,8,128] r32127 c32127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15164
  · exact u15165
  · exact u15166

def r32128 : Route 9 := (fun mask => (mask,id))

def c32128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32128 : Upper (D 7) (R 7) [6,288,65,17,130] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,130] 13 (by decide) (choices 1) [8,64,128] r32128 c32128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15167
  · exact u15168
  · exact u15169

def r32129 : Route 9 := (fun mask => (mask,id))

def c32129 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32129 : Upper (D 7) (R 7) [6,288,65,17,136] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,136] 13 (by decide) (choices 1) [2,64,128] r32129 c32129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15170
  · exact u15171
  · exact u15172

def r32130 : Route 9 := (fun mask => (mask,id))

def c32130 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32130 : Upper (D 7) (R 7) [6,288,65,17,160] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,160] 13 (by decide) (choices 1) [2,8,64,128] r32130 c32130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15173
  · exact u15174
  · exact u15175
  · exact u15176

def r32131 : Route 9 := (fun mask => (mask,id))

def c32131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32131 : Upper (D 7) (R 7) [6,288,65,17,192] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17,192] 13 (by decide) (choices 1) [2,8,128] r32131 c32131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15177
  · exact u15178
  · exact u15179

def b32132 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 197, targets := 32 },{ cop := 4, region := 458, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,0)], upper := (rows 7 290 69 26 49 232 200 200 456), lower := (rows 7 290 69 26 49 32 64 128 256), losses := [] }

theorem u32132 : Upper (D 7) (R 7) [6,288,65,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32133 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 7 290 69 26 56 225 193 193 449), lower := (rows 7 290 69 26 56 32 64 128 256), losses := [] }

theorem u32133 : Upper (D 7) (R 7) [6,288,65,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32134 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 7 290 69 26 81 168 232 168 424), lower := (rows 7 290 69 26 81 32 64 128 256), losses := [] }

theorem u32134 : Upper (D 7) (R 7) [6,288,65,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32135 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(3,0)], upper := (rows 7 290 69 26 88 161 225 161 417), lower := (rows 7 290 69 26 88 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 32 64 128 256), good := (rows 30 290 92 26 88 32 64 128 256) }] }

theorem u32135 : Upper (D 7) (R 7) [6,288,65,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32136 : Route 9 := (fun mask => (mask,id))

def c32136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32136 : Upper (D 7) (R 7) [6,288,65,18,96] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,96] 13 (by decide) (choices 1) [1,8,128] r32136 c32136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15180
  · exact u15181
  · exact u15182

def r32137 : Route 9 := (fun mask => (mask,id))

def c32137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32137 : Upper (D 7) (R 7) [6,288,65,18,129] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,129] 13 (by decide) (choices 1) [8,64,128] r32137 c32137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15183
  · exact u15184
  · exact u15185

def r32138 : Route 9 := (fun mask => (mask,id))

def c32138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32138 : Upper (D 7) (R 7) [6,288,65,18,136] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,136] 13 (by decide) (choices 1) [1,64,128] r32138 c32138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15186
  · exact u15187
  · exact u15188

def r32139 : Route 9 := (fun mask => (mask,id))

def c32139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32139 : Upper (D 7) (R 7) [6,288,65,18,160] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,160] 13 (by decide) (choices 1) [1,8,64,128] r32139 c32139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15189
  · exact u15190
  · exact u15191
  · exact u15192

def r32140 : Route 9 := (fun mask => (mask,id))

def c32140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32140 : Upper (D 7) (R 7) [6,288,65,18,192] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,192] 13 (by decide) (choices 1) [1,8,128] r32140 c32140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15193
  · exact u15194
  · exact u15195

def b32141 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 41 82 184 216 152 408), lower := (rows 7 290 69 41 82 32 64 128 256), losses := [] }

theorem u32141 : Upper (D 7) (R 7) [6,288,65,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32142 : Route 9 := (fun mask => (mask,id))

def c32142 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32142 : Upper (D 7) (R 7) [6,288,65,33,72] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,72] 13 (by decide) (choices 1) [2,16,128] r32142 c32142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15196
  · exact u15197
  · exact u15198

def r32143 : Route 9 := (fun mask => (mask,id))

def c32143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u32143 : Upper (D 7) (R 7) [6,288,65,33,130] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,130] 13 (by decide) (choices 1) [8,16,64,128] r32143 c32143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15199
  · exact u15200
  · exact u15201
  · exact u15202

def r32144 : Route 9 := (fun mask => (mask,id))

def c32144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32144 : Upper (D 7) (R 7) [6,288,65,33,136] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,136] 13 (by decide) (choices 1) [2,16,64,128] r32144 c32144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15203
  · exact u15204
  · exact u15205
  · exact u15206

def r32145 : Route 9 := (fun mask => (mask,id))

def c32145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32145 : Upper (D 7) (R 7) [6,288,65,33,192] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,192] 13 (by decide) (choices 1) [2,8,16,128] r32145 c32145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15207
  · exact u15208
  · exact u15209
  · exact u15210

def b32146 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 69 42 88 177 209 145 401), lower := (rows 7 290 69 42 88 32 64 128 256), losses := [] }

theorem u32146 : Upper (D 7) (R 7) [6,288,65,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32147 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 69 42 145 248 216 216 472), lower := (rows 7 290 69 42 145 32 64 128 256), losses := [] }

theorem u32147 : Upper (D 7) (R 7) [6,288,65,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32148 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 69 42 152 241 209 209 465), lower := (rows 7 290 69 42 152 32 64 128 256), losses := [] }

theorem u32148 : Upper (D 7) (R 7) [6,288,65,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32149 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 69 42 208 185 217 153 409), lower := (rows 7 290 69 42 208 32 64 128 256), losses := [] }

theorem u32149 : Upper (D 7) (R 7) [6,288,65,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32150 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 7 290 69 56 81 170 202 138 394), lower := (rows 7 290 69 56 81 32 64 128 256), losses := [] }

theorem u32150 : Upper (D 7) (R 7) [6,288,65,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32151 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 56 82 169 201 137 393), lower := (rows 7 290 69 56 82 32 64 128 256), losses := [] }

theorem u32151 : Upper (D 7) (R 7) [6,288,65,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32152 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,5),(0,6),(1,6),(2,5)], upper := (rows 7 290 69 56 88 163 195 131 387), lower := (rows 7 290 69 56 88 32 64 128 256), losses := [] }

theorem u32152 : Upper (D 7) (R 7) [6,288,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32153 : Route 9 := (fun mask => (mask,id))

def c32153 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32153 : Upper (D 7) (R 7) [6,288,65,48,129] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,129] 13 (by decide) (choices 1) [2,8,64,128] r32153 c32153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15211
  · exact u15212
  · exact u15213
  · exact u15214

def r32154 : Route 9 := (fun mask => (mask,id))

def c32154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32154 : Upper (D 7) (R 7) [6,288,65,48,130] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,130] 13 (by decide) (choices 1) [1,8,64,128] r32154 c32154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15215
  · exact u15216
  · exact u15217
  · exact u15218

def r32155 : Route 9 := (fun mask => (mask,id))

def c32155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32155 : Upper (D 7) (R 7) [6,288,65,48,136] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,136] 13 (by decide) (choices 1) [1,2,64,128] r32155 c32155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15219
  · exact u15220
  · exact u15221
  · exact u15222

def r32156 : Route 9 := (fun mask => (mask,id))

def c32156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32156 : Upper (D 7) (R 7) [6,288,65,48,192] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,192] 13 (by decide) (choices 1) [1,2,8,128] r32156 c32156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15223
  · exact u15224
  · exact u15225
  · exact u15226

def b32157 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 7 290 69 73 146 184 248 184 440), lower := (rows 7 290 69 73 146 32 64 128 256), losses := [] }

theorem u32157 : Upper (D 7) (R 7) [6,288,65,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32158 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 7 290 69 73 152 178 242 178 434), lower := (rows 7 290 69 73 152 32 64 128 256), losses := [] }

theorem u32158 : Upper (D 7) (R 7) [6,288,65,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32159 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 7 290 69 73 176 186 218 154 410), lower := (rows 7 290 69 73 176 32 64 128 256), losses := [] }

theorem u32159 : Upper (D 7) (R 7) [6,288,65,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u32159
end Delivery.IrregularNine14.P07
