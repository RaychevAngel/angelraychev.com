import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0048
import IrregularNine14P07C0049

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15180 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 7 290 69 26 112 33 200 136 392), lower := (rows 7 290 69 26 112 33 64 128 256), losses := [] }

theorem u15180 : Upper (D 7) (R 7) [6,288,65,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15181 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,1),(2,5)], upper := (rows 7 290 69 26 112 40 193 129 385), lower := (rows 7 290 69 26 112 40 64 128 256), losses := [] }

theorem u15181 : Upper (D 7) (R 7) [6,288,65,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15181 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15182 : Route 9 := (fun mask => (mask,id))

def c15182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15182 : Upper (D 7) (R 7) [6,288,65,18,96,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,96,128] 13 (by decide) (choices 1) [1,8,128] r15182 c15182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2909
  · exact u2910
  · exact u2911

def b15183 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 7 290 69 26 145 40 224 224 480), lower := (rows 7 290 69 26 145 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 40 106 170 298), good := (rows 469 480 85 504 149 488 64 128 256) }] }

theorem u15183 : Upper (D 7) (R 7) [6,288,65,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15183 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15184 : Route 9 := (fun mask => (mask,id))

def c15184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15184 : Upper (D 7) (R 7) [6,288,65,18,129,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,129,64] 13 (by decide) (choices 1) [8,32,128] r15184 c15184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2912
  · exact u2913
  · exact u2914

def r15185 : Route 9 := (fun mask => (mask,id))

def c15185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15185 : Upper (D 7) (R 7) [6,288,65,18,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,129,128] 13 (by decide) (choices 1) [8,32] r15185 c15185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2915
  · exact u2916

def b15186 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 290 69 26 152 33 224 224 480), lower := (rows 7 290 69 26 152 33 64 128 256), losses := [] }

theorem u15186 : Upper (D 7) (R 7) [6,288,65,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15187 : Route 9 := (fun mask => (mask,id))

def c15187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15187 : Upper (D 7) (R 7) [6,288,65,18,136,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,136,64] 13 (by decide) (choices 1) [1,32,128] r15187 c15187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2917
  · exact u2918
  · exact u2919

def b15188 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 7 290 69 26 152 160 97 225 353), lower := (rows 7 290 69 26 152 160 64 128 256), losses := [] }

theorem u15188 : Upper (D 7) (R 7) [6,288,65,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15189 : PairBound 9 := { available := 200, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 290 69 26 176 33 200 200 456), lower := (rows 7 290 69 26 176 33 64 128 256), losses := [] }

theorem u15189 : Upper (D 7) (R 7) [6,288,65,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15190 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,1),(2,5)], upper := (rows 7 290 69 26 176 40 193 193 449), lower := (rows 7 290 69 26 176 40 64 128 256), losses := [] }

theorem u15190 : Upper (D 7) (R 7) [6,288,65,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15190 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15191 : Route 9 := (fun mask => (mask,id))

def c15191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15191 : Upper (D 7) (R 7) [6,288,65,18,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,160,64] 13 (by decide) (choices 1) [1,8,128] r15191 c15191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2920
  · exact u2921
  · exact u2922

def b15192 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 69 26 176 160 73 201 329), lower := (rows 7 290 69 26 176 160 64 128 256), losses := [] }

theorem u15192 : Upper (D 7) (R 7) [6,288,65,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15193 : Route 9 := (fun mask => (mask,id))

def c15193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15193 : Upper (D 7) (R 7) [6,288,65,18,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,192,1] 13 (by decide) (choices 1) [8,32,128] r15193 c15193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2923
  · exact u2924
  · exact u2925

def r15194 : Route 9 := (fun mask => (mask,id))

def c15194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15194 : Upper (D 7) (R 7) [6,288,65,18,192,8] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,192,8] 13 (by decide) (choices 1) [1,32,128] r15194 c15194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2926
  · exact u2927
  · exact u2928

def r15195 : Route 9 := (fun mask => (mask,id))

def c15195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15195 : Upper (D 7) (R 7) [6,288,65,18,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18,192,128] 13 (by decide) (choices 1) [1,8,32] r15195 c15195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2929
  · exact u2930
  · exact u2931

def b15196 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 69 41 88 34 208 144 400), lower := (rows 7 290 69 41 88 34 64 128 256), losses := [] }

theorem u15196 : Upper (D 7) (R 7) [6,288,65,33,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15197 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 56, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 7 290 69 41 88 48 194 130 386), lower := (rows 7 290 69 41 88 48 64 128 256), losses := [] }

theorem u15197 : Upper (D 7) (R 7) [6,288,65,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15197 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15198 : Route 9 := (fun mask => (mask,id))

def c15198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15198 : Upper (D 7) (R 7) [6,288,65,33,72,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,72,128] 13 (by decide) (choices 1) [2,16,128] r15198 c15198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2932
  · exact u2933
  · exact u2934

def b15199 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 290 69 41 146 40 208 208 464), lower := (rows 7 290 69 41 146 40 64 128 256), losses := [] }

theorem u15199 : Upper (D 7) (R 7) [6,288,65,33,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15199 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15200 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 466, targets := 1 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 290 69 41 146 48 200 200 456), lower := (rows 7 290 69 41 146 48 64 128 256), losses := [] }

theorem u15200 : Upper (D 7) (R 7) [6,288,65,33,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15200 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15201 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 40, targets := 130 },{ cop := 3, region := 402, targets := 1 }], pairs := [(1,0),(3,1),(3,7),(4,0)], upper := (rows 7 290 69 41 146 96 216 152 408), lower := (rows 7 290 69 41 146 96 64 128 256), losses := [] }

theorem u15201 : Upper (D 7) (R 7) [6,288,65,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15202 : Route 9 := (fun mask => (mask,id))

def c15202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15202 : Upper (D 7) (R 7) [6,288,65,33,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,130,128] 13 (by decide) (choices 1) [8,16] r15202 c15202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2935
  · exact u2936

def b15203 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 69 41 152 34 208 208 464), lower := (rows 7 290 69 41 152 34 64 128 256), losses := [] }

theorem u15203 : Upper (D 7) (R 7) [6,288,65,33,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15204 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 450, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 290 69 41 152 48 194 194 450), lower := (rows 7 290 69 41 152 48 64 128 256), losses := [] }

theorem u15204 : Upper (D 7) (R 7) [6,288,65,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15204 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15205 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 40, targets := 130 },{ cop := 3, region := 402, targets := 1 }], pairs := [(1,0),(3,1),(3,7),(4,0)], upper := (rows 7 290 69 41 152 96 210 146 402), lower := (rows 7 290 69 41 152 96 64 128 256), losses := [] }

theorem u15205 : Upper (D 7) (R 7) [6,288,65,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15206 : Route 9 := (fun mask => (mask,id))

def c15206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15206 : Upper (D 7) (R 7) [6,288,65,33,136,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,136,128] 13 (by decide) (choices 1) [2,16] r15206 c15206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2937
  · exact u2938

def b15207 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 69 41 208 34 216 152 408), lower := (rows 7 290 69 41 208 34 64 128 256), losses := [] }

theorem u15207 : Upper (D 7) (R 7) [6,288,65,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15208 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 290 69 41 208 40 210 146 402), lower := (rows 7 290 69 41 208 40 64 128 256), losses := [] }

theorem u15208 : Upper (D 7) (R 7) [6,288,65,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15208 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15209 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 466, targets := 1 },{ cop := 3, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 41 208 48 202 138 394), lower := (rows 7 290 69 41 208 48 64 128 256), losses := [] }

theorem u15209 : Upper (D 7) (R 7) [6,288,65,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15209 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15210 : Route 9 := (fun mask => (mask,id))

def c15210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15210 : Upper (D 7) (R 7) [6,288,65,33,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33,192,128] 13 (by decide) (choices 1) [2,8,16] r15210 c15210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2939
  · exact u2940
  · exact u2941

def b15211 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 290 69 56 145 34 200 200 456), lower := (rows 7 290 69 56 145 34 64 128 256), losses := [] }

theorem u15211 : Upper (D 7) (R 7) [6,288,65,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15212 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 69 56 145 40 194 194 450), lower := (rows 7 290 69 56 145 40 64 128 256), losses := [] }

theorem u15212 : Upper (D 7) (R 7) [6,288,65,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15212 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15213 : Route 9 := (fun mask => (mask,id))

def c15213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15213 : Upper (D 7) (R 7) [6,288,65,48,129,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,129,64] 13 (by decide) (choices 1) [2,8,128] r15213 c15213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2942
  · exact u2943
  · exact u2944

def b15214 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 290 69 56 145 160 74 202 330), lower := (rows 7 290 69 56 145 160 64 128 256), losses := [] }

theorem u15214 : Upper (D 7) (R 7) [6,288,65,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15215 : Route 9 := (fun mask => (mask,id))

def c15215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15215 : Upper (D 7) (R 7) [6,288,65,48,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,130,1] 13 (by decide) (choices 1) [8,128] r15215 c15215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2945
  · exact u2946

def b15216 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 290 69 56 146 40 193 193 449), lower := (rows 7 290 69 56 146 40 64 128 256), losses := [] }

theorem u15216 : Upper (D 7) (R 7) [6,288,65,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15216 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15217 : Route 9 := (fun mask => (mask,id))

def c15217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15217 : Upper (D 7) (R 7) [6,288,65,48,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,130,64] 13 (by decide) (choices 1) [1,8,128] r15217 c15217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2947
  · exact u2948
  · exact u2949

def b15218 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 290 69 56 146 160 73 201 329), lower := (rows 7 290 69 56 146 160 64 128 256), losses := [] }

theorem u15218 : Upper (D 7) (R 7) [6,288,65,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15219 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 290 69 56 152 33 194 194 450), lower := (rows 7 290 69 56 152 33 64 128 256), losses := [] }

theorem u15219 : Upper (D 7) (R 7) [6,288,65,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15220 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 290 69 56 152 34 193 193 449), lower := (rows 7 290 69 56 152 34 64 128 256), losses := [] }

theorem u15220 : Upper (D 7) (R 7) [6,288,65,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15221 : Route 9 := (fun mask => (mask,id))

def c15221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15221 : Upper (D 7) (R 7) [6,288,65,48,136,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,136,64] 13 (by decide) (choices 1) [1,2,128] r15221 c15221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2950
  · exact u2951
  · exact u2952

def b15222 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 7 290 69 56 152 160 67 195 323), lower := (rows 7 290 69 56 152 160 64 128 256), losses := [] }

theorem u15222 : Upper (D 7) (R 7) [6,288,65,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15223 : PairBound 9 := { available := 138, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 290 69 56 208 33 202 138 394), lower := (rows 7 290 69 56 208 33 64 128 256), losses := [] }

theorem u15223 : Upper (D 7) (R 7) [6,288,65,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15224 : Route 9 := (fun mask => (mask,id))

def c15224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15224 : Upper (D 7) (R 7) [6,288,65,48,192,2] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48,192,2] 13 (by decide) (choices 1) [1,8,128] r15224 c15224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2953
  · exact u2954
  · exact u2955

def b15225 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 290 69 56 208 40 195 131 387), lower := (rows 7 290 69 56 208 40 64 128 256), losses := [] }

theorem u15225 : Upper (D 7) (R 7) [6,288,65,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15225 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15226 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 290 69 56 208 160 75 139 267), lower := (rows 7 290 69 56 208 160 64 128 256), losses := [] }

theorem u15226 : Upper (D 7) (R 7) [6,288,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15227 : PairBound 9 := { available := 168, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 290 69 88 145 34 232 168 424), lower := (rows 7 290 69 88 145 34 64 128 256), losses := [] }

theorem u15227 : Upper (D 7) (R 7) [6,288,65,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15228 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 290 69 88 145 40 226 162 418), lower := (rows 7 290 69 88 145 40 64 128 256), losses := [] }

theorem u15228 : Upper (D 7) (R 7) [6,288,65,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15228 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15229 : Route 9 := (fun mask => (mask,id))

def c15229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15229 : Upper (D 7) (R 7) [6,288,65,80,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,129,128] 13 (by decide) (choices 1) [2,8,32] r15229 c15229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2956
  · exact u2957
  · exact u2958

def r15230 : Route 9 := (fun mask => (mask,id))

def c15230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15230 : Upper (D 7) (R 7) [6,288,65,80,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,130,1] 13 (by decide) (choices 1) [8,32,128] r15230 c15230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2959
  · exact u2960
  · exact u2961

def r15231 : Route 9 := (fun mask => (mask,id))

def c15231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15231 : Upper (D 7) (R 7) [6,288,65,80,130,8] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,130,8] 13 (by decide) (choices 1) [1,32,128] r15231 c15231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2962
  · exact u2963
  · exact u2964

def r15232 : Route 9 := (fun mask => (mask,id))

def c15232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15232 : Upper (D 7) (R 7) [6,288,65,80,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,130,128] 13 (by decide) (choices 1) [1,8,32] r15232 c15232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2965
  · exact u2966
  · exact u2967

def b15233 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 7 290 69 88 152 33 226 162 418), lower := (rows 7 290 69 88 152 33 64 128 256), losses := [] }

theorem u15233 : Upper (D 7) (R 7) [6,288,65,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15234 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 7 290 69 88 152 34 225 161 417), lower := (rows 7 290 69 88 152 34 64 128 256), losses := [] }

theorem u15234 : Upper (D 7) (R 7) [6,288,65,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15235 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 7 290 69 88 152 160 99 163 291), lower := (rows 7 290 69 88 152 160 64 128 256), losses := [] }

theorem u15235 : Upper (D 7) (R 7) [6,288,65,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15236 : Route 9 := (fun mask => (mask,id))

def c15236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15236 : Upper (D 7) (R 7) [6,288,65,80,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,160,1] 13 (by decide) (choices 1) [2,8,128] r15236 c15236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2968
  · exact u2969
  · exact u2970

def r15237 : Route 9 := (fun mask => (mask,id))

def c15237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15237 : Upper (D 7) (R 7) [6,288,65,80,160,2] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,160,2] 13 (by decide) (choices 1) [1,8,128] r15237 c15237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2971
  · exact u2972
  · exact u2973

def r15238 : Route 9 := (fun mask => (mask,id))

def c15238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15238 : Upper (D 7) (R 7) [6,288,65,80,160,8] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,160,8] 13 (by decide) (choices 1) [1,2,128] r15238 c15238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2974
  · exact u2975
  · exact u2976

def b15239 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 69 88 176 160 75 139 267), lower := (rows 7 290 69 88 176 160 64 128 256), losses := [] }

theorem u15239 : Upper (D 7) (R 7) [6,288,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15239
end Delivery.IrregularNine14.P07
