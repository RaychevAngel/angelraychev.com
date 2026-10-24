import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0447
import IrregularNine14P07C0448
import IrregularNine14P07C0449

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39120 : Route 9 := (fun mask => (mask,id))

def c39120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39120 : Upper (D 7) (R 7) [36,288,65,17,192] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17,192] 13 (by decide) (choices 1) [2,8,128] r39120 c39120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26870
  · exact u26871
  · exact u26872

def b39121 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 290 69 26 26 225 193 193 449), lower := (rows 37 290 69 26 26 32 64 128 256), losses := [] }

theorem u39121 : Upper (D 7) (R 7) [36,288,65,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39122 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 290 69 26 81 170 202 138 394), lower := (rows 37 290 69 26 81 32 64 128 256), losses := [] }

theorem u39122 : Upper (D 7) (R 7) [36,288,65,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39123 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 290 69 26 82 169 201 137 393), lower := (rows 37 290 69 26 82 32 64 128 256), losses := [] }

theorem u39123 : Upper (D 7) (R 7) [36,288,65,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39124 : Route 9 := (fun mask => (mask,id))

def c39124 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39124 : Upper (D 7) (R 7) [36,288,65,18,72] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,72] 13 (by decide) (choices 1) [1,2,128] r39124 c39124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26873
  · exact u26874
  · exact u26875

def r39125 : Route 9 := (fun mask => (mask,id))

def c39125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39125 : Upper (D 7) (R 7) [36,288,65,18,129] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,129] 13 (by decide) (choices 1) [2,8,64,128] r39125 c39125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26876
  · exact u26877
  · exact u26878
  · exact u26879

def b39126 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 290 69 26 146 233 201 201 457), lower := (rows 37 290 69 26 146 32 64 128 256), losses := [] }

theorem u39126 : Upper (D 7) (R 7) [36,288,65,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39127 : Route 9 := (fun mask => (mask,id))

def c39127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39127 : Upper (D 7) (R 7) [36,288,65,18,136] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,136] 13 (by decide) (choices 1) [1,2,64,128] r39127 c39127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26880
  · exact u26881
  · exact u26882
  · exact u26883

def r39128 : Route 9 := (fun mask => (mask,id))

def c39128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39128 : Upper (D 7) (R 7) [36,288,65,18,192] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,192] 13 (by decide) (choices 1) [1,2,8,128] r39128 c39128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26884
  · exact u26885
  · exact u26886
  · exact u26887

def b39129 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 37 290 69 73 146 186 218 154 410), lower := (rows 37 290 69 73 146 32 64 128 256), losses := [] }

theorem u39129 : Upper (D 7) (R 7) [36,288,65,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39130 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 37 290 69 73 152 178 210 146 402), lower := (rows 37 290 69 73 152 32 64 128 256), losses := [] }

theorem u39130 : Upper (D 7) (R 7) [36,288,65,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39131 : Route 9 := (fun mask => (mask,id))

def c39131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39131 : Upper (D 7) (R 7) [36,288,65,66,129] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66,129] 13 (by decide) (choices 1) [2,8,16,128] r39131 c39131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26888
  · exact u26889
  · exact u26890
  · exact u26891

def r39132 : Route 9 := (fun mask => (mask,id))

def c39132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39132 : Upper (D 7) (R 7) [36,288,65,66,130] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66,130] 13 (by decide) (choices 1) [1,8,16,128] r39132 c39132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26892
  · exact u26893
  · exact u26894
  · exact u26895

def r39133 : Route 9 := (fun mask => (mask,id))

def c39133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39133 : Upper (D 7) (R 7) [36,288,65,66,136] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66,136] 13 (by decide) (choices 1) [1,2,16,128] r39133 c39133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26896
  · exact u26897
  · exact u26898
  · exact u26899

def r39134 : Route 9 := (fun mask => (mask,id))

def c39134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39134 : Upper (D 7) (R 7) [36,288,65,80,129] 13 := by
  apply FastRouting.sound _ _ [36,288,65,80,129] 13 (by decide) (choices 1) [2,8,128] r39134 c39134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26900
  · exact u26901
  · exact u26902

def r39135 : Route 9 := (fun mask => (mask,id))

def c39135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39135 : Upper (D 7) (R 7) [36,288,65,80,130] 13 := by
  apply FastRouting.sound _ _ [36,288,65,80,130] 13 (by decide) (choices 1) [1,2,8,128] r39135 c39135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26903
  · exact u26904
  · exact u26905
  · exact u26906

def r39136 : Route 9 := (fun mask => (mask,id))

def c39136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39136 : Upper (D 7) (R 7) [36,288,65,80,136] 13 := by
  apply FastRouting.sound _ _ [36,288,65,80,136] 13 (by decide) (choices 1) [1,2,128] r39136 c39136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26907
  · exact u26908
  · exact u26909

def r39137 : Route 9 := (fun mask => (mask,id))

def c39137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39137 : Upper (D 7) (R 7) [36,288,65,129,130] 13 := by
  apply FastRouting.sound _ _ [36,288,65,129,130] 13 (by decide) (choices 1) [2,8,16,64] r39137 c39137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26910
  · exact u26911
  · exact u26912
  · exact u26913

def b39138 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,1),(4,5),(4,6)], upper := (rows 37 290 69 137 152 114 82 210 338), lower := (rows 37 290 69 137 152 32 64 128 256), losses := [] }

theorem u39138 : Upper (D 7) (R 7) [36,288,65,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39139 : Route 9 := (fun mask => (mask,id))

def c39139 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39139 : Upper (D 7) (R 7) [36,288,65,129,192] 13 := by
  apply FastRouting.sound _ _ [36,288,65,129,192] 13 (by decide) (choices 1) [2,8,16] r39139 c39139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26914
  · exact u26915
  · exact u26916

def b39140 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 290 69 138 146 121 89 217 345), lower := (rows 37 290 69 138 146 32 64 128 256), losses := [] }

theorem u39140 : Upper (D 7) (R 7) [36,288,65,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39141 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 290 69 138 152 115 83 211 339), lower := (rows 37 290 69 138 152 32 64 128 256), losses := [] }

theorem u39141 : Upper (D 7) (R 7) [36,288,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39142 : Route 9 := (fun mask => (mask,id))

def c39142 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39142 : Upper (D 7) (R 7) [36,288,65,130,192] 13 := by
  apply FastRouting.sound _ _ [36,288,65,130,192] 13 (by decide) (choices 1) [1,2,8,16] r39142 c39142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26917
  · exact u26918
  · exact u26919
  · exact u26920

def b39143 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 290 69 152 152 99 67 195 323), lower := (rows 37 290 69 152 152 32 64 128 256), losses := [] }

theorem u39143 : Upper (D 7) (R 7) [36,288,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39144 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 290 69 152 208 43 75 139 267), lower := (rows 37 290 69 152 208 32 64 128 256), losses := [] }

theorem u39144 : Upper (D 7) (R 7) [36,288,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39145 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 290 70 11 25 240 208 208 464), lower := (rows 37 290 70 11 25 32 64 128 256), losses := [] }

theorem u39145 : Upper (D 7) (R 7) [36,288,66,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39146 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 37 290 70 11 81 184 216 152 408), lower := (rows 37 290 70 11 81 32 64 128 256), losses := [] }

theorem u39146 : Upper (D 7) (R 7) [36,288,66,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39147 : Route 9 := (fun mask => (mask,id))

def c39147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39147 : Upper (D 7) (R 7) [36,288,66,3,72] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3,72] 13 (by decide) (choices 1) [1,16,128] r39147 c39147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26921
  · exact u26922
  · exact u26923

def r39148 : Route 9 := (fun mask => (mask,id))

def c39148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u39148 : Upper (D 7) (R 7) [36,288,66,3,129] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3,129] 13 (by decide) (choices 1) [8,16,64,128] r39148 c39148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26924
  · exact u26925
  · exact u26926
  · exact u26927

def r39149 : Route 9 := (fun mask => (mask,id))

def c39149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39149 : Upper (D 7) (R 7) [36,288,66,3,136] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3,136] 13 (by decide) (choices 1) [1,16,64,128] r39149 c39149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26928
  · exact u26929
  · exact u26930
  · exact u26931

def r39150 : Route 9 := (fun mask => (mask,id))

def c39150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39150 : Upper (D 7) (R 7) [36,288,66,3,192] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3,192] 13 (by decide) (choices 1) [1,8,16,128] r39150 c39150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26932
  · exact u26933
  · exact u26934
  · exact u26935

def b39151 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 290 70 25 25 226 194 194 450), lower := (rows 37 290 70 25 25 32 64 128 256), losses := [] }

theorem u39151 : Upper (D 7) (R 7) [36,288,66,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39152 : Route 9 := (fun mask => (mask,id))

def c39152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39152 : Upper (D 7) (R 7) [36,288,66,17,10] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,10] 13 (by decide) (choices 1) [1,64,128] r39152 c39152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26936
  · exact u26937
  · exact u26938

def b39153 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 70 25 81 170 202 138 394), lower := (rows 37 290 70 25 81 32 64 128 256), losses := [] }

theorem u39153 : Upper (D 7) (R 7) [36,288,66,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39154 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 290 70 25 82 169 201 137 393), lower := (rows 37 290 70 25 82 32 64 128 256), losses := [] }

theorem u39154 : Upper (D 7) (R 7) [36,288,66,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39155 : Route 9 := (fun mask => (mask,id))

def c39155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39155 : Upper (D 7) (R 7) [36,288,66,17,72] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,72] 13 (by decide) (choices 1) [1,2,128] r39155 c39155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26939
  · exact u26940
  · exact u26941

def b39156 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 290 70 25 145 234 202 202 458), lower := (rows 37 290 70 25 145 32 64 128 256), losses := [] }

theorem u39156 : Upper (D 7) (R 7) [36,288,66,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39157 : Route 9 := (fun mask => (mask,id))

def c39157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39157 : Upper (D 7) (R 7) [36,288,66,17,130] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,130] 13 (by decide) (choices 1) [1,8,64,128] r39157 c39157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26942
  · exact u26943
  · exact u26944
  · exact u26945

def r39158 : Route 9 := (fun mask => (mask,id))

def c39158 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39158 : Upper (D 7) (R 7) [36,288,66,17,136] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,136] 13 (by decide) (choices 1) [1,2,64,128] r39158 c39158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26946
  · exact u26947
  · exact u26948
  · exact u26949

def r39159 : Route 9 := (fun mask => (mask,id))

def c39159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39159 : Upper (D 7) (R 7) [36,288,66,17,192] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,192] 13 (by decide) (choices 1) [1,2,8,128] r39159 c39159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26950
  · exact u26951
  · exact u26952
  · exact u26953

def r39160 : Route 9 := (fun mask => (mask,id))

def c39160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39160 : Upper (D 7) (R 7) [36,288,66,18,65] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18,65] 13 (by decide) (choices 1) [1,8,128] r39160 c39160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26954
  · exact u26955
  · exact u26956

def b39161 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 290 70 26 88 161 193 129 385), lower := (rows 37 290 70 26 88 32 64 128 256), losses := [] }

theorem u39161 : Upper (D 7) (R 7) [36,288,66,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39162 : Route 9 := (fun mask => (mask,id))

def c39162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39162 : Upper (D 7) (R 7) [36,288,66,18,129] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18,129] 13 (by decide) (choices 1) [1,8,64,128] r39162 c39162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26957
  · exact u26958
  · exact u26959
  · exact u26960

def r39163 : Route 9 := (fun mask => (mask,id))

def c39163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39163 : Upper (D 7) (R 7) [36,288,66,18,136] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18,136] 13 (by decide) (choices 1) [1,64,128] r39163 c39163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26961
  · exact u26962
  · exact u26963

def r39164 : Route 9 := (fun mask => (mask,id))

def c39164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39164 : Upper (D 7) (R 7) [36,288,66,18,192] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18,192] 13 (by decide) (choices 1) [1,8,128] r39164 c39164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26964
  · exact u26965
  · exact u26966

def r39165 : Route 9 := (fun mask => (mask,id))

def c39165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39165 : Upper (D 7) (R 7) [36,288,66,65,129] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65,129] 13 (by decide) (choices 1) [2,8,16,128] r39165 c39165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26967
  · exact u26968
  · exact u26969
  · exact u26970

def r39166 : Route 9 := (fun mask => (mask,id))

def c39166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39166 : Upper (D 7) (R 7) [36,288,66,65,130] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65,130] 13 (by decide) (choices 1) [1,8,16,128] r39166 c39166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26971
  · exact u26972
  · exact u26973
  · exact u26974

def r39167 : Route 9 := (fun mask => (mask,id))

def c39167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39167 : Upper (D 7) (R 7) [36,288,66,65,136] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65,136] 13 (by decide) (choices 1) [1,2,16,128] r39167 c39167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26975
  · exact u26976
  · exact u26977
  · exact u26978

def b39168 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 161 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,7)], upper := (rows 37 290 70 74 145 185 217 153 409), lower := (rows 37 290 70 74 145 32 64 128 256), losses := [] }

theorem u39168 : Upper (D 7) (R 7) [36,288,66,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39169 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 8, targets := 161 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,7)], upper := (rows 37 290 70 74 152 177 209 145 401), lower := (rows 37 290 70 74 152 32 64 128 256), losses := [] }

theorem u39169 : Upper (D 7) (R 7) [36,288,66,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39170 : Route 9 := (fun mask => (mask,id))

def c39170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39170 : Upper (D 7) (R 7) [36,288,66,80,129] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80,129] 13 (by decide) (choices 1) [1,2,8,128] r39170 c39170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26979
  · exact u26980
  · exact u26981
  · exact u26982

def r39171 : Route 9 := (fun mask => (mask,id))

def c39171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39171 : Upper (D 7) (R 7) [36,288,66,80,130] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80,130] 13 (by decide) (choices 1) [1,8,128] r39171 c39171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26983
  · exact u26984
  · exact u26985

def r39172 : Route 9 := (fun mask => (mask,id))

def c39172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39172 : Upper (D 7) (R 7) [36,288,66,80,136] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80,136] 13 (by decide) (choices 1) [1,2,128] r39172 c39172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26986
  · exact u26987
  · exact u26988

def b39173 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 290 70 137 145 122 90 218 346), lower := (rows 37 290 70 137 145 32 64 128 256), losses := [] }

theorem u39173 : Upper (D 7) (R 7) [36,288,66,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39174 : Route 9 := (fun mask => (mask,id))

def c39174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39174 : Upper (D 7) (R 7) [36,288,66,129,130] 13 := by
  apply FastRouting.sound _ _ [36,288,66,129,130] 13 (by decide) (choices 1) [1,8,16,64] r39174 c39174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26989
  · exact u26990
  · exact u26991
  · exact u26992

def b39175 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 290 70 137 152 115 83 211 339), lower := (rows 37 290 70 137 152 32 64 128 256), losses := [] }

theorem u39175 : Upper (D 7) (R 7) [36,288,66,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39176 : Route 9 := (fun mask => (mask,id))

def c39176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39176 : Upper (D 7) (R 7) [36,288,66,129,192] 13 := by
  apply FastRouting.sound _ _ [36,288,66,129,192] 13 (by decide) (choices 1) [1,2,8,16] r39176 c39176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26993
  · exact u26994
  · exact u26995
  · exact u26996

def b39177 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 290 70 138 152 113 81 209 337), lower := (rows 37 290 70 138 152 32 64 128 256), losses := [] }

theorem u39177 : Upper (D 7) (R 7) [36,288,66,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39178 : Route 9 := (fun mask => (mask,id))

def c39178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39178 : Upper (D 7) (R 7) [36,288,66,130,192] 13 := by
  apply FastRouting.sound _ _ [36,288,66,130,192] 13 (by decide) (choices 1) [1,8,16] r39178 c39178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26997
  · exact u26998
  · exact u26999

def b39179 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 290 70 152 152 99 67 195 323), lower := (rows 37 290 70 152 152 32 64 128 256), losses := [] }

theorem u39179 : Upper (D 7) (R 7) [36,288,66,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39179
end Delivery.IrregularNine14.P07
