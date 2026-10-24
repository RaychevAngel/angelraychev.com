import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0397
import IrregularNine14P06C0398

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38160 : Route 9 := (fun mask => (mask,id))

def c38160 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38160 : Upper (D 6) (R 6) [34,136,80,65,36] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,36] 13 (by decide) (choices 1) [1,2,4,256] r38160 c38160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23840
  · exact u23841
  · exact u23842
  · exact u23843

def r38161 : Route 9 := (fun mask => (mask,id))

def c38161 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38161 : Upper (D 6) (R 6) [34,136,80,65,257] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,257] 13 (by decide) (choices 1) [2,4] r38161 c38161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23844
  · exact u23845

def r38162 : Route 9 := (fun mask => (mask,id))

def c38162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38162 : Upper (D 6) (R 6) [34,136,80,65,258] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,258] 13 (by decide) (choices 1) [1,4] r38162 c38162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23846
  · exact u23847

def r38163 : Route 9 := (fun mask => (mask,id))

def c38163 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38163 : Upper (D 6) (R 6) [34,136,80,65,260] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,260] 13 (by decide) (choices 1) [1,2,4] r38163 c38163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23848
  · exact u23849
  · exact u23850

def r38164 : Route 9 := (fun mask => (mask,id))

def c38164 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38164 : Upper (D 6) (R 6) [34,136,80,65,288] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,288] 13 (by decide) (choices 1) [1,2,4] r38164 c38164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23851
  · exact u23852
  · exact u23853

def r38165 : Route 9 := (fun mask => (mask,id))

def c38165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38165 : Upper (D 6) (R 6) [34,136,80,66,5] 13 := by
  apply FastRouting.sound _ _ [34,136,80,66,5] 13 (by decide) (choices 1) [1,4,256] r38165 c38165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23854
  · exact u23855
  · exact u23856

def b38166 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 84 74 49 293 325 389 261), lower := (rows 35 138 84 74 49 32 64 128 256), losses := [] }

theorem u38166 : Upper (D 6) (R 6) [34,136,80,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38167 : Route 9 := (fun mask => (mask,id))

def c38167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38167 : Upper (D 6) (R 6) [34,136,80,66,36] 13 := by
  apply FastRouting.sound _ _ [34,136,80,66,36] 13 (by decide) (choices 1) [1,4,256] r38167 c38167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23857
  · exact u23858
  · exact u23859

def r38168 : Route 9 := (fun mask => (mask,id))

def c38168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38168 : Upper (D 6) (R 6) [34,136,80,66,257] 13 := by
  apply FastRouting.sound _ _ [34,136,80,66,257] 13 (by decide) (choices 1) [1,4] r38168 c38168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23860
  · exact u23861

def r38169 : Route 9 := (fun mask => (mask,id))

def c38169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38169 : Upper (D 6) (R 6) [34,136,80,66,260] 13 := by
  apply FastRouting.sound _ _ [34,136,80,66,260] 13 (by decide) (choices 1) [1,4] r38169 c38169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23862
  · exact u23863

def r38170 : Route 9 := (fun mask => (mask,id))

def c38170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38170 : Upper (D 6) (R 6) [34,136,80,66,288] 13 := by
  apply FastRouting.sound _ _ [34,136,80,66,288] 13 (by decide) (choices 1) [1,4] r38170 c38170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23864
  · exact u23865

def b38171 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 84 104 19 293 325 389 261), lower := (rows 35 138 84 104 19 32 64 128 256), losses := [] }

theorem u38171 : Upper (D 6) (R 6) [34,136,80,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38172 : Route 9 := (fun mask => (mask,id))

def c38172 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38172 : Upper (D 6) (R 6) [34,136,80,96,5] 13 := by
  apply FastRouting.sound _ _ [34,136,80,96,5] 13 (by decide) (choices 1) [1,2,4,256] r38172 c38172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23866
  · exact u23867
  · exact u23868
  · exact u23869

def b38173 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 84 104 22 293 325 389 261), lower := (rows 35 138 84 104 22 32 64 128 256), losses := [] }

theorem u38173 : Upper (D 6) (R 6) [34,136,80,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38174 : Route 9 := (fun mask => (mask,id))

def c38174 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38174 : Upper (D 6) (R 6) [34,136,80,96,257] 13 := by
  apply FastRouting.sound _ _ [34,136,80,96,257] 13 (by decide) (choices 1) [1,2,4] r38174 c38174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23870
  · exact u23871
  · exact u23872

def r38175 : Route 9 := (fun mask => (mask,id))

def c38175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38175 : Upper (D 6) (R 6) [34,136,80,96,258] 13 := by
  apply FastRouting.sound _ _ [34,136,80,96,258] 13 (by decide) (choices 1) [1,4] r38175 c38175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23873
  · exact u23874

def r38176 : Route 9 := (fun mask => (mask,id))

def c38176 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38176 : Upper (D 6) (R 6) [34,136,80,96,260] 13 := by
  apply FastRouting.sound _ _ [34,136,80,96,260] 13 (by decide) (choices 1) [1,2,4] r38176 c38176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23875
  · exact u23876
  · exact u23877

def b38177 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 84 265 19 100 100 228 356), lower := (rows 35 138 84 265 19 32 64 128 256), losses := [] }

theorem u38177 : Upper (D 6) (R 6) [34,136,80,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38178 : Route 9 := (fun mask => (mask,id))

def c38178 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38178 : Upper (D 6) (R 6) [34,136,80,257,5] 13 := by
  apply FastRouting.sound _ _ [34,136,80,257,5] 13 (by decide) (choices 1) [2,4,64] r38178 c38178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23878
  · exact u23879
  · exact u23880

def r38179 : Route 9 := (fun mask => (mask,id))

def c38179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38179 : Upper (D 6) (R 6) [34,136,80,257,6] 13 := by
  apply FastRouting.sound _ _ [34,136,80,257,6] 13 (by decide) (choices 1) [1,4,64] r38179 c38179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23881
  · exact u23882
  · exact u23883

def b38180 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 84 265 49 102 70 198 326), lower := (rows 35 138 84 265 49 32 64 128 256), losses := [] }

theorem u38180 : Upper (D 6) (R 6) [34,136,80,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38181 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 84 265 50 101 69 197 325), lower := (rows 35 138 84 265 50 32 64 128 256), losses := [] }

theorem u38181 : Upper (D 6) (R 6) [34,136,80,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38182 : Route 9 := (fun mask => (mask,id))

def c38182 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38182 : Upper (D 6) (R 6) [34,136,80,257,36] 13 := by
  apply FastRouting.sound _ _ [34,136,80,257,36] 13 (by decide) (choices 1) [1,2,4,64] r38182 c38182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23884
  · exact u23885
  · exact u23886
  · exact u23887

def b38183 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 265 81 38 102 166 294), lower := (rows 35 138 84 265 81 32 64 128 256), losses := [] }

theorem u38183 : Upper (D 6) (R 6) [34,136,80,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38184 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 265 82 37 101 165 293), lower := (rows 35 138 84 265 82 32 64 128 256), losses := [] }

theorem u38184 : Upper (D 6) (R 6) [34,136,80,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38185 : PairBound 9 := { available := 39, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 138 84 265 84 39 103 167 295), lower := (rows 35 138 84 265 84 32 64 128 256), losses := [] }

theorem u38185 : Upper (D 6) (R 6) [34,136,80,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38186 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 265 112 39 71 135 263), lower := (rows 35 138 84 265 112 32 64 128 256), losses := [] }

theorem u38186 : Upper (D 6) (R 6) [34,136,80,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38187 : Route 9 := (fun mask => (mask,id))

def c38187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38187 : Upper (D 6) (R 6) [34,136,80,258,5] 13 := by
  apply FastRouting.sound _ _ [34,136,80,258,5] 13 (by decide) (choices 1) [1,4,64] r38187 c38187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23888
  · exact u23889
  · exact u23890

def b38188 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 84 266 49 101 69 197 325), lower := (rows 35 138 84 266 49 32 64 128 256), losses := [] }

theorem u38188 : Upper (D 6) (R 6) [34,136,80,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38189 : Route 9 := (fun mask => (mask,id))

def c38189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38189 : Upper (D 6) (R 6) [34,136,80,258,36] 13 := by
  apply FastRouting.sound _ _ [34,136,80,258,36] 13 (by decide) (choices 1) [1,4,64] r38189 c38189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23891
  · exact u23892
  · exact u23893

def b38190 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 266 81 37 101 165 293), lower := (rows 35 138 84 266 81 32 64 128 256), losses := [] }

theorem u38190 : Upper (D 6) (R 6) [34,136,80,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38191 : PairBound 9 := { available := 37, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 138 84 266 84 37 101 165 293), lower := (rows 35 138 84 266 84 32 64 128 256), losses := [] }

theorem u38191 : Upper (D 6) (R 6) [34,136,80,258,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38192 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 266 112 37 69 133 261), lower := (rows 35 138 84 266 112 32 64 128 256), losses := [] }

theorem u38192 : Upper (D 6) (R 6) [34,136,80,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38193 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 84 268 19 101 101 229 357), lower := (rows 35 138 84 268 19 32 64 128 256), losses := [] }

theorem u38193 : Upper (D 6) (R 6) [34,136,80,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38194 : Route 9 := (fun mask => (mask,id))

def c38194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38194 : Upper (D 6) (R 6) [34,136,80,260,5] 13 := by
  apply FastRouting.sound _ _ [34,136,80,260,5] 13 (by decide) (choices 1) [1,2,64] r38194 c38194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23894
  · exact u23895
  · exact u23896

def r38195 : Route 9 := (fun mask => (mask,id))

def c38195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38195 : Upper (D 6) (R 6) [34,136,80,260,6] 13 := by
  apply FastRouting.sound _ _ [34,136,80,260,6] 13 (by decide) (choices 1) [1,64] r38195 c38195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23897
  · exact u23898

def b38196 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 84 268 49 103 71 199 327), lower := (rows 35 138 84 268 49 32 64 128 256), losses := [] }

theorem u38196 : Upper (D 6) (R 6) [34,136,80,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38197 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 84 268 50 101 69 197 325), lower := (rows 35 138 84 268 50 32 64 128 256), losses := [] }

theorem u38197 : Upper (D 6) (R 6) [34,136,80,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38198 : Route 9 := (fun mask => (mask,id))

def c38198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38198 : Upper (D 6) (R 6) [34,136,80,260,36] 13 := by
  apply FastRouting.sound _ _ [34,136,80,260,36] 13 (by decide) (choices 1) [1,2,64] r38198 c38198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23899
  · exact u23900
  · exact u23901

def b38199 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 268 81 39 103 167 295), lower := (rows 35 138 84 268 81 32 64 128 256), losses := [] }

theorem u38199 : Upper (D 6) (R 6) [34,136,80,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38200 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 268 82 37 101 165 293), lower := (rows 35 138 84 268 82 32 64 128 256), losses := [] }

theorem u38200 : Upper (D 6) (R 6) [34,136,80,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38201 : PairBound 9 := { available := 35, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 138 84 268 84 35 99 163 291), lower := (rows 35 138 84 268 84 32 64 128 256), losses := [] }

theorem u38201 : Upper (D 6) (R 6) [34,136,80,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38202 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 268 112 39 71 135 263), lower := (rows 35 138 84 268 112 32 64 128 256), losses := [] }

theorem u38202 : Upper (D 6) (R 6) [34,136,80,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38203 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 84 296 19 101 69 197 325), lower := (rows 35 138 84 296 19 32 64 128 256), losses := [] }

theorem u38203 : Upper (D 6) (R 6) [34,136,80,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38204 : Route 9 := (fun mask => (mask,id))

def c38204 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38204 : Upper (D 6) (R 6) [34,136,80,288,5] 13 := by
  apply FastRouting.sound _ _ [34,136,80,288,5] 13 (by decide) (choices 1) [1,2,4,64] r38204 c38204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23902
  · exact u23903
  · exact u23904
  · exact u23905

def r38205 : Route 9 := (fun mask => (mask,id))

def c38205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38205 : Upper (D 6) (R 6) [34,136,80,288,6] 13 := by
  apply FastRouting.sound _ _ [34,136,80,288,6] 13 (by decide) (choices 1) [1,4,64] r38205 c38205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23906
  · exact u23907
  · exact u23908

def b38206 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 296 81 39 71 135 263), lower := (rows 35 138 84 296 81 32 64 128 256), losses := [] }

theorem u38206 : Upper (D 6) (R 6) [34,136,80,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38207 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 296 82 37 69 133 261), lower := (rows 35 138 84 296 82 32 64 128 256), losses := [] }

theorem u38207 : Upper (D 6) (R 6) [34,136,80,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38208 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 138 84 296 84 39 71 135 263), lower := (rows 35 138 84 296 84 32 64 128 256), losses := [] }

theorem u38208 : Upper (D 6) (R 6) [34,136,80,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38209 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 84 328 19 37 101 165 293), lower := (rows 35 138 84 328 19 32 64 128 256), losses := [] }

theorem u38209 : Upper (D 6) (R 6) [34,136,80,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38210 : Route 9 := (fun mask => (mask,id))

def c38210 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38210 : Upper (D 6) (R 6) [34,136,80,320,5] 13 := by
  apply FastRouting.sound _ _ [34,136,80,320,5] 13 (by decide) (choices 1) [1,2,4] r38210 c38210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23909
  · exact u23910
  · exact u23911

def r38211 : Route 9 := (fun mask => (mask,id))

def c38211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38211 : Upper (D 6) (R 6) [34,136,80,320,6] 13 := by
  apply FastRouting.sound _ _ [34,136,80,320,6] 13 (by decide) (choices 1) [1,4] r38211 c38211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23912
  · exact u23913

def b38212 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 84 328 49 39 71 135 263), lower := (rows 35 138 84 328 49 32 64 128 256), losses := [] }

theorem u38212 : Upper (D 6) (R 6) [34,136,80,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38213 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 84 328 50 37 69 133 261), lower := (rows 35 138 84 328 50 32 64 128 256), losses := [] }

theorem u38213 : Upper (D 6) (R 6) [34,136,80,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38214 : Route 9 := (fun mask => (mask,id))

def c38214 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38214 : Upper (D 6) (R 6) [34,136,80,320,36] 13 := by
  apply FastRouting.sound _ _ [34,136,80,320,36] 13 (by decide) (choices 1) [1,2,4] r38214 c38214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23914
  · exact u23915
  · exact u23916

def b38215 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 100 13 19 372 340 468 340), lower := (rows 35 138 100 13 19 32 64 128 256), losses := [] }

theorem u38215 : Upper (D 6) (R 6) [34,136,96,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38216 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 66 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 35 138 100 13 21 370 338 466 338), lower := (rows 35 138 100 13 21 32 64 128 256), losses := [] }

theorem u38216 : Upper (D 6) (R 6) [34,136,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38217 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 353, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 138 100 13 22 369 337 465 337), lower := (rows 35 138 100 13 22 32 64 128 256), losses := [] }

theorem u38217 : Upper (D 6) (R 6) [34,136,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38218 : Route 9 := (fun mask => (mask,id))

def c38218 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38218 : Upper (D 6) (R 6) [34,136,96,5,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,5,65] 13 (by decide) (choices 1) [2,4,16,256] r38218 c38218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23917
  · exact u23918
  · exact u23919
  · exact u23920

def r38219 : Route 9 := (fun mask => (mask,id))

def c38219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38219 : Upper (D 6) (R 6) [34,136,96,5,66] 13 := by
  apply FastRouting.sound _ _ [34,136,96,5,66] 13 (by decide) (choices 1) [1,4,16,256] r38219 c38219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23921
  · exact u23922
  · exact u23923
  · exact u23924

#print axioms u38219
end Delivery.IrregularNine14.P06
