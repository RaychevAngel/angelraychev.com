import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0064
import IrregularNine14P09C0065

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7140 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 14 84 200 49 417 449 385 385), lower := (rows 35 14 84 200 49 32 64 128 256), losses := [] }

theorem u7140 : Upper (D 9) (R 9) [34,12,80,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7140 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7141 : Route 9 := (fun mask => (mask,id))

def c7141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7141 : Upper (D 9) (R 9) [34,12,80,192,129] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,129] 13 (by decide) (choices 1) [1,256] r7141 c7141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3855
  · exact u3856

def r7142 : Route 9 := (fun mask => (mask,id))

def c7142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7142 : Upper (D 9) (R 9) [34,12,80,192,160] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,160] 13 (by decide) (choices 1) [1,256] r7142 c7142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3857
  · exact u3858

def r7143 : Route 9 := (fun mask => (mask,id))

def c7143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7143 : Upper (D 9) (R 9) [34,12,80,192,257] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,257] 13 (by decide) (choices 1) [1,128,256] r7143 c7143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3859
  · exact u3860
  · exact u3861

def r7144 : Route 9 := (fun mask => (mask,id))

def c7144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7144 : Upper (D 9) (R 9) [34,12,80,192,288] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,288] 13 (by decide) (choices 1) [1,128,256] r7144 c7144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3862
  · exact u3863
  · exact u3864

def r7145 : Route 9 := (fun mask => (mask,id))

def c7145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7145 : Upper (D 9) (R 9) [34,12,80,192,384] 13 := by
  apply FastRouting.sound _ _ [34,12,80,192,384] 13 (by decide) (choices 1) [1,256] r7145 c7145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3865
  · exact u3866

def b7146 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 14 84 392 49 481 449 449 449), lower := (rows 35 14 84 392 49 32 64 128 256), losses := [] }

theorem u7146 : Upper (D 9) (R 9) [34,12,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7146 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7147 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 4, targets := 417 },{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 35 14 84 392 81 417 481 417 417), lower := (rows 35 14 84 392 81 32 64 128 256), losses := [] }

theorem u7147 : Upper (D 9) (R 9) [34,12,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7147 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7148 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 417 },{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 35 14 84 392 112 417 449 385 385), lower := (rows 35 14 84 392 112 32 64 128 256), losses := [] }

theorem u7148 : Upper (D 9) (R 9) [34,12,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7148 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7149 : Route 9 := (fun mask => (mask,id))

def c7149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7149 : Upper (D 9) (R 9) [34,12,80,384,129] 13 := by
  apply FastRouting.sound _ _ [34,12,80,384,129] 13 (by decide) (choices 1) [1,64,256] r7149 c7149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3867
  · exact u3868
  · exact u3869

def r7150 : Route 9 := (fun mask => (mask,id))

def c7150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7150 : Upper (D 9) (R 9) [34,12,80,384,160] 13 := by
  apply FastRouting.sound _ _ [34,12,80,384,160] 13 (by decide) (choices 1) [1,64,256] r7150 c7150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3870
  · exact u3871
  · exact u3872

def b7151 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 4, targets := 417 },{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 35 14 84 392 208 289 353 417 289), lower := (rows 35 14 84 392 208 32 64 128 256), losses := [] }

theorem u7151 : Upper (D 9) (R 9) [34,12,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7151 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7152 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 14 84 392 400 97 97 225 353), lower := (rows 35 14 84 392 400 32 64 128 256), losses := [] }

theorem u7152 : Upper (D 9) (R 9) [34,12,80,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7152 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7153 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 356, targets := 128 }], pairs := [(0,6),(2,7),(3,5),(4,5),(4,6)], upper := (rows 35 14 100 200 145 305 337 401 273), lower := (rows 35 14 100 200 145 32 64 128 256), losses := [] }

theorem u7153 : Upper (D 9) (R 9) [34,12,96,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7153 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7154 : Route 9 := (fun mask => (mask,id))

def c7154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7154 : Upper (D 9) (R 9) [34,12,96,192,257] 13 := by
  apply FastRouting.sound _ _ [34,12,96,192,257] 13 (by decide) (choices 1) [1,16,128,256] r7154 c7154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3873
  · exact u3874
  · exact u3875
  · exact u3876

def r7155 : Route 9 := (fun mask => (mask,id))

def c7155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7155 : Upper (D 9) (R 9) [34,12,96,192,384] 13 := by
  apply FastRouting.sound _ _ [34,12,96,192,384] 13 (by decide) (choices 1) [1,16,256] r7155 c7155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3877
  · exact u3878
  · exact u3879

def r7156 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7156 : Upper (D 9) (R 9) [34,12,96,384,65] 13 := by
  apply FastRouting.sound _ _ [34,12,96,384,65] 13 (by decide) (choices 1) [1,16,128] r7156 c7156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3880
  · exact u3881
  · exact u3882

def r7157 : Route 9 := (fun mask => (mask,id))

def c7157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7157 : Upper (D 9) (R 9) [34,12,96,384,129] 13 := by
  apply FastRouting.sound _ _ [34,12,96,384,129] 13 (by decide) (choices 1) [1,16,64,256] r7157 c7157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3883
  · exact u3884
  · exact u3885
  · exact u3886

def r7158 : Route 9 := (fun mask => (mask,id))

def c7158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7158 : Upper (D 9) (R 9) [34,12,96,384,192] 13 := by
  apply FastRouting.sound _ _ [34,12,96,384,192] 13 (by decide) (choices 1) [1,16,256] r7158 c7158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3887
  · exact u3888
  · exact u3889

def b7159 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 14 100 392 400 113 81 209 337), lower := (rows 35 14 100 392 400 32 64 128 256), losses := [] }

theorem u7159 : Upper (D 9) (R 9) [34,12,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7159 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7160 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 14 196 328 49 433 465 401 401), lower := (rows 35 14 196 328 49 32 64 128 256), losses := [] }

theorem u7160 : Upper (D 9) (R 9) [34,12,192,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7160 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7161 : Route 9 := (fun mask => (mask,id))

def c7161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7161 : Upper (D 9) (R 9) [34,12,192,320,129] 13 := by
  apply FastRouting.sound _ _ [34,12,192,320,129] 13 (by decide) (choices 1) [1,16,256] r7161 c7161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3890
  · exact u3891
  · exact u3892

def r7162 : Route 9 := (fun mask => (mask,id))

def c7162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7162 : Upper (D 9) (R 9) [34,12,192,320,160] 13 := by
  apply FastRouting.sound _ _ [34,12,192,320,160] 13 (by decide) (choices 1) [1,16,256] r7162 c7162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3893
  · exact u3894
  · exact u3895

def r7163 : Route 9 := (fun mask => (mask,id))

def c7163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7163 : Upper (D 9) (R 9) [34,12,192,320,384] 13 := by
  apply FastRouting.sound _ _ [34,12,192,320,384] 13 (by decide) (choices 1) [1,16] r7163 c7163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3896
  · exact u3897

def b7164 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 13 28 112 416 448 384 384), lower := (rows 35 67 13 28 112 32 64 128 256), losses := [] }

theorem u7164 : Upper (D 9) (R 9) [34,65,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7164 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7165 : Route 9 := (fun mask => (mask,id))

def c7165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7165 : Upper (D 9) (R 9) [34,65,9,20,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,160] 13 (by decide) (choices 1) [64,128,256] r7165 c7165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3898
  · exact u3899
  · exact u3900

def r7166 : Route 9 := (fun mask => (mask,id))

def c7166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7166 : Upper (D 9) (R 9) [34,65,9,20,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,192] 13 (by decide) (choices 1) [128,256] r7166 c7166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3901
  · exact u3902

def r7167 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7167 : Upper (D 9) (R 9) [34,65,9,20,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,384] 13 (by decide) (choices 1) [64,128] r7167 c7167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3903
  · exact u3904

def b7168 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 67 13 44 208 432 464 400 400), lower := (rows 35 67 13 44 208 32 64 128 256), losses := [] }

theorem u7168 : Upper (D 9) (R 9) [34,65,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7168 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7169 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 67 13 44 400 496 464 464 464), lower := (rows 35 67 13 44 400 32 64 128 256), losses := [] }

theorem u7169 : Upper (D 9) (R 9) [34,65,9,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7169 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7170 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 56 84 416 448 384 384), lower := (rows 35 67 13 56 84 32 64 128 256), losses := [] }

theorem u7170 : Upper (D 9) (R 9) [34,65,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7170 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7171 : Route 9 := (fun mask => (mask,id))

def c7171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7171 : Upper (D 9) (R 9) [34,65,9,48,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,132] 13 (by decide) (choices 1) [64,128,256] r7171 c7171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3905
  · exact u3906
  · exact u3907

def r7172 : Route 9 := (fun mask => (mask,id))

def c7172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7172 : Upper (D 9) (R 9) [34,65,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,192] 13 (by decide) (choices 1) [4,128,256] r7172 c7172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3908
  · exact u3909
  · exact u3910

def r7173 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7173 : Upper (D 9) (R 9) [34,65,9,48,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,384] 13 (by decide) (choices 1) [4,64,128] r7173 c7173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3911
  · exact u3912
  · exact u3913

def b7174 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 12, targets := 416 }], pairs := [(2,5),(2,7),(2,8),(3,5),(3,7)], upper := (rows 35 67 13 76 176 432 464 400 400), lower := (rows 35 67 13 76 176 32 64 128 256), losses := [] }

theorem u7174 : Upper (D 9) (R 9) [34,65,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7174 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7175 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 416 }], pairs := [(2,5),(2,7),(2,8),(3,5),(3,7)], upper := (rows 35 67 13 76 400 432 496 432 432), lower := (rows 35 67 13 76 400 32 64 128 256), losses := [] }

theorem u7175 : Upper (D 9) (R 9) [34,65,9,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7175 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7176 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 417, targets := 64 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(4,0),(4,6)], upper := (rows 35 67 13 88 52 416 448 384 384), lower := (rows 35 67 13 88 52 32 64 128 256), losses := [] }

theorem u7176 : Upper (D 9) (R 9) [34,65,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7176 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7177 : Route 9 := (fun mask => (mask,id))

def c7177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7177 : Upper (D 9) (R 9) [34,65,9,80,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,132] 13 (by decide) (choices 1) [128,256] r7177 c7177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3914
  · exact u3915

def r7178 : Route 9 := (fun mask => (mask,id))

def c7178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7178 : Upper (D 9) (R 9) [34,65,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,160] 13 (by decide) (choices 1) [4,128,256] r7178 c7178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3916
  · exact u3917
  · exact u3918

def r7179 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7179 : Upper (D 9) (R 9) [34,65,9,80,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,384] 13 (by decide) (choices 1) [4,128] r7179 c7179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3919
  · exact u3920

def b7180 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 13 104 148 432 464 400 400), lower := (rows 35 67 13 104 148 32 64 128 256), losses := [] }

theorem u7180 : Upper (D 9) (R 9) [34,65,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7180 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7181 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 13 104 400 436 468 404 404), lower := (rows 35 67 13 104 400 32 64 128 256), losses := [] }

theorem u7181 : Upper (D 9) (R 9) [34,65,9,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7181 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7182 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 3, targets := 384 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,0)], upper := (rows 35 67 13 140 112 432 464 400 400), lower := (rows 35 67 13 140 112 32 64 128 256), losses := [] }

theorem u7182 : Upper (D 9) (R 9) [34,65,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7182 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7183 : Route 9 := (fun mask => (mask,id))

def c7183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7183 : Upper (D 9) (R 9) [34,65,9,132,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,160] 13 (by decide) (choices 1) [16,64,256] r7183 c7183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3921
  · exact u3922
  · exact u3923

def r7184 : Route 9 := (fun mask => (mask,id))

def c7184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7184 : Upper (D 9) (R 9) [34,65,9,132,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,192] 13 (by decide) (choices 1) [16,256] r7184 c7184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3924
  · exact u3925

def r7185 : Route 9 := (fun mask => (mask,id))

def c7185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7185 : Upper (D 9) (R 9) [34,65,9,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,288] 13 (by decide) (choices 1) [16,64,128,256] r7185 c7185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3926
  · exact u3927
  · exact u3928
  · exact u3929

def r7186 : Route 9 := (fun mask => (mask,id))

def c7186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7186 : Upper (D 9) (R 9) [34,65,9,132,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,320] 13 (by decide) (choices 1) [16,128,256] r7186 c7186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3930
  · exact u3931
  · exact u3932

def r7187 : Route 9 := (fun mask => (mask,id))

def c7187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7187 : Upper (D 9) (R 9) [34,65,9,132,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,384] 13 (by decide) (choices 1) [16,64,256] r7187 c7187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3933
  · exact u3934
  · exact u3935

def r7188 : Route 9 := (fun mask => (mask,id))

def c7188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7188 : Upper (D 9) (R 9) [34,65,9,144,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,36] 13 (by decide) (choices 1) [64,128,256] r7188 c7188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3936
  · exact u3937
  · exact u3938

def r7189 : Route 9 := (fun mask => (mask,id))

def c7189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7189 : Upper (D 9) (R 9) [34,65,9,144,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,68] 13 (by decide) (choices 1) [128,256] r7189 c7189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3939
  · exact u3940

def b7190 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 3, targets := 384 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,0)], upper := (rows 35 67 13 152 112 420 452 388 388), lower := (rows 35 67 13 152 112 32 64 128 256), losses := [] }

theorem u7190 : Upper (D 9) (R 9) [34,65,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7190 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7191 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 96 }], pairs := [(0,7),(1,7),(2,7),(3,5),(3,6)], upper := (rows 35 67 13 152 148 352 352 480 352), lower := (rows 35 67 13 152 148 32 64 128 256), losses := [] }

theorem u7191 : Upper (D 9) (R 9) [34,65,9,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7191 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7192 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 13 152 176 356 324 452 324), lower := (rows 35 67 13 152 176 32 64 128 256), losses := [] }

theorem u7192 : Upper (D 9) (R 9) [34,65,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7192 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7193 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 13 152 208 292 356 420 292), lower := (rows 35 67 13 152 208 32 64 128 256), losses := [] }

theorem u7193 : Upper (D 9) (R 9) [34,65,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7193 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7194 : Route 9 := (fun mask => (mask,id))

def c7194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7194 : Upper (D 9) (R 9) [34,65,9,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,260] 13 (by decide) (choices 1) [64,128,256] r7194 c7194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3941
  · exact u3942
  · exact u3943

def r7195 : Route 9 := (fun mask => (mask,id))

def c7195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7195 : Upper (D 9) (R 9) [34,65,9,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,288] 13 (by decide) (choices 1) [4,64,128,256] r7195 c7195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3944
  · exact u3945
  · exact u3946
  · exact u3947

def r7196 : Route 9 := (fun mask => (mask,id))

def c7196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7196 : Upper (D 9) (R 9) [34,65,9,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,320] 13 (by decide) (choices 1) [4,128,256] r7196 c7196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3948
  · exact u3949
  · exact u3950

def b7197 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 13 152 400 356 356 484 356), lower := (rows 35 67 13 152 400 32 64 128 256), losses := [] }

theorem u7197 : Upper (D 9) (R 9) [34,65,9,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7197 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7198 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,5),(3,0),(3,6),(4,0),(4,5)], upper := (rows 35 67 13 168 84 432 464 400 400), lower := (rows 35 67 13 168 84 32 64 128 256), losses := [] }

theorem u7198 : Upper (D 9) (R 9) [34,65,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7198 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7199 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 168 148 368 336 464 336), lower := (rows 35 67 13 168 148 32 64 128 256), losses := [] }

theorem u7199 : Upper (D 9) (R 9) [34,65,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7199 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u7199
end Delivery.IrregularNine14.P09
