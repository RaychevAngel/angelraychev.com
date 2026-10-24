import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0065
import IrregularNine14P06C0066

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16140 : Route 9 := (fun mask => (mask,id))

def c16140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16140 : Upper (D 6) (R 6) [10,132,34,80,288,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,288,1] 13 (by decide) (choices 1) [1,4] r16140 c16140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3956
  · exact u3957

def b16141 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 88 304 36 65 193 321), lower := (rows 11 134 38 88 304 36 64 128 256), losses := [] }

theorem u16141 : Upper (D 6) (R 6) [10,132,34,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16142 : Route 9 := (fun mask => (mask,id))

def c16142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16142 : Upper (D 6) (R 6) [10,132,34,80,288,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,288,64] 13 (by decide) (choices 1) [1,4] r16142 c16142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3958
  · exact u3959

def b16143 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 40, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 134 38 104 81 33 340 404 276), lower := (rows 11 134 38 104 81 33 64 128 256), losses := [] }

theorem u16143 : Upper (D 6) (R 6) [10,132,34,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16144 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 104 81 36 337 401 273), lower := (rows 11 134 38 104 81 36 64 128 256), losses := [] }

theorem u16144 : Upper (D 6) (R 6) [10,132,34,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16145 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 104 81 48 325 389 261), lower := (rows 11 134 38 104 81 48 64 128 256), losses := [] }

theorem u16145 : Upper (D 6) (R 6) [10,132,34,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16145 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16146 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 134 38 104 81 288 85 149 277), lower := (rows 11 134 38 104 81 288 64 128 256), losses := [] }

theorem u16146 : Upper (D 6) (R 6) [10,132,34,96,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16146 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16147 : Route 9 := (fun mask => (mask,id))

def c16147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16147 : Upper (D 6) (R 6) [10,132,34,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,68,1] 13 (by decide) (choices 1) [1,16,256] r16147 c16147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3960
  · exact u3961
  · exact u3962

def b16148 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 104 84 48 321 385 257), lower := (rows 11 134 38 104 84 48 64 128 256), losses := [] }

theorem u16148 : Upper (D 6) (R 6) [10,132,34,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16148 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16149 : Route 9 := (fun mask => (mask,id))

def c16149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16149 : Upper (D 6) (R 6) [10,132,34,96,68,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,68,256] 13 (by decide) (choices 1) [1,16] r16149 c16149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3963
  · exact u3964

def r16150 : Route 9 := (fun mask => (mask,id))

def c16150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16150 : Upper (D 6) (R 6) [10,132,34,96,257,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,257,1] 13 (by decide) (choices 1) [4,16] r16150 c16150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3965
  · exact u3966

def b16151 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 104 273 36 81 209 337), lower := (rows 11 134 38 104 273 36 64 128 256), losses := [] }

theorem u16151 : Upper (D 6) (R 6) [10,132,34,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16152 : Route 9 := (fun mask => (mask,id))

def c16152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16152 : Upper (D 6) (R 6) [10,132,34,96,257,16] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,257,16] 13 (by decide) (choices 1) [1,4] r16152 c16152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3967
  · exact u3968

def b16153 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 104 273 96 85 149 277), lower := (rows 11 134 38 104 273 96 64 128 256), losses := [] }

theorem u16153 : Upper (D 6) (R 6) [10,132,34,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16154 : Route 9 := (fun mask => (mask,id))

def c16154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16154 : Upper (D 6) (R 6) [10,132,34,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,260,1] 13 (by decide) (choices 1) [1,16] r16154 c16154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3969
  · exact u3970

def b16155 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 104 276 48 65 193 321), lower := (rows 11 134 38 104 276 48 64 128 256), losses := [] }

theorem u16155 : Upper (D 6) (R 6) [10,132,34,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16155 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16156 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 104 276 96 81 145 273), lower := (rows 11 134 38 104 276 96 64 128 256), losses := [] }

theorem u16156 : Upper (D 6) (R 6) [10,132,34,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16157 : Route 9 := (fun mask => (mask,id))

def c16157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16157 : Upper (D 6) (R 6) [10,132,34,96,320,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,320,1] 13 (by decide) (choices 1) [1,4,16] r16157 c16157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3971
  · exact u3972
  · exact u3973

def b16158 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 104 336 36 81 145 273), lower := (rows 11 134 38 104 336 36 64 128 256), losses := [] }

theorem u16158 : Upper (D 6) (R 6) [10,132,34,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16159 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 38 104 336 48 69 133 261), lower := (rows 11 134 38 104 336 48 64 128 256), losses := [] }

theorem u16159 : Upper (D 6) (R 6) [10,132,34,96,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16159 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16160 : PairBound 9 := { available := 80, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 265 49 36 80 208 336), lower := (rows 11 134 38 265 49 36 64 128 256), losses := [] }

theorem u16160 : Upper (D 6) (R 6) [10,132,34,257,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16161 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 265 49 48 68 196 324), lower := (rows 11 134 38 265 49 48 64 128 256), losses := [] }

theorem u16161 : Upper (D 6) (R 6) [10,132,34,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16161 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16162 : Route 9 := (fun mask => (mask,id))

def c16162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16162 : Upper (D 6) (R 6) [10,132,34,257,33,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,257,33,64] 13 (by decide) (choices 1) [4,16] r16162 c16162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3974
  · exact u3975

def b16163 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 265 81 36 112 240 368), lower := (rows 11 134 38 265 81 36 64 128 256), losses := [] }

theorem u16163 : Upper (D 6) (R 6) [10,132,34,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16164 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 38 265 81 48 100 228 356), lower := (rows 11 134 38 265 81 48 64 128 256), losses := [] }

theorem u16164 : Upper (D 6) (R 6) [10,132,34,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16164 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16165 : Route 9 := (fun mask => (mask,id))

def c16165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16165 : Upper (D 6) (R 6) [10,132,34,257,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,257,65,64] 13 (by decide) (choices 1) [4,16,32] r16165 c16165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3976
  · exact u3977
  · exact u3978

def b16166 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 265 84 33 112 240 368), lower := (rows 11 134 38 265 84 33 64 128 256), losses := [] }

theorem u16166 : Upper (D 6) (R 6) [10,132,34,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16167 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 265 84 48 97 225 353), lower := (rows 11 134 38 265 84 48 64 128 256), losses := [] }

theorem u16167 : Upper (D 6) (R 6) [10,132,34,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16167 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16168 : Route 9 := (fun mask => (mask,id))

def c16168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16168 : Upper (D 6) (R 6) [10,132,34,257,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,257,68,64] 13 (by decide) (choices 1) [1,16,32] r16168 c16168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3979
  · exact u3980
  · exact u3981

def b16169 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 265 112 33 84 212 340), lower := (rows 11 134 38 265 112 33 64 128 256), losses := [] }

theorem u16169 : Upper (D 6) (R 6) [10,132,34,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16170 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 265 112 36 81 209 337), lower := (rows 11 134 38 265 112 36 64 128 256), losses := [] }

theorem u16170 : Upper (D 6) (R 6) [10,132,34,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16171 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 265 112 48 69 197 325), lower := (rows 11 134 38 265 112 48 64 128 256), losses := [] }

theorem u16171 : Upper (D 6) (R 6) [10,132,34,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16171 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16172 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 265 112 96 85 149 277), lower := (rows 11 134 38 265 112 96 64 128 256), losses := [] }

theorem u16172 : Upper (D 6) (R 6) [10,132,34,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16173 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 268 49 33 80 208 336), lower := (rows 11 134 38 268 49 33 64 128 256), losses := [] }

theorem u16173 : Upper (D 6) (R 6) [10,132,34,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16174 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 268 49 48 65 193 321), lower := (rows 11 134 38 268 49 48 64 128 256), losses := [] }

theorem u16174 : Upper (D 6) (R 6) [10,132,34,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16174 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16175 : Route 9 := (fun mask => (mask,id))

def c16175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16175 : Upper (D 6) (R 6) [10,132,34,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,260,33,64] 13 (by decide) (choices 1) [1,16] r16175 c16175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3982
  · exact u3983

def b16176 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 134 38 268 81 33 112 240 368), lower := (rows 11 134 38 268 81 33 64 128 256), losses := [] }

theorem u16176 : Upper (D 6) (R 6) [10,132,34,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16177 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 268 81 48 97 225 353), lower := (rows 11 134 38 268 81 48 64 128 256), losses := [] }

theorem u16177 : Upper (D 6) (R 6) [10,132,34,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16177 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16178 : Route 9 := (fun mask => (mask,id))

def c16178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16178 : Upper (D 6) (R 6) [10,132,34,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,260,65,64] 13 (by decide) (choices 1) [1,16,32] r16178 c16178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3984
  · exact u3985
  · exact u3986

def b16179 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 134 38 268 112 33 81 209 337), lower := (rows 11 134 38 268 112 33 64 128 256), losses := [] }

theorem u16179 : Upper (D 6) (R 6) [10,132,34,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16180 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 268 112 48 65 193 321), lower := (rows 11 134 38 268 112 48 64 128 256), losses := [] }

theorem u16180 : Upper (D 6) (R 6) [10,132,34,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16180 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16181 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 268 112 96 81 145 273), lower := (rows 11 134 38 268 112 96 64 128 256), losses := [] }

theorem u16181 : Upper (D 6) (R 6) [10,132,34,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16182 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 11 134 38 280 21 33 96 224 352), lower := (rows 11 134 38 280 21 33 64 128 256), losses := [] }

theorem u16182 : Upper (D 6) (R 6) [10,132,34,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16183 : Route 9 := (fun mask => (mask,id))

def c16183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16183 : Upper (D 6) (R 6) [10,132,34,272,5,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,5,64] 13 (by decide) (choices 1) [1,32] r16183 c16183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3987
  · exact u3988

def b16184 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 280 49 33 68 196 324), lower := (rows 11 134 38 280 49 33 64 128 256), losses := [] }

theorem u16184 : Upper (D 6) (R 6) [10,132,34,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16185 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 280 49 36 65 193 321), lower := (rows 11 134 38 280 49 36 64 128 256), losses := [] }

theorem u16185 : Upper (D 6) (R 6) [10,132,34,272,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16186 : Route 9 := (fun mask => (mask,id))

def c16186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16186 : Upper (D 6) (R 6) [10,132,34,272,33,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,33,64] 13 (by decide) (choices 1) [1,4] r16186 c16186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3989
  · exact u3990

def b16187 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 134 38 280 81 33 100 228 356), lower := (rows 11 134 38 280 81 33 64 128 256), losses := [] }

theorem u16187 : Upper (D 6) (R 6) [10,132,34,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16188 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 280 81 36 97 225 353), lower := (rows 11 134 38 280 81 36 64 128 256), losses := [] }

theorem u16188 : Upper (D 6) (R 6) [10,132,34,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16189 : Route 9 := (fun mask => (mask,id))

def c16189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16189 : Upper (D 6) (R 6) [10,132,34,272,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,65,64] 13 (by decide) (choices 1) [1,4,32] r16189 c16189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3991
  · exact u3992
  · exact u3993

def b16190 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 280 84 33 97 225 353), lower := (rows 11 134 38 280 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 33 97 161 289), good := (rows 489 156 508 280 92 481 64 128 256) }] }

theorem u16190 : Upper (D 6) (R 6) [10,132,34,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16191 : Route 9 := (fun mask => (mask,id))

def c16191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16191 : Upper (D 6) (R 6) [10,132,34,272,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,68,64] 13 (by decide) (choices 1) [1,32] r16191 c16191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3994
  · exact u3995

def r16192 : Route 9 := (fun mask => (mask,id))

def c16192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16192 : Upper (D 6) (R 6) [10,132,34,272,96,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,96,1] 13 (by decide) (choices 1) [1,4] r16192 c16192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3996
  · exact u3997

def b16193 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 280 112 36 65 193 321), lower := (rows 11 134 38 280 112 36 64 128 256), losses := [] }

theorem u16193 : Upper (D 6) (R 6) [10,132,34,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16194 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 280 112 96 69 133 261), lower := (rows 11 134 38 280 112 96 64 128 256), losses := [] }

theorem u16194 : Upper (D 6) (R 6) [10,132,34,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16195 : Route 9 := (fun mask => (mask,id))

def c16195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16195 : Upper (D 6) (R 6) [10,132,34,288,65,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288,65,1] 13 (by decide) (choices 1) [4,16] r16195 c16195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3998
  · exact u3999

def b16196 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 296 81 36 81 209 337), lower := (rows 11 134 38 296 81 36 64 128 256), losses := [] }

theorem u16196 : Upper (D 6) (R 6) [10,132,34,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16197 : Route 9 := (fun mask => (mask,id))

def c16197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16197 : Upper (D 6) (R 6) [10,132,34,288,65,16] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288,65,16] 13 (by decide) (choices 1) [1,4] r16197 c16197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4000
  · exact u4001

def r16198 : Route 9 := (fun mask => (mask,id))

def c16198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16198 : Upper (D 6) (R 6) [10,132,34,288,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288,65,64] 13 (by decide) (choices 1) [1,4,16] r16198 c16198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4002
  · exact u4003
  · exact u4004

def r16199 : Route 9 := (fun mask => (mask,id))

def c16199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16199 : Upper (D 6) (R 6) [10,132,34,288,68,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288,68,1] 13 (by decide) (choices 1) [1,16] r16199 c16199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4005
  · exact u4006

#print axioms u16199
end Delivery.IrregularNine14.P06
