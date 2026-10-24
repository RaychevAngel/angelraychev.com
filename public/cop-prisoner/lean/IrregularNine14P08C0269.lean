import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0096
import IrregularNine14P08C0097

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16140 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 196 25 88 160 224 160 416), lower := (rows 259 7 196 25 88 32 64 128 256), losses := [] }

theorem u16140 : Upper (D 8) (R 8) [258,5,192,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16141 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 25 112 168 232 168 424), lower := (rows 259 7 196 25 112 32 64 128 256), losses := [] }

theorem u16141 : Upper (D 8) (R 8) [258,5,192,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16142 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 41 56 240 240 240 496), lower := (rows 259 7 196 41 56 32 64 128 256), losses := [] }

theorem u16142 : Upper (D 8) (R 8) [258,5,192,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16143 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 41 88 176 240 176 432), lower := (rows 259 7 196 41 88 32 64 128 256), losses := [] }

theorem u16143 : Upper (D 8) (R 8) [258,5,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16144 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 41 112 184 248 184 440), lower := (rows 259 7 196 41 112 32 64 128 256), losses := [] }

theorem u16144 : Upper (D 8) (R 8) [258,5,192,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16145 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 196 56 56 225 225 225 481), lower := (rows 259 7 196 56 56 32 64 128 256), losses := [] }

theorem u16145 : Upper (D 8) (R 8) [258,5,192,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16146 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 56 81 168 232 168 424), lower := (rows 259 7 196 56 81 32 64 128 256), losses := [] }

theorem u16146 : Upper (D 8) (R 8) [258,5,192,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16147 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 196 56 88 161 225 161 417), lower := (rows 259 7 196 56 88 32 64 128 256), losses := [] }

theorem u16147 : Upper (D 8) (R 8) [258,5,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16148 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 196 56 112 169 233 169 425), lower := (rows 259 7 196 56 112 32 64 128 256), losses := [] }

theorem u16148 : Upper (D 8) (R 8) [258,5,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16149 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 7 196 56 208 41 105 169 297), lower := (rows 259 7 196 56 208 32 64 128 256), losses := [] }

theorem u16149 : Upper (D 8) (R 8) [258,5,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16150 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 73 152 48 112 176 304), lower := (rows 259 7 196 73 152 32 64 128 256), losses := [] }

theorem u16150 : Upper (D 8) (R 8) [258,5,192,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16151 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 73 176 56 120 184 312), lower := (rows 259 7 196 73 176 32 64 128 256), losses := [] }

theorem u16151 : Upper (D 8) (R 8) [258,5,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16152 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 196 88 152 33 97 161 289), lower := (rows 259 7 196 88 152 32 64 128 256), losses := [] }

theorem u16152 : Upper (D 8) (R 8) [258,5,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16153 : Route 9 := (fun mask => (mask,id))

def c16153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16153 : Upper (D 8) (R 8) [258,5,192,80,160] 13 := by
  apply FastRouting.sound _ _ [258,5,192,80,160] 13 (by decide) (choices 1) [1,8] r16153 c16153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5800
  · exact u5801

theorem m16154_16 : Upper (D 8) (R 8) [258,5,192,96,160,16] 13 :=
  permutation_upper _ _ _ [258,5,192,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5803

def r16154 : Route 9 := (fun mask => (mask,id))

def c16154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16154 : Upper (D 8) (R 8) [258,5,192,96,160] 13 := by
  apply FastRouting.sound _ _ [258,5,192,96,160] 13 (by decide) (choices 1) [1,8,16] r16154 c16154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5802
  · exact u5803
  · exact m16154_16

def b16155 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 14 21 104 49 224 224 224 480), lower := (rows 259 14 21 104 49 32 64 128 256), losses := [] }

theorem u16155 : Upper (D 8) (R 8) [258,12,17,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16156 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 21 104 81 160 224 160 416), lower := (rows 259 14 21 104 81 32 64 128 256), losses := [] }

theorem u16156 : Upper (D 8) (R 8) [258,12,17,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16157 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 21 104 112 161 225 161 417), lower := (rows 259 14 21 104 112 32 64 128 256), losses := [] }

theorem u16157 : Upper (D 8) (R 8) [258,12,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16158 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 14 21 104 145 224 224 224 480), lower := (rows 259 14 21 104 145 32 64 128 256), losses := [] }

theorem u16158 : Upper (D 8) (R 8) [258,12,17,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16159 : Route 9 := (fun mask => (mask,id))

def c16159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16159 : Upper (D 8) (R 8) [258,12,17,96,160] 13 := by
  apply FastRouting.sound _ _ [258,12,17,96,160] 13 (by decide) (choices 1) [1,64,128] r16159 c16159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5804
  · exact u5805
  · exact u5806

def b16160 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 21 104 208 161 225 161 417), lower := (rows 259 14 21 104 208 32 64 128 256), losses := [] }

theorem u16160 : Upper (D 8) (R 8) [258,12,17,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16161 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 14 21 200 49 224 224 224 480), lower := (rows 259 14 21 200 49 32 64 128 256), losses := [] }

theorem u16161 : Upper (D 8) (R 8) [258,12,17,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16162 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 21 200 81 160 224 160 416), lower := (rows 259 14 21 200 81 32 64 128 256), losses := [] }

theorem u16162 : Upper (D 8) (R 8) [258,12,17,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16163 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 21 200 112 161 225 161 417), lower := (rows 259 14 21 200 112 32 64 128 256), losses := [] }

theorem u16163 : Upper (D 8) (R 8) [258,12,17,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16164 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 21 200 208 33 97 161 289), lower := (rows 259 14 21 200 208 32 64 128 256), losses := [] }

theorem u16164 : Upper (D 8) (R 8) [258,12,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16165 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 26, targets := 64 }], pairs := [(1,6)], upper := (rows 259 14 37 56 49 224 192 192 448), lower := (rows 259 14 37 56 49 32 64 128 256), losses := [] }

theorem u16165 : Upper (D 8) (R 8) [258,12,33,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16166 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 37 56 81 224 224 224 480), lower := (rows 259 14 37 56 81 32 64 128 256), losses := [] }

theorem u16166 : Upper (D 8) (R 8) [258,12,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16167 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 37 56 112 225 193 193 449), lower := (rows 259 14 37 56 112 32 64 128 256), losses := [] }

theorem u16167 : Upper (D 8) (R 8) [258,12,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16168 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c16168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16168 : Upper (D 8) (R 8) [258,12,33,48,192] 13 := by
  apply FastRouting.sound _ _ [258,12,33,48,192] 13 (by decide) (choices 1) [1,64] r16168 c16168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5807
  · exact u5808

def b16169 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 14 37 88 49 224 224 224 480), lower := (rows 259 14 37 88 49 32 64 128 256), losses := [] }

theorem u16169 : Upper (D 8) (R 8) [258,12,33,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16170 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 37 88 81 160 224 160 416), lower := (rows 259 14 37 88 81 32 64 128 256), losses := [] }

theorem u16170 : Upper (D 8) (R 8) [258,12,33,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16171 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 37 88 112 161 225 161 417), lower := (rows 259 14 37 88 112 32 64 128 256), losses := [] }

theorem u16171 : Upper (D 8) (R 8) [258,12,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16172 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 37 88 145 224 224 224 480), lower := (rows 259 14 37 88 145 32 64 128 256), losses := [] }

theorem u16172 : Upper (D 8) (R 8) [258,12,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16173 : Route 9 := (fun mask => (mask,id))

def c16173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16173 : Upper (D 8) (R 8) [258,12,33,80,160] 13 := by
  apply FastRouting.sound _ _ [258,12,33,80,160] 13 (by decide) (choices 1) [1,64,128] r16173 c16173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5809
  · exact u5810
  · exact u5811

def b16174 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 37 88 208 161 225 161 417), lower := (rows 259 14 37 88 208 32 64 128 256), losses := [] }

theorem u16174 : Upper (D 8) (R 8) [258,12,33,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16175 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 14 37 104 49 240 208 208 464), lower := (rows 259 14 37 104 49 32 64 128 256), losses := [] }

theorem u16175 : Upper (D 8) (R 8) [258,12,33,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16176 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 37 104 81 176 240 176 432), lower := (rows 259 14 37 104 81 32 64 128 256), losses := [] }

theorem u16176 : Upper (D 8) (R 8) [258,12,33,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16177 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 37 104 112 177 209 145 401), lower := (rows 259 14 37 104 112 32 64 128 256), losses := [] }

theorem u16177 : Upper (D 8) (R 8) [258,12,33,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16178 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 37 104 145 240 240 240 496), lower := (rows 259 14 37 104 145 32 64 128 256), losses := [] }

theorem u16178 : Upper (D 8) (R 8) [258,12,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16179 : Route 9 := (fun mask => (mask,id))

def c16179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16179 : Upper (D 8) (R 8) [258,12,33,96,160] 13 := by
  apply FastRouting.sound _ _ [258,12,33,96,160] 13 (by decide) (choices 1) [1,16,64,128] r16179 c16179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5812
  · exact u5813
  · exact u5814
  · exact u5815

def r16180 : Route 9 := (fun mask => (mask,id))

def c16180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16180 : Upper (D 8) (R 8) [258,12,33,96,192] 13 := by
  apply FastRouting.sound _ _ [258,12,33,96,192] 13 (by decide) (choices 1) [1,16,128] r16180 c16180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5816
  · exact u5817
  · exact u5818

def b16181 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 14 37 200 49 240 240 240 496), lower := (rows 259 14 37 200 49 32 64 128 256), losses := [] }

theorem u16181 : Upper (D 8) (R 8) [258,12,33,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16182 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 37 200 81 176 240 176 432), lower := (rows 259 14 37 200 81 32 64 128 256), losses := [] }

theorem u16182 : Upper (D 8) (R 8) [258,12,33,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16183 : Route 9 := (fun mask => (mask,id))

def c16183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16183 : Upper (D 8) (R 8) [258,12,33,192,96] 13 := by
  apply FastRouting.sound _ _ [258,12,33,192,96] 13 (by decide) (choices 1) [1,16,128] r16183 c16183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5819
  · exact u5820
  · exact u5821

def b16184 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 37 200 208 49 113 177 305), lower := (rows 259 14 37 200 208 32 64 128 256), losses := [] }

theorem u16184 : Upper (D 8) (R 8) [258,12,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16185 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 14 52 73 49 224 224 224 480), lower := (rows 259 14 52 73 49 32 64 128 256), losses := [] }

theorem u16185 : Upper (D 8) (R 8) [258,12,48,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16186 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 14 52 73 81 160 224 160 416), lower := (rows 259 14 52 73 81 32 64 128 256), losses := [] }

theorem u16186 : Upper (D 8) (R 8) [258,12,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16187 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 14 52 73 112 161 225 161 417), lower := (rows 259 14 52 73 112 32 64 128 256), losses := [] }

theorem u16187 : Upper (D 8) (R 8) [258,12,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16188 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 259 14 52 73 145 224 224 224 480), lower := (rows 259 14 52 73 145 32 64 128 256), losses := [] }

theorem u16188 : Upper (D 8) (R 8) [258,12,48,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16189 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 14 52 73 176 225 225 225 481), lower := (rows 259 14 52 73 176 32 64 128 256), losses := [] }

theorem u16189 : Upper (D 8) (R 8) [258,12,48,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16190 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 52 73 208 161 225 161 417), lower := (rows 259 14 52 73 208 32 64 128 256), losses := [] }

theorem u16190 : Upper (D 8) (R 8) [258,12,48,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16191 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 14 52 104 49 225 193 193 449), lower := (rows 259 14 52 104 49 32 64 128 256), losses := [] }

theorem u16191 : Upper (D 8) (R 8) [258,12,48,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16192 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 52 104 81 161 225 161 417), lower := (rows 259 14 52 104 81 32 64 128 256), losses := [] }

theorem u16192 : Upper (D 8) (R 8) [258,12,48,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16193 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 52 104 112 161 193 129 385), lower := (rows 259 14 52 104 112 32 64 128 256), losses := [] }

theorem u16193 : Upper (D 8) (R 8) [258,12,48,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16194 : Route 9 := (fun mask => (mask,id))

def c16194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16194 : Upper (D 8) (R 8) [258,12,48,96,129] 13 := by
  apply FastRouting.sound _ _ [258,12,48,96,129] 13 (by decide) (choices 1) [1,64,128] r16194 c16194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5822
  · exact u5823
  · exact u5824

def b16195 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 14 52 104 176 225 193 193 449), lower := (rows 259 14 52 104 176 32 64 128 256), losses := [] }

theorem u16195 : Upper (D 8) (R 8) [258,12,48,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16196 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 52 104 208 161 225 161 417), lower := (rows 259 14 52 104 208 32 64 128 256), losses := [] }

theorem u16196 : Upper (D 8) (R 8) [258,12,48,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16197 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 14 52 200 49 225 225 225 481), lower := (rows 259 14 52 200 49 32 64 128 256), losses := [] }

theorem u16197 : Upper (D 8) (R 8) [258,12,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16198 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 52 200 81 161 225 161 417), lower := (rows 259 14 52 200 81 32 64 128 256), losses := [] }

theorem u16198 : Upper (D 8) (R 8) [258,12,48,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16199 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 14 52 200 112 161 225 161 417), lower := (rows 259 14 52 200 112 32 64 128 256), losses := [] }

theorem u16199 : Upper (D 8) (R 8) [258,12,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16199
end Delivery.IrregularNine14.P08
