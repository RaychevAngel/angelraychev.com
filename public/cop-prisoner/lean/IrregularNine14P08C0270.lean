import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0097

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16200 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 52 200 208 33 97 161 289), lower := (rows 259 14 52 200 208 32 64 128 256), losses := [] }

theorem u16200 : Upper (D 8) (R 8) [258,12,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16201 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 69 152 49 224 224 224 480), lower := (rows 259 14 69 152 49 32 64 128 256), losses := [] }

theorem u16201 : Upper (D 8) (R 8) [258,12,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16202 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 14 69 152 81 160 224 160 416), lower := (rows 259 14 69 152 81 32 64 128 256), losses := [] }

theorem u16202 : Upper (D 8) (R 8) [258,12,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16203 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 69 152 112 161 225 161 417), lower := (rows 259 14 69 152 112 32 64 128 256), losses := [] }

theorem u16203 : Upper (D 8) (R 8) [258,12,65,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16204 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 69 152 145 96 96 224 352), lower := (rows 259 14 69 152 145 32 64 128 256), losses := [] }

theorem u16204 : Upper (D 8) (R 8) [258,12,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16205 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 69 152 176 97 97 225 353), lower := (rows 259 14 69 152 176 32 64 128 256), losses := [] }

theorem u16205 : Upper (D 8) (R 8) [258,12,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16206 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 69 152 208 33 97 161 289), lower := (rows 259 14 69 152 208 32 64 128 256), losses := [] }

theorem u16206 : Upper (D 8) (R 8) [258,12,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16207 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 69 168 49 240 240 240 496), lower := (rows 259 14 69 168 49 32 64 128 256), losses := [] }

theorem u16207 : Upper (D 8) (R 8) [258,12,65,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16208 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 14 69 168 81 176 240 176 432), lower := (rows 259 14 69 168 81 32 64 128 256), losses := [] }

theorem u16208 : Upper (D 8) (R 8) [258,12,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16209 : Route 9 := (fun mask => (mask,id))

def c16209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16209 : Upper (D 8) (R 8) [258,12,65,160,96] 13 := by
  apply FastRouting.sound _ _ [258,12,65,160,96] 13 (by decide) (choices 1) [1,16,128] r16209 c16209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5825
  · exact u5826
  · exact u5827

def b16210 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 69 168 145 112 112 240 368), lower := (rows 259 14 69 168 145 32 64 128 256), losses := [] }

theorem u16210 : Upper (D 8) (R 8) [258,12,65,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16211 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 69 168 176 113 113 241 369), lower := (rows 259 14 69 168 176 32 64 128 256), losses := [] }

theorem u16211 : Upper (D 8) (R 8) [258,12,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16212 : Route 9 := (fun mask => (mask,id))

def c16212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16212 : Upper (D 8) (R 8) [258,12,65,160,192] 13 := by
  apply FastRouting.sound _ _ [258,12,65,160,192] 13 (by decide) (choices 1) [1,16] r16212 c16212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5828
  · exact u5829

def r16213 : Route 9 := (fun mask => (mask,id))

def c16213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16213 : Upper (D 8) (R 8) [258,12,80,160,33] 13 := by
  apply FastRouting.sound _ _ [258,12,80,160,33] 13 (by decide) (choices 1) [1,64,128] r16213 c16213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5830
  · exact u5831
  · exact u5832

def b16214 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 84 168 81 161 225 161 417), lower := (rows 259 14 84 168 81 32 64 128 256), losses := [] }

theorem u16214 : Upper (D 8) (R 8) [258,12,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16215 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 84 168 112 161 225 161 417), lower := (rows 259 14 84 168 112 32 64 128 256), losses := [] }

theorem u16215 : Upper (D 8) (R 8) [258,12,80,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16216 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 84 168 145 97 97 225 353), lower := (rows 259 14 84 168 145 32 64 128 256), losses := [] }

theorem u16216 : Upper (D 8) (R 8) [258,12,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16217 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 84 168 176 97 97 225 353), lower := (rows 259 14 84 168 176 32 64 128 256), losses := [] }

theorem u16217 : Upper (D 8) (R 8) [258,12,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16218 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 84 168 208 33 97 161 289), lower := (rows 259 14 84 168 208 32 64 128 256), losses := [] }

theorem u16218 : Upper (D 8) (R 8) [258,12,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m16219_128 : Upper (D 8) (R 8) [258,12,96,160,33,128] 13 :=
  permutation_upper _ _ _ [258,12,96,160,33,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5835

def r16219 : Route 9 := (fun mask => (mask,id))

def c16219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16219 : Upper (D 8) (R 8) [258,12,96,160,33] 13 := by
  apply FastRouting.sound _ _ [258,12,96,160,33] 13 (by decide) (choices 1) [1,16,64,128] r16219 c16219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5833
  · exact u5834
  · exact u5835
  · exact m16219_128

def b16220 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 259 14 100 168 81 177 241 177 433), lower := (rows 259 14 100 168 81 32 64 128 256), losses := [] }

theorem u16220 : Upper (D 8) (R 8) [258,12,96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16221 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 100 168 112 177 209 145 401), lower := (rows 259 14 100 168 112 32 64 128 256), losses := [] }

theorem u16221 : Upper (D 8) (R 8) [258,12,96,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16222 : Route 9 := (fun mask => (mask,id))

def c16222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16222 : Upper (D 8) (R 8) [258,12,96,160,192] 13 := by
  apply FastRouting.sound _ _ [258,12,96,160,192] 13 (by decide) (choices 1) [1,16] r16222 c16222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5836
  · exact u5837

def b16223 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 28 112 224 224 224 480), lower := (rows 259 35 13 28 112 32 64 128 256), losses := [] }

theorem u16223 : Upper (D 8) (R 8) [258,33,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16224 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 28 208 224 224 224 480), lower := (rows 259 35 13 28 208 32 64 128 256), losses := [] }

theorem u16224 : Upper (D 8) (R 8) [258,33,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16225 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 44 112 240 208 208 464), lower := (rows 259 35 13 44 112 32 64 128 256), losses := [] }

theorem u16225 : Upper (D 8) (R 8) [258,33,9,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16226 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 44 208 240 240 240 496), lower := (rows 259 35 13 44 208 32 64 128 256), losses := [] }

theorem u16226 : Upper (D 8) (R 8) [258,33,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16227 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 56 84 224 224 224 480), lower := (rows 259 35 13 56 84 32 64 128 256), losses := [] }

theorem u16227 : Upper (D 8) (R 8) [258,33,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16228 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 56 208 228 228 228 484), lower := (rows 259 35 13 56 208 32 64 128 256), losses := [] }

theorem u16228 : Upper (D 8) (R 8) [258,33,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16229 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 76 112 176 240 176 432), lower := (rows 259 35 13 76 112 32 64 128 256), losses := [] }

theorem u16229 : Upper (D 8) (R 8) [258,33,9,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16230 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 76 176 240 240 240 496), lower := (rows 259 35 13 76 176 32 64 128 256), losses := [] }

theorem u16230 : Upper (D 8) (R 8) [258,33,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16231 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 76 208 176 240 176 432), lower := (rows 259 35 13 76 208 32 64 128 256), losses := [] }

theorem u16231 : Upper (D 8) (R 8) [258,33,9,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16232 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 88 52 224 224 224 480), lower := (rows 259 35 13 88 52 32 64 128 256), losses := [] }

theorem u16232 : Upper (D 8) (R 8) [258,33,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16233 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 88 148 224 224 224 480), lower := (rows 259 35 13 88 148 32 64 128 256), losses := [] }

theorem u16233 : Upper (D 8) (R 8) [258,33,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16234 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 88 176 228 228 228 484), lower := (rows 259 35 13 88 176 32 64 128 256), losses := [] }

theorem u16234 : Upper (D 8) (R 8) [258,33,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16235 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 104 52 240 208 208 464), lower := (rows 259 35 13 104 52 32 64 128 256), losses := [] }

theorem u16235 : Upper (D 8) (R 8) [258,33,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16236 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 104 84 176 240 176 432), lower := (rows 259 35 13 104 84 32 64 128 256), losses := [] }

theorem u16236 : Upper (D 8) (R 8) [258,33,9,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16237 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 104 148 240 240 240 496), lower := (rows 259 35 13 104 148 32 64 128 256), losses := [] }

theorem u16237 : Upper (D 8) (R 8) [258,33,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16238 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 104 176 244 212 212 468), lower := (rows 259 35 13 104 176 32 64 128 256), losses := [] }

theorem u16238 : Upper (D 8) (R 8) [258,33,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16239 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 104 208 180 244 180 436), lower := (rows 259 35 13 104 208 32 64 128 256), losses := [] }

theorem u16239 : Upper (D 8) (R 8) [258,33,9,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16240 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 200 52 240 240 240 496), lower := (rows 259 35 13 200 52 32 64 128 256), losses := [] }

theorem u16240 : Upper (D 8) (R 8) [258,33,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16241 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 200 84 176 240 176 432), lower := (rows 259 35 13 200 84 32 64 128 256), losses := [] }

theorem u16241 : Upper (D 8) (R 8) [258,33,9,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16242 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 200 112 180 244 180 436), lower := (rows 259 35 13 200 112 32 64 128 256), losses := [] }

theorem u16242 : Upper (D 8) (R 8) [258,33,9,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16243 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 28 41 52 224 192 192 448), lower := (rows 259 35 28 41 52 32 64 128 256), losses := [] }

theorem u16243 : Upper (D 8) (R 8) [258,33,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16244 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 35 28 41 84 224 224 224 480), lower := (rows 259 35 28 41 84 32 64 128 256), losses := [] }

theorem u16244 : Upper (D 8) (R 8) [258,33,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16245 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 35 28 41 112 228 196 196 452), lower := (rows 259 35 28 41 112 32 64 128 256), losses := [] }

theorem u16245 : Upper (D 8) (R 8) [258,33,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16246 : PairBound 9 := { available := 228, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 35 28 41 208 228 228 228 484), lower := (rows 259 35 28 41 208 32 64 128 256), losses := [] }

theorem u16246 : Upper (D 8) (R 8) [258,33,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16247 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 44 81 224 224 224 480), lower := (rows 259 35 28 44 81 32 64 128 256), losses := [] }

theorem u16247 : Upper (D 8) (R 8) [258,33,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16248 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 44 112 225 193 193 449), lower := (rows 259 35 28 44 112 32 64 128 256), losses := [] }

theorem u16248 : Upper (D 8) (R 8) [258,33,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16249 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c16249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16249 : Upper (D 8) (R 8) [258,33,24,36,192] 13 := by
  apply FastRouting.sound _ _ [258,33,24,36,192] 13 (by decide) (choices 1) [1,64] r16249 c16249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5838
  · exact u5839

def b16250 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 28 73 84 160 224 160 416), lower := (rows 259 35 28 73 84 32 64 128 256), losses := [] }

theorem u16250 : Upper (D 8) (R 8) [258,33,24,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16251 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 73 112 164 228 164 420), lower := (rows 259 35 28 73 112 32 64 128 256), losses := [] }

theorem u16251 : Upper (D 8) (R 8) [258,33,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16252 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 73 148 224 224 224 480), lower := (rows 259 35 28 73 148 32 64 128 256), losses := [] }

theorem u16252 : Upper (D 8) (R 8) [258,33,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16253 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 73 176 228 228 228 484), lower := (rows 259 35 28 73 176 32 64 128 256), losses := [] }

theorem u16253 : Upper (D 8) (R 8) [258,33,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16254 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 73 208 164 228 164 420), lower := (rows 259 35 28 73 208 32 64 128 256), losses := [] }

theorem u16254 : Upper (D 8) (R 8) [258,33,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16255 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 76 112 161 225 161 417), lower := (rows 259 35 28 76 112 32 64 128 256), losses := [] }

theorem u16255 : Upper (D 8) (R 8) [258,33,24,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16256 : Route 9 := (fun mask => (mask,id))

def c16256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16256 : Upper (D 8) (R 8) [258,33,24,68,160] 13 := by
  apply FastRouting.sound _ _ [258,33,24,68,160] 13 (by decide) (choices 1) [1,64,128] r16256 c16256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5840
  · exact u5841
  · exact u5842

def b16257 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 76 208 161 225 161 417), lower := (rows 259 35 28 76 208 32 64 128 256), losses := [] }

theorem u16257 : Upper (D 8) (R 8) [258,33,24,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16258 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 104 112 165 197 133 389), lower := (rows 259 35 28 104 112 32 64 128 256), losses := [] }

theorem u16258 : Upper (D 8) (R 8) [258,33,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m16259_128 : Upper (D 8) (R 8) [258,33,24,96,160,128] 13 :=
  permutation_upper _ _ _ [258,33,24,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5845

def r16259 : Route 9 := (fun mask => (mask,id))

def c16259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16259 : Upper (D 8) (R 8) [258,33,24,96,160] 13 := by
  apply FastRouting.sound _ _ [258,33,24,96,160] 13 (by decide) (choices 1) [1,4,64,128] r16259 c16259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5843
  · exact u5844
  · exact u5845
  · exact m16259_128

#print axioms u16259
end Delivery.IrregularNine14.P08
