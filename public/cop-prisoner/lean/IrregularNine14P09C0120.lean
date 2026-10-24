import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0065
import IrregularNine14P09C0066
import IrregularNine14P09C0067

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7200 : Route 9 := (fun mask => (mask,id))

def c7200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7200 : Upper (D 9) (R 9) [34,65,9,160,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,192] 13 (by decide) (choices 1) [4,16,256] r7200 c7200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3951
  · exact u3952
  · exact u3953

def r7201 : Route 9 := (fun mask => (mask,id))

def c7201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7201 : Upper (D 9) (R 9) [34,65,9,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,260] 13 (by decide) (choices 1) [16,64,128,256] r7201 c7201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3954
  · exact u3955
  · exact u3956
  · exact u3957

def r7202 : Route 9 := (fun mask => (mask,id))

def c7202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7202 : Upper (D 9) (R 9) [34,65,9,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,320] 13 (by decide) (choices 1) [4,16,128,256] r7202 c7202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3958
  · exact u3959
  · exact u3960
  · exact u3961

def r7203 : Route 9 := (fun mask => (mask,id))

def c7203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7203 : Upper (D 9) (R 9) [34,65,9,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,384] 13 (by decide) (choices 1) [4,16,64,256] r7203 c7203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3962
  · exact u3963
  · exact u3964
  · exact u3965

def r7204 : Route 9 := (fun mask => (mask,id))

def c7204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7204 : Upper (D 9) (R 9) [34,65,9,192,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,36] 13 (by decide) (choices 1) [16,128,256] r7204 c7204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3966
  · exact u3967
  · exact u3968

def b7205 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 355, targets := 128 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,7),(1,7),(3,0),(4,0),(4,6)], upper := (rows 35 67 13 200 148 304 368 432 304), lower := (rows 35 67 13 200 148 32 64 128 256), losses := [] }

theorem u7205 : Upper (D 9) (R 9) [34,65,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7205 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7206 : Route 9 := (fun mask => (mask,id))

def c7206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7206 : Upper (D 9) (R 9) [34,65,9,192,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,160] 13 (by decide) (choices 1) [4,16,256] r7206 c7206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3969
  · exact u3970
  · exact u3971

def r7207 : Route 9 := (fun mask => (mask,id))

def c7207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7207 : Upper (D 9) (R 9) [34,65,9,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,260] 13 (by decide) (choices 1) [16,128,256] r7207 c7207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3972
  · exact u3973
  · exact u3974

def r7208 : Route 9 := (fun mask => (mask,id))

def c7208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7208 : Upper (D 9) (R 9) [34,65,9,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,288] 13 (by decide) (choices 1) [4,16,128,256] r7208 c7208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3975
  · exact u3976
  · exact u3977
  · exact u3978

def r7209 : Route 9 := (fun mask => (mask,id))

def c7209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7209 : Upper (D 9) (R 9) [34,65,9,192,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,384] 13 (by decide) (choices 1) [4,16,256] r7209 c7209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3979
  · exact u3980
  · exact u3981

def r7210 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7210 : Upper (D 9) (R 9) [34,65,9,384,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,36] 13 (by decide) (choices 1) [16,64,128] r7210 c7210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3982
  · exact u3983
  · exact u3984

def r7211 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7211 : Upper (D 9) (R 9) [34,65,9,384,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,68] 13 (by decide) (choices 1) [16,128] r7211 c7211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3985
  · exact u3986

def b7212 : PairBound 9 := { available := 404, camps := [{ cop := 4, region := 3, targets := 384 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,0)], upper := (rows 35 67 13 392 112 436 468 404 404), lower := (rows 35 67 13 392 112 32 64 128 256), losses := [] }

theorem u7212 : Upper (D 9) (R 9) [34,65,9,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7212 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7213 : Route 9 := (fun mask => (mask,id))

def c7213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7213 : Upper (D 9) (R 9) [34,65,9,384,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,132] 13 (by decide) (choices 1) [16,64,256] r7213 c7213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3987
  · exact u3988
  · exact u3989

def r7214 : Route 9 := (fun mask => (mask,id))

def c7214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7214 : Upper (D 9) (R 9) [34,65,9,384,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,160] 13 (by decide) (choices 1) [4,16,64,256] r7214 c7214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3990
  · exact u3991
  · exact u3992
  · exact u3993

def r7215 : Route 9 := (fun mask => (mask,id))

def c7215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7215 : Upper (D 9) (R 9) [34,65,9,384,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,192] 13 (by decide) (choices 1) [4,16,256] r7215 c7215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3994
  · exact u3995
  · exact u3996

def b7216 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 67 13 392 400 116 116 244 372), lower := (rows 35 67 13 392 400 32 64 128 256), losses := [] }

theorem u7216 : Upper (D 9) (R 9) [34,65,9,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7216 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7217 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 67 28 41 84 416 448 384 384), lower := (rows 35 67 28 41 84 32 64 128 256), losses := [] }

theorem u7217 : Upper (D 9) (R 9) [34,65,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7217 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7218 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 67 28 41 148 480 448 448 448), lower := (rows 35 67 28 41 148 32 64 128 256), losses := [] }

theorem u7218 : Upper (D 9) (R 9) [34,65,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7218 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7219 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 67 28 41 208 420 452 388 388), lower := (rows 35 67 28 41 208 32 64 128 256), losses := [] }

theorem u7219 : Upper (D 9) (R 9) [34,65,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7219 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7220 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 67 28 41 400 484 452 452 452), lower := (rows 35 67 28 41 400 32 64 128 256), losses := [] }

theorem u7220 : Upper (D 9) (R 9) [34,65,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7220 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7221 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 384 },{ cop := 4, region := 428, targets := 1 }], pairs := [(1,5),(2,0),(4,5),(4,7),(4,8)], upper := (rows 35 67 28 44 81 416 448 384 384), lower := (rows 35 67 28 44 81 32 64 128 256), losses := [] }

theorem u7221 : Upper (D 9) (R 9) [34,65,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7221 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7222 : Route 9 := (fun mask => (mask,id))

def c7222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7222 : Upper (D 9) (R 9) [34,65,24,36,129] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,129] 13 (by decide) (choices 1) [64,128,256] r7222 c7222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3997
  · exact u3998
  · exact u3999

def r7223 : Route 9 := (fun mask => (mask,id))

def c7223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7223 : Upper (D 9) (R 9) [34,65,24,36,192] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,192] 13 (by decide) (choices 1) [1,128,256] r7223 c7223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4000
  · exact u4001
  · exact u4002

def r7224 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7224 : Upper (D 9) (R 9) [34,65,24,36,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,384] 13 (by decide) (choices 1) [1,64,128] r7224 c7224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4003
  · exact u4004
  · exact u4005

def b7225 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 8, targets := 416 },{ cop := 3, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7),(3,8)], upper := (rows 35 67 28 73 148 416 480 416 416), lower := (rows 35 67 28 73 148 32 64 128 256), losses := [] }

theorem u7225 : Upper (D 9) (R 9) [34,65,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7225 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7226 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 8, targets := 416 },{ cop := 3, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7),(3,8)], upper := (rows 35 67 28 73 176 420 452 388 388), lower := (rows 35 67 28 73 176 32 64 128 256), losses := [] }

theorem u7226 : Upper (D 9) (R 9) [34,65,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7226 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7227 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 8, targets := 416 },{ cop := 3, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7),(3,8)], upper := (rows 35 67 28 73 400 420 484 420 420), lower := (rows 35 67 28 73 400 32 64 128 256), losses := [] }

theorem u7227 : Upper (D 9) (R 9) [34,65,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7227 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7228 : Route 9 := (fun mask => (mask,id))

def c7228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7228 : Upper (D 9) (R 9) [34,65,24,68,129] 13 := by
  apply FastRouting.sound _ _ [34,65,24,68,129] 13 (by decide) (choices 1) [128,256] r7228 c7228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4006
  · exact u4007

def r7229 : Route 9 := (fun mask => (mask,id))

def c7229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7229 : Upper (D 9) (R 9) [34,65,24,68,160] 13 := by
  apply FastRouting.sound _ _ [34,65,24,68,160] 13 (by decide) (choices 1) [1,128,256] r7229 c7229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4008
  · exact u4009
  · exact u4010

def r7230 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7230 : Upper (D 9) (R 9) [34,65,24,68,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,68,384] 13 (by decide) (choices 1) [1,128] r7230 c7230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4011
  · exact u4012

def b7231 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 3, targets := 384 },{ cop := 4, region := 364, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 28 104 145 420 452 388 388), lower := (rows 35 67 28 104 145 32 64 128 256), losses := [] }

theorem u7231 : Upper (D 9) (R 9) [34,65,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7231 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7232 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 3, targets := 384 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,7),(0,8),(1,5),(1,7),(1,8)], upper := (rows 35 67 28 104 148 417 449 385 385), lower := (rows 35 67 28 104 148 32 64 128 256), losses := [] }

theorem u7232 : Upper (D 9) (R 9) [34,65,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7232 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7233 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7233 : Upper (D 9) (R 9) [34,65,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,384] 13 (by decide) (choices 1) [1,4,128] r7233 c7233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4013
  · exact u4014
  · exact u4015

def b7234 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 20, targets := 352 }], pairs := [(2,5),(2,6),(2,8),(4,5),(4,6)], upper := (rows 35 67 28 137 148 352 352 480 352), lower := (rows 35 67 28 137 148 32 64 128 256), losses := [] }

theorem u7234 : Upper (D 9) (R 9) [34,65,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7234 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7235 : Route 9 := (fun mask => (mask,id))

def c7235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7235 : Upper (D 9) (R 9) [34,65,24,129,160] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,160] 13 (by decide) (choices 1) [4,64,256] r7235 c7235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4016
  · exact u4017
  · exact u4018

def r7236 : Route 9 := (fun mask => (mask,id))

def c7236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7236 : Upper (D 9) (R 9) [34,65,24,129,192] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,192] 13 (by decide) (choices 1) [4,256] r7236 c7236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4019
  · exact u4020

def r7237 : Route 9 := (fun mask => (mask,id))

def c7237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7237 : Upper (D 9) (R 9) [34,65,24,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,260] 13 (by decide) (choices 1) [64,128,256] r7237 c7237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4021
  · exact u4022
  · exact u4023

def r7238 : Route 9 := (fun mask => (mask,id))

def c7238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7238 : Upper (D 9) (R 9) [34,65,24,129,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,288] 13 (by decide) (choices 1) [4,64,128,256] r7238 c7238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4024
  · exact u4025
  · exact u4026
  · exact u4027

def r7239 : Route 9 := (fun mask => (mask,id))

def c7239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7239 : Upper (D 9) (R 9) [34,65,24,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,320] 13 (by decide) (choices 1) [4,128,256] r7239 c7239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4028
  · exact u4029
  · exact u4030

def r7240 : Route 9 := (fun mask => (mask,id))

def c7240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7240 : Upper (D 9) (R 9) [34,65,24,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,384] 13 (by decide) (choices 1) [4,64,256] r7240 c7240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4031
  · exact u4032
  · exact u4033

def b7241 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 12, targets := 353 }], pairs := [(2,0),(2,5),(2,6),(2,8),(3,0)], upper := (rows 35 67 28 140 176 353 321 449 321), lower := (rows 35 67 28 140 176 32 64 128 256), losses := [] }

theorem u7241 : Upper (D 9) (R 9) [34,65,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7241 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7242 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 353 }], pairs := [(2,0),(2,5),(2,6),(2,8),(3,0)], upper := (rows 35 67 28 140 208 289 353 417 289), lower := (rows 35 67 28 140 208 32 64 128 256), losses := [] }

theorem u7242 : Upper (D 9) (R 9) [34,65,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7242 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7243 : Route 9 := (fun mask => (mask,id))

def c7243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7243 : Upper (D 9) (R 9) [34,65,24,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132,288] 13 (by decide) (choices 1) [1,64,128,256] r7243 c7243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4034
  · exact u4035
  · exact u4036
  · exact u4037

def r7244 : Route 9 := (fun mask => (mask,id))

def c7244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7244 : Upper (D 9) (R 9) [34,65,24,132,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132,320] 13 (by decide) (choices 1) [1,128,256] r7244 c7244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4038
  · exact u4039
  · exact u4040

def b7245 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 353 }], pairs := [(2,0),(2,5),(2,6),(2,8),(3,0)], upper := (rows 35 67 28 140 400 353 353 481 353), lower := (rows 35 67 28 140 400 32 64 128 256), losses := [] }

theorem u7245 : Upper (D 9) (R 9) [34,65,24,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7245 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7246 : Route 9 := (fun mask => (mask,id))

def c7246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7246 : Upper (D 9) (R 9) [34,65,24,160,192] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,192] 13 (by decide) (choices 1) [1,4,256] r7246 c7246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4041
  · exact u4042
  · exact u4043

def r7247 : Route 9 := (fun mask => (mask,id))

def c7247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7247 : Upper (D 9) (R 9) [34,65,24,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,320] 13 (by decide) (choices 1) [1,4,128,256] r7247 c7247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4044
  · exact u4045
  · exact u4046
  · exact u4047

def r7248 : Route 9 := (fun mask => (mask,id))

def c7248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7248 : Upper (D 9) (R 9) [34,65,24,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,384] 13 (by decide) (choices 1) [1,4,64,256] r7248 c7248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4048
  · exact u4049
  · exact u4050
  · exact u4051

def r7249 : Route 9 := (fun mask => (mask,id))

def c7249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7249 : Upper (D 9) (R 9) [34,65,24,192,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,384] 13 (by decide) (choices 1) [1,4,256] r7249 c7249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4052
  · exact u4053
  · exact u4054

def b7250 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0),(4,5)], upper := (rows 35 67 28 392 400 101 101 229 357), lower := (rows 35 67 28 392 400 32 64 128 256), losses := [] }

theorem u7250 : Upper (D 9) (R 9) [34,65,24,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7250 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7251 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 76 152 432 464 400 400), lower := (rows 35 67 37 76 152 32 64 128 256), losses := [] }

theorem u7251 : Upper (D 9) (R 9) [34,65,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7251 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7252 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 76 400 440 472 408 408), lower := (rows 35 67 37 76 400 32 64 128 256), losses := [] }

theorem u7252 : Upper (D 9) (R 9) [34,65,33,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7252 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7253 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 88 148 424 456 392 392), lower := (rows 35 67 37 88 148 32 64 128 256), losses := [] }

theorem u7253 : Upper (D 9) (R 9) [34,65,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7253 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7254 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 67 37 88 152 420 452 388 388), lower := (rows 35 67 37 88 152 32 64 128 256), losses := [] }

theorem u7254 : Upper (D 9) (R 9) [34,65,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7254 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7255 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 88 400 428 460 396 396), lower := (rows 35 67 37 88 400 32 64 128 256), losses := [] }

theorem u7255 : Upper (D 9) (R 9) [34,65,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7255 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7256 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 140 208 312 344 408 280), lower := (rows 35 67 37 140 208 32 64 128 256), losses := [] }

theorem u7256 : Upper (D 9) (R 9) [34,65,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7256 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7257 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 140 280 496 464 464 464), lower := (rows 35 67 37 140 280 32 64 128 256), losses := [] }

theorem u7257 : Upper (D 9) (R 9) [34,65,33,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7257 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7258 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 140 336 440 472 408 408), lower := (rows 35 67 37 140 336 32 64 128 256), losses := [] }

theorem u7258 : Upper (D 9) (R 9) [34,65,33,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7258 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7259 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 140 400 376 344 472 344), lower := (rows 35 67 37 140 400 32 64 128 256), losses := [] }

theorem u7259 : Upper (D 9) (R 9) [34,65,33,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7259 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u7259
end Delivery.IrregularNine14.P09
