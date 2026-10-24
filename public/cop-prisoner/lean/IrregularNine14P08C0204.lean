import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0066
import IrregularNine14P08C0067

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12240 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 28 140 208 33 97 161 289), lower := (rows 67 290 28 140 208 32 64 128 256), losses := [] }

theorem u12240 : Upper (D 8) (R 8) [66,288,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12241 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 28 168 176 101 69 197 325), lower := (rows 67 290 28 168 176 32 64 128 256), losses := [] }

theorem u12241 : Upper (D 8) (R 8) [66,288,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12242 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 168 208 37 101 165 293), lower := (rows 67 290 28 168 208 32 64 128 256), losses := [] }

theorem u12242 : Upper (D 8) (R 8) [66,288,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12243 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 290 37 41 84 184 216 152 408), lower := (rows 67 290 37 41 84 32 64 128 256), losses := [] }

theorem u12243 : Upper (D 8) (R 8) [66,288,33,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12244 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 290 37 41 148 248 216 216 472), lower := (rows 67 290 37 41 148 32 64 128 256), losses := [] }

theorem u12244 : Upper (D 8) (R 8) [66,288,33,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12245 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 290 37 41 208 188 220 156 412), lower := (rows 67 290 37 41 208 32 64 128 256), losses := [] }

theorem u12245 : Upper (D 8) (R 8) [66,288,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12246 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 37 44 88 177 209 145 401), lower := (rows 67 290 37 44 88 32 64 128 256), losses := [] }

theorem u12246 : Upper (D 8) (R 8) [66,288,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12247 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 37 44 145 248 216 216 472), lower := (rows 67 290 37 44 145 32 64 128 256), losses := [] }

theorem u12247 : Upper (D 8) (R 8) [66,288,33,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12248 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 37 44 152 241 209 209 465), lower := (rows 67 290 37 44 152 32 64 128 256), losses := [] }

theorem u12248 : Upper (D 8) (R 8) [66,288,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12249 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 37 44 208 185 217 153 409), lower := (rows 67 290 37 44 208 32 64 128 256), losses := [] }

theorem u12249 : Upper (D 8) (R 8) [66,288,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12250 : PairBound 9 := { available := 140, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 56 81 172 204 140 396), lower := (rows 67 290 37 56 81 32 64 128 256), losses := [] }

theorem u12250 : Upper (D 8) (R 8) [66,288,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12251 : Route 9 := (fun mask => (mask,id))

def c12251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12251 : Upper (D 8) (R 8) [66,288,33,48,68] 13 := by
  apply FastRouting.sound _ _ [66,288,33,48,68] 13 (by decide) (choices 1) [1,8,128] r12251 c12251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3974
  · exact u3975
  · exact u3976

def b12252 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 56 88 165 197 133 389), lower := (rows 67 290 37 56 88 32 64 128 256), losses := [] }

theorem u12252 : Upper (D 8) (R 8) [66,288,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12253 : Route 9 := (fun mask => (mask,id))

def c12253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12253 : Upper (D 8) (R 8) [66,288,33,48,129] 13 := by
  apply FastRouting.sound _ _ [66,288,33,48,129] 13 (by decide) (choices 1) [4,8,64,128] r12253 c12253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3977
  · exact u3978
  · exact u3979
  · exact u3980

def r12254 : Route 9 := (fun mask => (mask,id))

def c12254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12254 : Upper (D 8) (R 8) [66,288,33,48,132] 13 := by
  apply FastRouting.sound _ _ [66,288,33,48,132] 13 (by decide) (choices 1) [1,8,64,128] r12254 c12254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3981
  · exact u3982
  · exact u3983
  · exact u3984

def r12255 : Route 9 := (fun mask => (mask,id))

def c12255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12255 : Upper (D 8) (R 8) [66,288,33,48,136] 13 := by
  apply FastRouting.sound _ _ [66,288,33,48,136] 13 (by decide) (choices 1) [1,4,64,128] r12255 c12255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3985
  · exact u3986
  · exact u3987
  · exact u3988

def r12256 : Route 9 := (fun mask => (mask,id))

def c12256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12256 : Upper (D 8) (R 8) [66,288,33,48,192] 13 := by
  apply FastRouting.sound _ _ [66,288,33,48,192] 13 (by decide) (choices 1) [1,4,8,128] r12256 c12256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3989
  · exact u3990
  · exact u3991
  · exact u3992

def b12257 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 73 148 184 248 184 440), lower := (rows 67 290 37 73 148 32 64 128 256), losses := [] }

theorem u12257 : Upper (D 8) (R 8) [66,288,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12258 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 73 152 180 244 180 436), lower := (rows 67 290 37 73 152 32 64 128 256), losses := [] }

theorem u12258 : Upper (D 8) (R 8) [66,288,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12259 : PairBound 9 := { available := 156, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 73 176 188 220 156 412), lower := (rows 67 290 37 73 176 32 64 128 256), losses := [] }

theorem u12259 : Upper (D 8) (R 8) [66,288,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12260 : Route 9 := (fun mask => (mask,id))

def c12260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12260 : Upper (D 8) (R 8) [66,288,33,68,129] 13 := by
  apply FastRouting.sound _ _ [66,288,33,68,129] 13 (by decide) (choices 1) [8,16,128] r12260 c12260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3993
  · exact u3994
  · exact u3995

def r12261 : Route 9 := (fun mask => (mask,id))

def c12261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12261 : Upper (D 8) (R 8) [66,288,33,68,136] 13 := by
  apply FastRouting.sound _ _ [66,288,33,68,136] 13 (by decide) (choices 1) [1,16,128] r12261 c12261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3996
  · exact u3997
  · exact u3998

def r12262 : Route 9 := (fun mask => (mask,id))

def c12262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12262 : Upper (D 8) (R 8) [66,288,33,68,160] 13 := by
  apply FastRouting.sound _ _ [66,288,33,68,160] 13 (by decide) (choices 1) [1,8,16,128] r12262 c12262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3999
  · exact u4000
  · exact u4001
  · exact u4002

def r12263 : Route 9 := (fun mask => (mask,id))

def c12263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12263 : Upper (D 8) (R 8) [66,288,33,80,129] 13 := by
  apply FastRouting.sound _ _ [66,288,33,80,129] 13 (by decide) (choices 1) [4,8,128] r12263 c12263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4003
  · exact u4004
  · exact u4005

def r12264 : Route 9 := (fun mask => (mask,id))

def c12264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12264 : Upper (D 8) (R 8) [66,288,33,80,132] 13 := by
  apply FastRouting.sound _ _ [66,288,33,80,132] 13 (by decide) (choices 1) [1,8,128] r12264 c12264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4006
  · exact u4007
  · exact u4008

def b12265 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 88 152 165 229 165 421), lower := (rows 67 290 37 88 152 32 64 128 256), losses := [] }

theorem u12265 : Upper (D 8) (R 8) [66,288,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12266 : Route 9 := (fun mask => (mask,id))

def c12266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12266 : Upper (D 8) (R 8) [66,288,33,80,160] 13 := by
  apply FastRouting.sound _ _ [66,288,33,80,160] 13 (by decide) (choices 1) [1,4,8,128] r12266 c12266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4009
  · exact u4010
  · exact u4011
  · exact u4012

def r12267 : Route 9 := (fun mask => (mask,id))

def c12267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12267 : Upper (D 8) (R 8) [66,288,33,96,129] 13 := by
  apply FastRouting.sound _ _ [66,288,33,96,129] 13 (by decide) (choices 1) [4,8,16,128] r12267 c12267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4013
  · exact u4014
  · exact u4015
  · exact u4016

def r12268 : Route 9 := (fun mask => (mask,id))

def c12268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12268 : Upper (D 8) (R 8) [66,288,33,96,132] 13 := by
  apply FastRouting.sound _ _ [66,288,33,96,132] 13 (by decide) (choices 1) [1,8,16,128] r12268 c12268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4017
  · exact u4018
  · exact u4019
  · exact u4020

def r12269 : Route 9 := (fun mask => (mask,id))

def c12269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12269 : Upper (D 8) (R 8) [66,288,33,96,136] 13 := by
  apply FastRouting.sound _ _ [66,288,33,96,136] 13 (by decide) (choices 1) [1,4,16,128] r12269 c12269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4021
  · exact u4022
  · exact u4023
  · exact u4024

def r12270 : Route 9 := (fun mask => (mask,id))

def c12270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12270 : Upper (D 8) (R 8) [66,288,33,129,132] 13 := by
  apply FastRouting.sound _ _ [66,288,33,129,132] 13 (by decide) (choices 1) [8,16,64] r12270 c12270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4025
  · exact u4026
  · exact u4027

def b12271 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 290 37 137 152 116 116 244 372), lower := (rows 67 290 37 137 152 32 64 128 256), losses := [] }

theorem u12271 : Upper (D 8) (R 8) [66,288,33,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12272 : Route 9 := (fun mask => (mask,id))

def c12272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12272 : Upper (D 8) (R 8) [66,288,33,129,160] 13 := by
  apply FastRouting.sound _ _ [66,288,33,129,160] 13 (by decide) (choices 1) [4,8,16,64] r12272 c12272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4028
  · exact u4029
  · exact u4030
  · exact u4031

def r12273 : Route 9 := (fun mask => (mask,id))

def c12273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12273 : Upper (D 8) (R 8) [66,288,33,129,192] 13 := by
  apply FastRouting.sound _ _ [66,288,33,129,192] 13 (by decide) (choices 1) [4,8,16] r12273 c12273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4032
  · exact u4033
  · exact u4034

def b12274 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 290 37 140 152 113 113 241 369), lower := (rows 67 290 37 140 152 32 64 128 256), losses := [] }

theorem u12274 : Upper (D 8) (R 8) [66,288,33,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12275 : Route 9 := (fun mask => (mask,id))

def c12275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12275 : Upper (D 8) (R 8) [66,288,33,132,160] 13 := by
  apply FastRouting.sound _ _ [66,288,33,132,160] 13 (by decide) (choices 1) [1,8,16,64] r12275 c12275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4035
  · exact u4036
  · exact u4037
  · exact u4038

def r12276 : Route 9 := (fun mask => (mask,id))

def c12276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12276 : Upper (D 8) (R 8) [66,288,33,132,192] 13 := by
  apply FastRouting.sound _ _ [66,288,33,132,192] 13 (by decide) (choices 1) [1,8,16] r12276 c12276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4039
  · exact u4040
  · exact u4041

def b12277 : PairBound 9 := { available := 101, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 37 152 152 101 101 229 357), lower := (rows 67 290 37 152 152 32 64 128 256), losses := [] }

theorem u12277 : Upper (D 8) (R 8) [66,288,33,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12278 : PairBound 9 := { available := 77, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 152 176 109 77 205 333), lower := (rows 67 290 37 152 176 32 64 128 256), losses := [] }

theorem u12278 : Upper (D 8) (R 8) [66,288,33,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12279 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 152 208 45 109 173 301), lower := (rows 67 290 37 152 208 32 64 128 256), losses := [] }

theorem u12279 : Upper (D 8) (R 8) [66,288,33,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12280 : Route 9 := (fun mask => (mask,id))

def c12280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12280 : Upper (D 8) (R 8) [66,288,33,160,192] 13 := by
  apply FastRouting.sound _ _ [66,288,33,160,192] 13 (by decide) (choices 1) [1,4,8,16] r12280 c12280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4042
  · exact u4043
  · exact u4044
  · exact u4045

def b12281 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 44 145 241 209 209 465), lower := (rows 67 290 44 44 145 32 64 128 256), losses := [] }

theorem u12281 : Upper (D 8) (R 8) [66,288,40,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12282 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 44 208 177 209 145 401), lower := (rows 67 290 44 44 208 32 64 128 256), losses := [] }

theorem u12282 : Upper (D 8) (R 8) [66,288,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12283 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 56 84 161 193 129 385), lower := (rows 67 290 44 56 84 32 64 128 256), losses := [] }

theorem u12283 : Upper (D 8) (R 8) [66,288,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12284 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 56 145 229 197 197 453), lower := (rows 67 290 44 56 145 32 64 128 256), losses := [] }

theorem u12284 : Upper (D 8) (R 8) [66,288,40,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12285 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 56 148 225 193 193 449), lower := (rows 67 290 44 56 148 32 64 128 256), losses := [] }

theorem u12285 : Upper (D 8) (R 8) [66,288,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12286 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 56 208 165 197 133 389), lower := (rows 67 290 44 56 208 32 64 128 256), losses := [] }

theorem u12286 : Upper (D 8) (R 8) [66,288,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12287 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 73 145 180 244 180 436), lower := (rows 67 290 44 73 145 32 64 128 256), losses := [] }

theorem u12287 : Upper (D 8) (R 8) [66,288,40,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12288 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 73 148 177 241 177 433), lower := (rows 67 290 44 73 148 32 64 128 256), losses := [] }

theorem u12288 : Upper (D 8) (R 8) [66,288,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12289 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 73 176 181 213 149 405), lower := (rows 67 290 44 73 176 32 64 128 256), losses := [] }

theorem u12289 : Upper (D 8) (R 8) [66,288,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12290 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 76 145 177 241 177 433), lower := (rows 67 290 44 76 145 32 64 128 256), losses := [] }

theorem u12290 : Upper (D 8) (R 8) [66,288,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12291 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 76 176 177 209 145 401), lower := (rows 67 290 44 76 176 32 64 128 256), losses := [] }

theorem u12291 : Upper (D 8) (R 8) [66,288,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12292 : Route 9 := (fun mask => (mask,id))

def c12292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12292 : Upper (D 8) (R 8) [66,288,40,80,129] 13 := by
  apply FastRouting.sound _ _ [66,288,40,80,129] 13 (by decide) (choices 1) [1,4,128] r12292 c12292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4046
  · exact u4047
  · exact u4048

def b12293 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 88 148 161 225 161 417), lower := (rows 67 290 44 88 148 32 64 128 256), losses := [] }

theorem u12293 : Upper (D 8) (R 8) [66,288,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12294 : Route 9 := (fun mask => (mask,id))

def c12294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12294 : Upper (D 8) (R 8) [66,288,40,80,160] 13 := by
  apply FastRouting.sound _ _ [66,288,40,80,160] 13 (by decide) (choices 1) [1,4,128] r12294 c12294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4049
  · exact u4050
  · exact u4051

def b12295 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 104 145 181 213 149 405), lower := (rows 67 290 44 104 145 32 64 128 256), losses := [] }

theorem u12295 : Upper (D 8) (R 8) [66,288,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12296 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 104 148 177 209 145 401), lower := (rows 67 290 44 104 148 32 64 128 256), losses := [] }

theorem u12296 : Upper (D 8) (R 8) [66,288,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12297 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 137 81 180 244 180 436), lower := (rows 67 290 44 137 81 32 64 128 256), losses := [] }

theorem u12297 : Upper (D 8) (R 8) [66,288,40,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12298 : Route 9 := (fun mask => (mask,id))

def c12298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12298 : Upper (D 8) (R 8) [66,288,40,129,68] 13 := by
  apply FastRouting.sound _ _ [66,288,40,129,68] 13 (by decide) (choices 1) [1,16,128] r12298 c12298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4052
  · exact u4053
  · exact u4054

def r12299 : Route 9 := (fun mask => (mask,id))

def c12299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12299 : Upper (D 8) (R 8) [66,288,40,129,96] 13 := by
  apply FastRouting.sound _ _ [66,288,40,129,96] 13 (by decide) (choices 1) [1,4,16,128] r12299 c12299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4055
  · exact u4056
  · exact u4057
  · exact u4058

#print axioms u12299
end Delivery.IrregularNine14.P08
