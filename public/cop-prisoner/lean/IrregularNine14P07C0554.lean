import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0284
import IrregularNine14P07C0285
import IrregularNine14P07C0286

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33240 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 16, targets := 2 },{ cop := 1, region := 16, targets := 128 }], pairs := [(1,0),(4,0),(4,1),(4,7)], upper := (rows 13 98 133 265 112 178 210 146 402), lower := (rows 13 98 133 265 112 32 64 128 256), losses := [] }

theorem u33240 : Upper (D 7) (R 7) [12,96,129,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33241 : Route 9 := (fun mask => (mask,id))

def c33241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33241 : Upper (D 7) (R 7) [12,96,129,257,130] 13 := by
  apply FastRouting.sound _ _ [12,96,129,257,130] 13 (by decide) (choices 1) [2,16,64] r33241 c33241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17052
  · exact u17053
  · exact u17054

def r33242 : Route 9 := (fun mask => (mask,id))

def c33242 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33242 : Upper (D 7) (R 7) [12,96,129,257,160] 13 := by
  apply FastRouting.sound _ _ [12,96,129,257,160] 13 (by decide) (choices 1) [2,16,64] r33242 c33242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17055
  · exact u17056
  · exact u17057

def r33243 : Route 9 := (fun mask => (mask,id))

def c33243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33243 : Upper (D 7) (R 7) [12,96,129,258,3] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258,3] 13 (by decide) (choices 1) [16,64,128] r33243 c33243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17058
  · exact u17059
  · exact u17060

def r33244 : Route 9 := (fun mask => (mask,id))

def c33244 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33244 : Upper (D 7) (R 7) [12,96,129,258,33] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258,33] 13 (by decide) (choices 1) [2,16,64,128] r33244 c33244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17061
  · exact u17062
  · exact u17063
  · exact u17064

def b33245 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 133 266 50 241 209 209 465), lower := (rows 13 98 133 266 50 32 64 128 256), losses := [] }

theorem u33245 : Upper (D 7) (R 7) [12,96,129,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33246 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 133 266 112 179 211 147 403), lower := (rows 13 98 133 266 112 32 64 128 256), losses := [] }

theorem u33246 : Upper (D 7) (R 7) [12,96,129,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33247 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 13 98 133 266 145 114 114 242 370), lower := (rows 13 98 133 266 145 32 64 128 256), losses := [] }

theorem u33247 : Upper (D 7) (R 7) [12,96,129,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33248 : Route 9 := (fun mask => (mask,id))

def c33248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33248 : Upper (D 7) (R 7) [12,96,129,258,130] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258,130] 13 (by decide) (choices 1) [1,16,64] r33248 c33248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17065
  · exact u17066
  · exact u17067

def r33249 : Route 9 := (fun mask => (mask,id))

def c33249 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33249 : Upper (D 7) (R 7) [12,96,129,258,160] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258,160] 13 (by decide) (choices 1) [1,2,16,64] r33249 c33249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17068
  · exact u17069
  · exact u17070
  · exact u17071

def r33250 : Route 9 := (fun mask => (mask,id))

def c33250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33250 : Upper (D 7) (R 7) [12,96,129,272,3] 13 := by
  apply FastRouting.sound _ _ [12,96,129,272,3] 13 (by decide) (choices 1) [2,64,128] r33250 c33250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17072
  · exact u17073
  · exact u17074

def r33251 : Route 9 := (fun mask => (mask,id))

def c33251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33251 : Upper (D 7) (R 7) [12,96,129,272,33] 13 := by
  apply FastRouting.sound _ _ [12,96,129,272,33] 13 (by decide) (choices 1) [2,64,128] r33251 c33251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17075
  · exact u17076
  · exact u17077

def b33252 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 133 280 50 227 195 195 451), lower := (rows 13 98 133 280 50 32 64 128 256), losses := [] }

theorem u33252 : Upper (D 7) (R 7) [12,96,129,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33253 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 133 280 112 163 195 131 387), lower := (rows 13 98 133 280 112 32 64 128 256), losses := [] }

theorem u33253 : Upper (D 7) (R 7) [12,96,129,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33254 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 13 98 133 280 145 98 98 226 354), lower := (rows 13 98 133 280 145 32 64 128 256), losses := [] }

theorem u33254 : Upper (D 7) (R 7) [12,96,129,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33255 : Route 9 := (fun mask => (mask,id))

def c33255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33255 : Upper (D 7) (R 7) [12,96,129,272,130] 13 := by
  apply FastRouting.sound _ _ [12,96,129,272,130] 13 (by decide) (choices 1) [1,2,64] r33255 c33255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17078
  · exact u17079
  · exact u17080

def r33256 : Route 9 := (fun mask => (mask,id))

def c33256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33256 : Upper (D 7) (R 7) [12,96,129,272,160] 13 := by
  apply FastRouting.sound _ _ [12,96,129,272,160] 13 (by decide) (choices 1) [1,2,64] r33256 c33256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17081
  · exact u17082
  · exact u17083

def r33257 : Route 9 := (fun mask => (mask,id))

def c33257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33257 : Upper (D 7) (R 7) [12,96,129,288,3] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,3] 13 (by decide) (choices 1) [2,16,64,128] r33257 c33257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17084
  · exact u17085
  · exact u17086
  · exact u17087

def r33258 : Route 9 := (fun mask => (mask,id))

def c33258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33258 : Upper (D 7) (R 7) [12,96,129,288,65] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,65] 13 (by decide) (choices 1) [2,16,128] r33258 c33258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17088
  · exact u17089
  · exact u17090

def b33259 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 133 296 82 179 211 147 403), lower := (rows 13 98 133 296 82 32 64 128 256), losses := [] }

theorem u33259 : Upper (D 7) (R 7) [12,96,129,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33260 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 13 98 133 296 145 114 82 210 338), lower := (rows 13 98 133 296 145 32 64 128 256), losses := [] }

theorem u33260 : Upper (D 7) (R 7) [12,96,129,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33261 : Route 9 := (fun mask => (mask,id))

def c33261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33261 : Upper (D 7) (R 7) [12,96,129,288,130] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,130] 13 (by decide) (choices 1) [1,2,16,64] r33261 c33261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17091
  · exact u17092
  · exact u17093
  · exact u17094

def r33262 : Route 9 := (fun mask => (mask,id))

def c33262 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33262 : Upper (D 7) (R 7) [12,96,129,288,192] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288,192] 13 (by decide) (choices 1) [1,2,16] r33262 c33262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17095
  · exact u17096
  · exact u17097

def b33263 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 98 134 152 19 353 353 481 353), lower := (rows 13 98 134 152 19 32 64 128 256), losses := [] }

theorem u33263 : Upper (D 7) (R 7) [12,96,130,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33264 : Route 9 := (fun mask => (mask,id))

def c33264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33264 : Upper (D 7) (R 7) [12,96,130,144,33] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,33] 13 (by decide) (choices 1) [1,2,64,256] r33264 c33264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17098
  · exact u17099
  · exact u17100
  · exact u17101

def b33265 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 134 152 50 353 321 449 321), lower := (rows 13 98 134 152 50 32 64 128 256), losses := [] }

theorem u33265 : Upper (D 7) (R 7) [12,96,130,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33266 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,7),(4,0),(4,1),(4,7)], upper := (rows 13 98 134 152 112 291 323 387 259), lower := (rows 13 98 134 152 112 32 64 128 256), losses := [] }

theorem u33266 : Upper (D 7) (R 7) [12,96,130,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33267 : Route 9 := (fun mask => (mask,id))

def c33267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33267 : Upper (D 7) (R 7) [12,96,130,144,257] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,257] 13 (by decide) (choices 1) [1,2,64] r33267 c33267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17102
  · exact u17103
  · exact u17104

def r33268 : Route 9 := (fun mask => (mask,id))

def c33268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33268 : Upper (D 7) (R 7) [12,96,130,144,258] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,258] 13 (by decide) (choices 1) [1,64] r33268 c33268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17105
  · exact u17106

def r33269 : Route 9 := (fun mask => (mask,id))

def c33269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33269 : Upper (D 7) (R 7) [12,96,130,144,288] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144,288] 13 (by decide) (choices 1) [1,2,64] r33269 c33269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17107
  · exact u17108
  · exact u17109

def b33270 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 4, region := 488, targets := 2 },{ cop := 4, region := 452, targets := 32 }], pairs := [(1,7),(2,5),(3,1),(4,7)], upper := (rows 13 98 134 168 19 369 337 465 337), lower := (rows 13 98 134 168 19 32 64 128 256), losses := [] }

theorem u33270 : Upper (D 7) (R 7) [12,96,130,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33271 : Route 9 := (fun mask => (mask,id))

def c33271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33271 : Upper (D 7) (R 7) [12,96,130,160,65] 13 := by
  apply FastRouting.sound _ _ [12,96,130,160,65] 13 (by decide) (choices 1) [1,2,16,256] r33271 c33271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17110
  · exact u17111
  · exact u17112
  · exact u17113

def b33272 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 134 168 82 305 337 401 273), lower := (rows 13 98 134 168 82 32 64 128 256), losses := [] }

theorem u33272 : Upper (D 7) (R 7) [12,96,130,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33273 : Route 9 := (fun mask => (mask,id))

def c33273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33273 : Upper (D 7) (R 7) [12,96,130,160,257] 13 := by
  apply FastRouting.sound _ _ [12,96,130,160,257] 13 (by decide) (choices 1) [1,2,16,64] r33273 c33273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17114
  · exact u17115
  · exact u17116
  · exact u17117

def r33274 : Route 9 := (fun mask => (mask,id))

def c33274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33274 : Upper (D 7) (R 7) [12,96,130,160,258] 13 := by
  apply FastRouting.sound _ _ [12,96,130,160,258] 13 (by decide) (choices 1) [1,16,64] r33274 c33274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17118
  · exact u17119
  · exact u17120

def r33275 : Route 9 := (fun mask => (mask,id))

def c33275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33275 : Upper (D 7) (R 7) [12,96,130,160,320] 13 := by
  apply FastRouting.sound _ _ [12,96,130,160,320] 13 (by decide) (choices 1) [1,2,16] r33275 c33275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17121
  · exact u17122
  · exact u17123

def r33276 : Route 9 := (fun mask => (mask,id))

def c33276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33276 : Upper (D 7) (R 7) [12,96,130,257,3] 13 := by
  apply FastRouting.sound _ _ [12,96,130,257,3] 13 (by decide) (choices 1) [16,64,128] r33276 c33276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17124
  · exact u17125
  · exact u17126

def r33277 : Route 9 := (fun mask => (mask,id))

def c33277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33277 : Upper (D 7) (R 7) [12,96,130,257,33] 13 := by
  apply FastRouting.sound _ _ [12,96,130,257,33] 13 (by decide) (choices 1) [2,16,64,128] r33277 c33277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17127
  · exact u17128
  · exact u17129
  · exact u17130

def b33278 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 134 265 50 241 209 209 465), lower := (rows 13 98 134 265 50 32 64 128 256), losses := [] }

theorem u33278 : Upper (D 7) (R 7) [12,96,130,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33279 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 134 265 112 179 211 147 403), lower := (rows 13 98 134 265 112 32 64 128 256), losses := [] }

theorem u33279 : Upper (D 7) (R 7) [12,96,130,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33280 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 134 265 145 114 114 242 370), lower := (rows 13 98 134 265 145 32 64 128 256), losses := [] }

theorem u33280 : Upper (D 7) (R 7) [12,96,130,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33281 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 13 98 134 265 146 113 113 241 369), lower := (rows 13 98 134 265 146 32 64 128 256), losses := [] }

theorem u33281 : Upper (D 7) (R 7) [12,96,130,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33282 : Route 9 := (fun mask => (mask,id))

def c33282 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33282 : Upper (D 7) (R 7) [12,96,130,257,160] 13 := by
  apply FastRouting.sound _ _ [12,96,130,257,160] 13 (by decide) (choices 1) [1,2,16,64] r33282 c33282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17131
  · exact u17132
  · exact u17133
  · exact u17134

def r33283 : Route 9 := (fun mask => (mask,id))

def c33283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33283 : Upper (D 7) (R 7) [12,96,130,258,33] 13 := by
  apply FastRouting.sound _ _ [12,96,130,258,33] 13 (by decide) (choices 1) [1,16,64,128] r33283 c33283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17135
  · exact u17136
  · exact u17137
  · exact u17138

def b33284 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 134 266 112 177 209 145 401), lower := (rows 13 98 134 266 112 32 64 128 256), losses := [] }

theorem u33284 : Upper (D 7) (R 7) [12,96,130,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33285 : Route 9 := (fun mask => (mask,id))

def c33285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33285 : Upper (D 7) (R 7) [12,96,130,258,129] 13 := by
  apply FastRouting.sound _ _ [12,96,130,258,129] 13 (by decide) (choices 1) [1,16,64] r33285 c33285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17139
  · exact u17140
  · exact u17141

def r33286 : Route 9 := (fun mask => (mask,id))

def c33286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33286 : Upper (D 7) (R 7) [12,96,130,258,160] 13 := by
  apply FastRouting.sound _ _ [12,96,130,258,160] 13 (by decide) (choices 1) [1,16,64] r33286 c33286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17142
  · exact u17143
  · exact u17144

def r33287 : Route 9 := (fun mask => (mask,id))

def c33287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33287 : Upper (D 7) (R 7) [12,96,130,272,3] 13 := by
  apply FastRouting.sound _ _ [12,96,130,272,3] 13 (by decide) (choices 1) [1,64,128] r33287 c33287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17145
  · exact u17146
  · exact u17147

def r33288 : Route 9 := (fun mask => (mask,id))

def c33288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33288 : Upper (D 7) (R 7) [12,96,130,272,33] 13 := by
  apply FastRouting.sound _ _ [12,96,130,272,33] 13 (by decide) (choices 1) [1,2,64,128] r33288 c33288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17148
  · exact u17149
  · exact u17150
  · exact u17151

def b33289 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 134 280 50 225 193 193 449), lower := (rows 13 98 134 280 50 32 64 128 256), losses := [] }

theorem u33289 : Upper (D 7) (R 7) [12,96,130,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33290 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 134 280 112 163 195 131 387), lower := (rows 13 98 134 280 112 32 64 128 256), losses := [] }

theorem u33290 : Upper (D 7) (R 7) [12,96,130,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33291 : Route 9 := (fun mask => (mask,id))

def c33291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33291 : Upper (D 7) (R 7) [12,96,130,272,129] 13 := by
  apply FastRouting.sound _ _ [12,96,130,272,129] 13 (by decide) (choices 1) [1,2,64] r33291 c33291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17152
  · exact u17153
  · exact u17154

def b33292 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 13 98 134 280 146 97 97 225 353), lower := (rows 13 98 134 280 146 32 64 128 256), losses := [] }

theorem u33292 : Upper (D 7) (R 7) [12,96,130,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33293 : Route 9 := (fun mask => (mask,id))

def c33293 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33293 : Upper (D 7) (R 7) [12,96,130,272,160] 13 := by
  apply FastRouting.sound _ _ [12,96,130,272,160] 13 (by decide) (choices 1) [1,2,64] r33293 c33293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17155
  · exact u17156
  · exact u17157

def r33294 : Route 9 := (fun mask => (mask,id))

def c33294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33294 : Upper (D 7) (R 7) [12,96,130,288,3] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,3] 13 (by decide) (choices 1) [1,16,64,128] r33294 c33294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17158
  · exact u17159
  · exact u17160
  · exact u17161

def r33295 : Route 9 := (fun mask => (mask,id))

def c33295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33295 : Upper (D 7) (R 7) [12,96,130,288,65] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,65] 13 (by decide) (choices 1) [1,2,16,128] r33295 c33295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17162
  · exact u17163
  · exact u17164
  · exact u17165

def b33296 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 134 296 82 177 209 145 401), lower := (rows 13 98 134 296 82 32 64 128 256), losses := [] }

theorem u33296 : Upper (D 7) (R 7) [12,96,130,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33297 : Route 9 := (fun mask => (mask,id))

def c33297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33297 : Upper (D 7) (R 7) [12,96,130,288,129] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,129] 13 (by decide) (choices 1) [1,2,16,64] r33297 c33297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17166
  · exact u17167
  · exact u17168
  · exact u17169

def b33298 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 13 98 134 296 146 113 81 209 337), lower := (rows 13 98 134 296 146 32 64 128 256), losses := [] }

theorem u33298 : Upper (D 7) (R 7) [12,96,130,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33299 : Route 9 := (fun mask => (mask,id))

def c33299 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33299 : Upper (D 7) (R 7) [12,96,130,288,192] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,192] 13 (by decide) (choices 1) [1,2,16] r33299 c33299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17170
  · exact u17171
  · exact u17172

#print axioms u33299
end Delivery.IrregularNine14.P07
