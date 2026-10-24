import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0071

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13140 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 200 274 56 120 184 312), lower := (rows 97 7 133 200 274 32 64 128 256), losses := [] }

theorem u13140 : Upper (D 8) (R 8) [96,5,129,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13141 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 200 280 50 114 178 306), lower := (rows 97 7 133 200 280 32 64 128 256), losses := [] }

theorem u13141 : Upper (D 8) (R 8) [96,5,129,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13142 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 200 304 58 122 186 314), lower := (rows 97 7 133 200 304 32 64 128 256), losses := [] }

theorem u13142 : Upper (D 8) (R 8) [96,5,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13143 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 25 176 360 360 488 360), lower := (rows 97 7 134 25 176 32 64 128 256), losses := [] }

theorem u13143 : Upper (D 8) (R 8) [96,5,130,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13144 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 134 25 280 224 224 224 480), lower := (rows 97 7 134 25 280 32 64 128 256), losses := [] }

theorem u13144 : Upper (D 8) (R 8) [96,5,130,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13145 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 134 25 304 232 232 232 488), lower := (rows 97 7 134 25 304 32 64 128 256), losses := [] }

theorem u13145 : Upper (D 8) (R 8) [96,5,130,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13146 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 25 336 168 232 168 424), lower := (rows 97 7 134 25 336 32 64 128 256), losses := [] }

theorem u13146 : Upper (D 8) (R 8) [96,5,130,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13147 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 25 400 104 104 232 360), lower := (rows 97 7 134 25 400 32 64 128 256), losses := [] }

theorem u13147 : Upper (D 8) (R 8) [96,5,130,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13148 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 134 41 56 496 464 464 464), lower := (rows 97 7 134 41 56 32 64 128 256), losses := [] }

theorem u13148 : Upper (D 8) (R 8) [96,5,130,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13149 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 8, targets := 128 }], pairs := [(3,7)], upper := (rows 97 7 134 41 88 432 496 432 432), lower := (rows 97 7 134 41 88 32 64 128 256), losses := [] }

theorem u13149 : Upper (D 8) (R 8) [96,5,130,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13150 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 134 41 280 240 240 240 496), lower := (rows 97 7 134 41 280 32 64 128 256), losses := [] }

theorem u13150 : Upper (D 8) (R 8) [96,5,130,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13151 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 134 41 304 248 216 216 472), lower := (rows 97 7 134 41 304 32 64 128 256), losses := [] }

theorem u13151 : Upper (D 8) (R 8) [96,5,130,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13152 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 134 41 336 184 248 184 440), lower := (rows 97 7 134 41 336 32 64 128 256), losses := [] }

theorem u13152 : Upper (D 8) (R 8) [96,5,130,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13153 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 56 481 449 449 449), lower := (rows 97 7 134 56 56 32 64 128 256), losses := [] }

theorem u13153 : Upper (D 8) (R 8) [96,5,130,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13154 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 56 81 424 488 424 424), lower := (rows 97 7 134 56 81 32 64 128 256), losses := [] }

theorem u13154 : Upper (D 8) (R 8) [96,5,130,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13155 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 88 417 481 417 417), lower := (rows 97 7 134 56 88 32 64 128 256), losses := [] }

theorem u13155 : Upper (D 8) (R 8) [96,5,130,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13156 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 112 425 457 393 393), lower := (rows 97 7 134 56 112 32 64 128 256), losses := [] }

theorem u13156 : Upper (D 8) (R 8) [96,5,130,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13157 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 56 145 360 360 488 360), lower := (rows 97 7 134 56 145 32 64 128 256), losses := [] }

theorem u13157 : Upper (D 8) (R 8) [96,5,130,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13158 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 152 353 353 481 353), lower := (rows 97 7 134 56 152 32 64 128 256), losses := [] }

theorem u13158 : Upper (D 8) (R 8) [96,5,130,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13159 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 176 361 329 457 329), lower := (rows 97 7 134 56 176 32 64 128 256), losses := [] }

theorem u13159 : Upper (D 8) (R 8) [96,5,130,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13160 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 297, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 208 297 361 425 297), lower := (rows 97 7 134 56 208 32 64 128 256), losses := [] }

theorem u13160 : Upper (D 8) (R 8) [96,5,130,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13161 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 273 232 232 232 488), lower := (rows 97 7 134 56 273 32 64 128 256), losses := [] }

theorem u13161 : Upper (D 8) (R 8) [96,5,130,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13162 : Route 9 := (fun mask => (mask,id))

def c13162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13162 : Upper (D 8) (R 8) [96,5,130,48,264] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,264] 13 (by decide) (choices 1) [1,64,128] r13162 c13162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4270
  · exact u4271
  · exact u4272

def b13163 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 304 233 201 201 457), lower := (rows 97 7 134 56 304 32 64 128 256), losses := [] }

theorem u13163 : Upper (D 8) (R 8) [96,5,130,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13164 : Route 9 := (fun mask => (mask,id))

def c13164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13164 : Upper (D 8) (R 8) [96,5,130,48,320] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,320] 13 (by decide) (choices 1) [1,8,128] r13164 c13164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4273
  · exact u4274
  · exact u4275

def b13165 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 400 105 105 233 361), lower := (rows 97 7 134 56 400 32 64 128 256), losses := [] }

theorem u13165 : Upper (D 8) (R 8) [96,5,130,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13166 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 73 280 176 240 176 432), lower := (rows 97 7 134 73 280 32 64 128 256), losses := [] }

theorem u13166 : Upper (D 8) (R 8) [96,5,130,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13167 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 73 304 184 248 184 440), lower := (rows 97 7 134 73 304 32 64 128 256), losses := [] }

theorem u13167 : Upper (D 8) (R 8) [96,5,130,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13168 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 88 145 296 360 424 296), lower := (rows 97 7 134 88 145 32 64 128 256), losses := [] }

theorem u13168 : Upper (D 8) (R 8) [96,5,130,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13169 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 88 152 289 353 417 289), lower := (rows 97 7 134 88 152 32 64 128 256), losses := [] }

theorem u13169 : Upper (D 8) (R 8) [96,5,130,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13170 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 88 176 297 361 425 297), lower := (rows 97 7 134 88 176 32 64 128 256), losses := [] }

theorem u13170 : Upper (D 8) (R 8) [96,5,130,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13171 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 88 273 168 232 168 424), lower := (rows 97 7 134 88 273 32 64 128 256), losses := [] }

theorem u13171 : Upper (D 8) (R 8) [96,5,130,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13172 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 88 280 161 225 161 417), lower := (rows 97 7 134 88 280 32 64 128 256), losses := [] }

theorem u13172 : Upper (D 8) (R 8) [96,5,130,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13173 : Route 9 := (fun mask => (mask,id))

def c13173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13173 : Upper (D 8) (R 8) [96,5,130,80,288] 13 := by
  apply FastRouting.sound _ _ [96,5,130,80,288] 13 (by decide) (choices 1) [1,8,128] r13173 c13173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4276
  · exact u4277
  · exact u4278

def b13174 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 88 400 41 105 169 297), lower := (rows 97 7 134 88 400 32 64 128 256), losses := [] }

theorem u13174 : Upper (D 8) (R 8) [96,5,130,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13175 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 104 280 177 241 177 433), lower := (rows 97 7 134 104 280 32 64 128 256), losses := [] }

theorem u13175 : Upper (D 8) (R 8) [96,5,130,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13176 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 104 304 185 217 153 409), lower := (rows 97 7 134 104 304 32 64 128 256), losses := [] }

theorem u13176 : Upper (D 8) (R 8) [96,5,130,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13177 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 137 280 112 112 240 368), lower := (rows 97 7 134 137 280 32 64 128 256), losses := [] }

theorem u13177 : Upper (D 8) (R 8) [96,5,130,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13178 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 137 304 120 120 248 376), lower := (rows 97 7 134 137 304 32 64 128 256), losses := [] }

theorem u13178 : Upper (D 8) (R 8) [96,5,130,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13179 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 137 336 56 120 184 312), lower := (rows 97 7 134 137 336 32 64 128 256), losses := [] }

theorem u13179 : Upper (D 8) (R 8) [96,5,130,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13180 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 273 104 104 232 360), lower := (rows 97 7 134 152 273 32 64 128 256), losses := [] }

theorem u13180 : Upper (D 8) (R 8) [96,5,130,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13181 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 280 97 97 225 353), lower := (rows 97 7 134 152 280 32 64 128 256), losses := [] }

theorem u13181 : Upper (D 8) (R 8) [96,5,130,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13182 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 304 105 105 233 361), lower := (rows 97 7 134 152 304 32 64 128 256), losses := [] }

theorem u13182 : Upper (D 8) (R 8) [96,5,130,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13183 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 336 41 105 169 297), lower := (rows 97 7 134 152 336 32 64 128 256), losses := [] }

theorem u13183 : Upper (D 8) (R 8) [96,5,130,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13184 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 273 120 120 248 376), lower := (rows 97 7 134 168 273 32 64 128 256), losses := [] }

theorem u13184 : Upper (D 8) (R 8) [96,5,130,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13185 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 280 113 113 241 369), lower := (rows 97 7 134 168 280 32 64 128 256), losses := [] }

theorem u13185 : Upper (D 8) (R 8) [96,5,130,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13186 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 304 121 89 217 345), lower := (rows 97 7 134 168 304 32 64 128 256), losses := [] }

theorem u13186 : Upper (D 8) (R 8) [96,5,130,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13187 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 336 57 121 185 313), lower := (rows 97 7 134 168 336 32 64 128 256), losses := [] }

theorem u13187 : Upper (D 8) (R 8) [96,5,130,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13188 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 200 273 56 120 184 312), lower := (rows 97 7 134 200 273 32 64 128 256), losses := [] }

theorem u13188 : Upper (D 8) (R 8) [96,5,130,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13189 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 200 280 49 113 177 305), lower := (rows 97 7 134 200 280 32 64 128 256), losses := [] }

theorem u13189 : Upper (D 8) (R 8) [96,5,130,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13190 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 200 304 57 121 185 313), lower := (rows 97 7 134 200 304 32 64 128 256), losses := [] }

theorem u13190 : Upper (D 8) (R 8) [96,5,130,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13191 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 25 176 354 354 482 354), lower := (rows 97 7 140 25 176 32 64 128 256), losses := [] }

theorem u13191 : Upper (D 8) (R 8) [96,5,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13192 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 25 208 290 354 418 290), lower := (rows 97 7 140 25 208 32 64 128 256), losses := [] }

theorem u13192 : Upper (D 8) (R 8) [96,5,136,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13193 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 25 274 224 224 224 480), lower := (rows 97 7 140 25 274 32 64 128 256), losses := [] }

theorem u13193 : Upper (D 8) (R 8) [96,5,136,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13194 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 25 304 226 226 226 482), lower := (rows 97 7 140 25 304 32 64 128 256), losses := [] }

theorem u13194 : Upper (D 8) (R 8) [96,5,136,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13195 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 25 336 162 226 162 418), lower := (rows 97 7 140 25 336 32 64 128 256), losses := [] }

theorem u13195 : Upper (D 8) (R 8) [96,5,136,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13196 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 25 400 98 98 226 354), lower := (rows 97 7 140 25 400 32 64 128 256), losses := [] }

theorem u13196 : Upper (D 8) (R 8) [96,5,136,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13197 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 26 49 480 480 480 480), lower := (rows 97 7 140 26 49 32 64 128 256), losses := [] }

theorem u13197 : Upper (D 8) (R 8) [96,5,136,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13198 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 26 81 416 480 416 416), lower := (rows 97 7 140 26 81 32 64 128 256), losses := [] }

theorem u13198 : Upper (D 8) (R 8) [96,5,136,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13199 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 26 112 417 481 417 417), lower := (rows 97 7 140 26 112 32 64 128 256), losses := [] }

theorem u13199 : Upper (D 8) (R 8) [96,5,136,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13199
end Delivery.IrregularNine14.P08
