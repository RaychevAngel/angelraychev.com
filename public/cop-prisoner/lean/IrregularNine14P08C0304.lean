import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0112

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18240 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 41 146 56 120 184 312), lower := (rows 321 7 196 41 146 32 64 128 256), losses := [] }

theorem u18240 : Upper (D 8) (R 8) [320,5,192,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18241 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 41 152 50 114 178 306), lower := (rows 321 7 196 41 152 32 64 128 256), losses := [] }

theorem u18241 : Upper (D 8) (R 8) [320,5,192,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18242 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 41 176 58 122 186 314), lower := (rows 321 7 196 41 176 32 64 128 256), losses := [] }

theorem u18242 : Upper (D 8) (R 8) [320,5,192,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18243 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 42 145 56 120 184 312), lower := (rows 321 7 196 42 145 32 64 128 256), losses := [] }

theorem u18243 : Upper (D 8) (R 8) [320,5,192,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18244 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 42 152 49 113 177 305), lower := (rows 321 7 196 42 152 32 64 128 256), losses := [] }

theorem u18244 : Upper (D 8) (R 8) [320,5,192,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18245 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 42 176 57 121 185 313), lower := (rows 321 7 196 42 176 32 64 128 256), losses := [] }

theorem u18245 : Upper (D 8) (R 8) [320,5,192,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18246 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 56 145 42 106 170 298), lower := (rows 321 7 196 56 145 32 64 128 256), losses := [] }

theorem u18246 : Upper (D 8) (R 8) [320,5,192,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18247 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 56 146 41 105 169 297), lower := (rows 321 7 196 56 146 32 64 128 256), losses := [] }

theorem u18247 : Upper (D 8) (R 8) [320,5,192,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18248 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 56 152 35 99 163 291), lower := (rows 321 7 196 56 152 32 64 128 256), losses := [] }

theorem u18248 : Upper (D 8) (R 8) [320,5,192,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18249 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 22, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 22 41 49 224 224 224 480), lower := (rows 321 14 22 41 49 32 64 128 256), losses := [] }

theorem u18249 : Upper (D 8) (R 8) [320,12,18,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18250 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 22 41 81 160 224 160 416), lower := (rows 321 14 22 41 81 32 64 128 256), losses := [] }

theorem u18250 : Upper (D 8) (R 8) [320,12,18,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18251 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 22 41 112 161 225 161 417), lower := (rows 321 14 22 41 112 32 64 128 256), losses := [] }

theorem u18251 : Upper (D 8) (R 8) [320,12,18,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18252 : Route 9 := (fun mask => (mask,id))

def c18252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18252 : Upper (D 8) (R 8) [320,12,18,33,129] 13 := by
  apply FastRouting.sound _ _ [320,12,18,33,129] 13 (by decide) (choices 1) [64,128] r18252 c18252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6729
  · exact u6730

def r18253 : Route 9 := (fun mask => (mask,id))

def c18253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18253 : Upper (D 8) (R 8) [320,12,18,33,160] 13 := by
  apply FastRouting.sound _ _ [320,12,18,33,160] 13 (by decide) (choices 1) [1,64,128] r18253 c18253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6731
  · exact u6732
  · exact u6733

def b18254 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 22 41 208 161 225 161 417), lower := (rows 321 14 22 41 208 32 64 128 256), losses := [] }

theorem u18254 : Upper (D 8) (R 8) [320,12,18,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18255 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 22 73 145 160 224 160 416), lower := (rows 321 14 22 73 145 32 64 128 256), losses := [] }

theorem u18255 : Upper (D 8) (R 8) [320,12,18,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18256 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 22 73 176 161 225 161 417), lower := (rows 321 14 22 73 176 32 64 128 256), losses := [] }

theorem u18256 : Upper (D 8) (R 8) [320,12,18,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18257 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 22 104 145 161 225 161 417), lower := (rows 321 14 22 104 145 32 64 128 256), losses := [] }

theorem u18257 : Upper (D 8) (R 8) [320,12,18,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18258 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 22 104 176 161 225 161 417), lower := (rows 321 14 22 104 176 32 64 128 256), losses := [] }

theorem u18258 : Upper (D 8) (R 8) [320,12,18,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18259 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 321 14 22 137 145 96 96 224 352), lower := (rows 321 14 22 137 145 32 64 128 256), losses := [] }

theorem u18259 : Upper (D 8) (R 8) [320,12,18,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18260 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 22 137 176 97 97 225 353), lower := (rows 321 14 22 137 176 32 64 128 256), losses := [] }

theorem u18260 : Upper (D 8) (R 8) [320,12,18,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18261 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 22 137 208 33 97 161 289), lower := (rows 321 14 22 137 208 32 64 128 256), losses := [] }

theorem u18261 : Upper (D 8) (R 8) [320,12,18,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18262 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 22 168 176 97 97 225 353), lower := (rows 321 14 22 168 176 32 64 128 256), losses := [] }

theorem u18262 : Upper (D 8) (R 8) [320,12,18,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18263 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 22 168 208 33 97 161 289), lower := (rows 321 14 22 168 208 32 64 128 256), losses := [] }

theorem u18263 : Upper (D 8) (R 8) [320,12,18,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18264 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 41 50 240 208 208 464), lower := (rows 321 14 37 41 50 32 64 128 256), losses := [] }

theorem u18264 : Upper (D 8) (R 8) [320,12,33,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18265 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 41 82 176 240 176 432), lower := (rows 321 14 37 41 82 32 64 128 256), losses := [] }

theorem u18265 : Upper (D 8) (R 8) [320,12,33,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18266 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 41 112 178 210 146 402), lower := (rows 321 14 37 41 112 32 64 128 256), losses := [] }

theorem u18266 : Upper (D 8) (R 8) [320,12,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18267 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 41 146 240 240 240 496), lower := (rows 321 14 37 41 146 32 64 128 256), losses := [] }

theorem u18267 : Upper (D 8) (R 8) [320,12,33,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18268 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 41 176 242 210 210 466), lower := (rows 321 14 37 41 176 32 64 128 256), losses := [] }

theorem u18268 : Upper (D 8) (R 8) [320,12,33,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18269 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 41 208 178 242 178 434), lower := (rows 321 14 37 41 208 32 64 128 256), losses := [] }

theorem u18269 : Upper (D 8) (R 8) [320,12,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18270 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 42 49 240 208 208 464), lower := (rows 321 14 37 42 49 32 64 128 256), losses := [] }

theorem u18270 : Upper (D 8) (R 8) [320,12,33,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18271 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 42 112 177 209 145 401), lower := (rows 321 14 37 42 112 32 64 128 256), losses := [] }

theorem u18271 : Upper (D 8) (R 8) [320,12,33,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18272 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 42 145 240 240 240 496), lower := (rows 321 14 37 42 145 32 64 128 256), losses := [] }

theorem u18272 : Upper (D 8) (R 8) [320,12,33,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18273 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 42 176 241 209 209 465), lower := (rows 321 14 37 42 176 32 64 128 256), losses := [] }

theorem u18273 : Upper (D 8) (R 8) [320,12,33,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18274 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 42 208 177 241 177 433), lower := (rows 321 14 37 42 208 32 64 128 256), losses := [] }

theorem u18274 : Upper (D 8) (R 8) [320,12,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18275 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 26, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 56 49 226 194 194 450), lower := (rows 321 14 37 56 49 32 64 128 256), losses := [] }

theorem u18275 : Upper (D 8) (R 8) [320,12,33,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18276 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 26, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 56 50 225 193 193 449), lower := (rows 321 14 37 56 50 32 64 128 256), losses := [] }

theorem u18276 : Upper (D 8) (R 8) [320,12,33,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18277 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 56 81 162 226 162 418), lower := (rows 321 14 37 56 81 32 64 128 256), losses := [] }

theorem u18277 : Upper (D 8) (R 8) [320,12,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18278 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 56 82 161 225 161 417), lower := (rows 321 14 37 56 82 32 64 128 256), losses := [] }

theorem u18278 : Upper (D 8) (R 8) [320,12,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18279 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 14 37 56 112 163 195 131 387), lower := (rows 321 14 37 56 112 32 64 128 256), losses := [] }

theorem u18279 : Upper (D 8) (R 8) [320,12,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18280 : Route 9 := (fun mask => (mask,id))

def c18280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18280 : Upper (D 8) (R 8) [320,12,33,48,129] 13 := by
  apply FastRouting.sound _ _ [320,12,33,48,129] 13 (by decide) (choices 1) [2,64,128] r18280 c18280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6734
  · exact u6735
  · exact u6736

def r18281 : Route 9 := (fun mask => (mask,id))

def c18281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18281 : Upper (D 8) (R 8) [320,12,33,48,130] 13 := by
  apply FastRouting.sound _ _ [320,12,33,48,130] 13 (by decide) (choices 1) [1,64,128] r18281 c18281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6737
  · exact u6738
  · exact u6739

def b18282 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 14 37 56 176 227 195 195 451), lower := (rows 321 14 37 56 176 32 64 128 256), losses := [] }

theorem u18282 : Upper (D 8) (R 8) [320,12,33,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18283 : Route 9 := (fun mask => (mask,id))

def c18283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18283 : Upper (D 8) (R 8) [320,12,33,48,192] 13 := by
  apply FastRouting.sound _ _ [320,12,33,48,192] 13 (by decide) (choices 1) [1,2,128] r18283 c18283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6740
  · exact u6741
  · exact u6742

def b18284 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 73 50 176 240 176 432), lower := (rows 321 14 37 73 50 32 64 128 256), losses := [] }

theorem u18284 : Upper (D 8) (R 8) [320,12,33,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18285 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 73 146 176 240 176 432), lower := (rows 321 14 37 73 146 32 64 128 256), losses := [] }

theorem u18285 : Upper (D 8) (R 8) [320,12,33,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18286 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 73 176 178 242 178 434), lower := (rows 321 14 37 73 176 32 64 128 256), losses := [] }

theorem u18286 : Upper (D 8) (R 8) [320,12,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18287 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 74 145 176 240 176 432), lower := (rows 321 14 37 74 145 32 64 128 256), losses := [] }

theorem u18287 : Upper (D 8) (R 8) [320,12,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18288 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 74 176 177 241 177 433), lower := (rows 321 14 37 74 176 32 64 128 256), losses := [] }

theorem u18288 : Upper (D 8) (R 8) [320,12,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18289 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 37 88 49 162 226 162 418), lower := (rows 321 14 37 88 49 32 64 128 256), losses := [] }

theorem u18289 : Upper (D 8) (R 8) [320,12,33,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18290 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 88 50 161 225 161 417), lower := (rows 321 14 37 88 50 32 64 128 256), losses := [] }

theorem u18290 : Upper (D 8) (R 8) [320,12,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18291 : Route 9 := (fun mask => (mask,id))

def c18291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18291 : Upper (D 8) (R 8) [320,12,33,80,129] 13 := by
  apply FastRouting.sound _ _ [320,12,33,80,129] 13 (by decide) (choices 1) [2,128] r18291 c18291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6743
  · exact u6744

def b18292 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 88 146 161 225 161 417), lower := (rows 321 14 37 88 146 32 64 128 256), losses := [] }

theorem u18292 : Upper (D 8) (R 8) [320,12,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18293 : Route 9 := (fun mask => (mask,id))

def c18293 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18293 : Upper (D 8) (R 8) [320,12,33,80,160] 13 := by
  apply FastRouting.sound _ _ [320,12,33,80,160] 13 (by decide) (choices 1) [1,2,128] r18293 c18293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6745
  · exact u6746
  · exact u6747

def b18294 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 37 104 49 178 210 146 402), lower := (rows 321 14 37 104 49 32 64 128 256), losses := [] }

theorem u18294 : Upper (D 8) (R 8) [320,12,33,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18295 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 321 14 37 104 50 177 209 145 401), lower := (rows 321 14 37 104 50 32 64 128 256), losses := [] }

theorem u18295 : Upper (D 8) (R 8) [320,12,33,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18296 : Route 9 := (fun mask => (mask,id))

def c18296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18296 : Upper (D 8) (R 8) [320,12,33,96,129] 13 := by
  apply FastRouting.sound _ _ [320,12,33,96,129] 13 (by decide) (choices 1) [2,16,128] r18296 c18296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6748
  · exact u6749
  · exact u6750

def r18297 : Route 9 := (fun mask => (mask,id))

def c18297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18297 : Upper (D 8) (R 8) [320,12,33,96,130] 13 := by
  apply FastRouting.sound _ _ [320,12,33,96,130] 13 (by decide) (choices 1) [1,16,128] r18297 c18297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6751
  · exact u6752
  · exact u6753

def r18298 : Route 9 := (fun mask => (mask,id))

def c18298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18298 : Upper (D 8) (R 8) [320,12,33,96,160] 13 := by
  apply FastRouting.sound _ _ [320,12,33,96,160] 13 (by decide) (choices 1) [1,2,16,128] r18298 c18298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6754
  · exact u6755
  · exact u6756
  · exact u6757

def b18299 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 137 50 240 240 240 496), lower := (rows 321 14 37 137 50 32 64 128 256), losses := [] }

theorem u18299 : Upper (D 8) (R 8) [320,12,33,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18299
end Delivery.IrregularNine14.P08
