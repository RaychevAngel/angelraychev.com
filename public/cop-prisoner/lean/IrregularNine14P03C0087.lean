import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0034

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5220 : Route 9 := (fun mask => (mask,id))

def c5220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5220 : Upper (D 3) (R 3) [258,36,192,80,160] 13 := by
  apply FastRouting.sound _ _ [258,36,192,80,160] 13 (by decide) (choices 1) [1,8] r5220 c5220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2066
  · exact u2067

def b5221 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 13 145 240 240 240 496), lower := (rows 259 98 13 13 145 32 64 128 256), losses := [] }

theorem u5221 : Upper (D 3) (R 3) [258,96,9,5,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5221
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5222 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 13 176 241 209 209 465), lower := (rows 259 98 13 13 176 32 64 128 256), losses := [] }

theorem u5222 : Upper (D 3) (R 3) [258,96,9,5,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5222
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5223 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 25 52 225 193 193 449), lower := (rows 259 98 13 25 52 32 64 128 256), losses := [] }

theorem u5223 : Upper (D 3) (R 3) [258,96,9,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5223
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5224 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 25 145 228 228 228 484), lower := (rows 259 98 13 25 145 32 64 128 256), losses := [] }

theorem u5224 : Upper (D 3) (R 3) [258,96,9,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5224
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5225 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 25 148 225 225 225 481), lower := (rows 259 98 13 25 148 32 64 128 256), losses := [] }

theorem u5225 : Upper (D 3) (R 3) [258,96,9,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5225
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5226 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 25 176 229 197 197 453), lower := (rows 259 98 13 25 176 32 64 128 256), losses := [] }

theorem u5226 : Upper (D 3) (R 3) [258,96,9,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5226
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5227 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 28 49 225 193 193 449), lower := (rows 259 98 13 28 49 32 64 128 256), losses := [] }

theorem u5227 : Upper (D 3) (R 3) [258,96,9,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5227
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5228 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 28 112 161 193 129 385), lower := (rows 259 98 13 28 112 32 64 128 256), losses := [] }

theorem u5228 : Upper (D 3) (R 3) [258,96,9,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5228
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5229 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 28 145 225 225 225 481), lower := (rows 259 98 13 28 145 32 64 128 256), losses := [] }

theorem u5229 : Upper (D 3) (R 3) [258,96,9,20,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5229
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5230 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 13 28 176 225 193 193 449), lower := (rows 259 98 13 28 176 32 64 128 256), losses := [] }

theorem u5230 : Upper (D 3) (R 3) [258,96,9,20,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5230
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5231 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 84 177 209 145 401), lower := (rows 259 98 13 41 84 32 64 128 256), losses := [] }

theorem u5231 : Upper (D 3) (R 3) [258,96,9,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5231
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5232 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 145 244 212 212 468), lower := (rows 259 98 13 41 145 32 64 128 256), losses := [] }

theorem u5232 : Upper (D 3) (R 3) [258,96,9,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5232
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5233 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 148 241 209 209 465), lower := (rows 259 98 13 41 148 32 64 128 256), losses := [] }

theorem u5233 : Upper (D 3) (R 3) [258,96,9,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5233
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5234 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 208 181 213 149 405), lower := (rows 259 98 13 41 208 32 64 128 256), losses := [] }

theorem u5234 : Upper (D 3) (R 3) [258,96,9,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5234
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5235 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 13 44 145 241 209 209 465), lower := (rows 259 98 13 44 145 32 64 128 256), losses := [] }

theorem u5235 : Upper (D 3) (R 3) [258,96,9,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5235
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5236 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 13 44 208 177 209 145 401), lower := (rows 259 98 13 44 208 32 64 128 256), losses := [] }

theorem u5236 : Upper (D 3) (R 3) [258,96,9,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5236
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5237 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 13 56 84 161 193 129 385), lower := (rows 259 98 13 56 84 32 64 128 256), losses := [] }

theorem u5237 : Upper (D 3) (R 3) [258,96,9,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5237
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5238 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 13 56 145 229 197 197 453), lower := (rows 259 98 13 56 145 32 64 128 256), losses := [] }

theorem u5238 : Upper (D 3) (R 3) [258,96,9,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5238
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5239 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 13 56 148 225 193 193 449), lower := (rows 259 98 13 56 148 32 64 128 256), losses := [] }

theorem u5239 : Upper (D 3) (R 3) [258,96,9,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5239
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5240 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 13 56 208 165 197 133 389), lower := (rows 259 98 13 56 208 32 64 128 256), losses := [] }

theorem u5240 : Upper (D 3) (R 3) [258,96,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5240
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5241 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 145 181 213 149 405), lower := (rows 259 98 13 104 145 32 64 128 256), losses := [] }

theorem u5241 : Upper (D 3) (R 3) [258,96,9,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5241
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5242 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 148 177 209 145 401), lower := (rows 259 98 13 104 148 32 64 128 256), losses := [] }

theorem u5242 : Upper (D 3) (R 3) [258,96,9,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5242
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5243 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 52 241 209 209 465), lower := (rows 259 98 13 137 52 32 64 128 256), losses := [] }

theorem u5243 : Upper (D 3) (R 3) [258,96,9,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5243
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5244 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 145 116 116 244 372), lower := (rows 259 98 13 137 145 32 64 128 256), losses := [] }

theorem u5244 : Upper (D 3) (R 3) [258,96,9,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5244
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5245 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 148 113 113 241 369), lower := (rows 259 98 13 137 148 32 64 128 256), losses := [] }

theorem u5245 : Upper (D 3) (R 3) [258,96,9,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5245
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5246 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 176 117 85 213 341), lower := (rows 259 98 13 137 176 32 64 128 256), losses := [] }

theorem u5246 : Upper (D 3) (R 3) [258,96,9,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5246
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5247 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 140 49 241 209 209 465), lower := (rows 259 98 13 140 49 32 64 128 256), losses := [] }

theorem u5247 : Upper (D 3) (R 3) [258,96,9,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5247
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5248 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 140 112 177 209 145 401), lower := (rows 259 98 13 140 112 32 64 128 256), losses := [] }

theorem u5248 : Upper (D 3) (R 3) [258,96,9,132,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5248
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5249 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 140 145 113 113 241 369), lower := (rows 259 98 13 140 145 32 64 128 256), losses := [] }

theorem u5249 : Upper (D 3) (R 3) [258,96,9,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5249
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5250 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 140 176 113 81 209 337), lower := (rows 259 98 13 140 176 32 64 128 256), losses := [] }

theorem u5250 : Upper (D 3) (R 3) [258,96,9,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5250
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5251 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 152 49 229 197 197 453), lower := (rows 259 98 13 152 49 32 64 128 256), losses := [] }

theorem u5251 : Upper (D 3) (R 3) [258,96,9,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5251
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5252 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 13 152 52 225 193 193 449), lower := (rows 259 98 13 152 52 32 64 128 256), losses := [] }

theorem u5252 : Upper (D 3) (R 3) [258,96,9,144,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5252
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5253 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 152 112 165 197 133 389), lower := (rows 259 98 13 152 112 32 64 128 256), losses := [] }

theorem u5253 : Upper (D 3) (R 3) [258,96,9,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5253
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5254 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 152 145 101 101 229 357), lower := (rows 259 98 13 152 145 32 64 128 256), losses := [] }

theorem u5254 : Upper (D 3) (R 3) [258,96,9,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5254
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5255 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 152 148 97 97 225 353), lower := (rows 259 98 13 152 148 32 64 128 256), losses := [] }

theorem u5255 : Upper (D 3) (R 3) [258,96,9,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5255
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5256 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 152 176 101 69 197 325), lower := (rows 259 98 13 152 176 32 64 128 256), losses := [] }

theorem u5256 : Upper (D 3) (R 3) [258,96,9,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5256
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5257 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 13 168 84 177 209 145 401), lower := (rows 259 98 13 168 84 32 64 128 256), losses := [] }

theorem u5257 : Upper (D 3) (R 3) [258,96,9,160,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5257
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5258 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 13 168 145 117 85 213 341), lower := (rows 259 98 13 168 145 32 64 128 256), losses := [] }

theorem u5258 : Upper (D 3) (R 3) [258,96,9,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5258
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5259 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 168 148 113 81 209 337), lower := (rows 259 98 13 168 148 32 64 128 256), losses := [] }

theorem u5259 : Upper (D 3) (R 3) [258,96,9,160,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5259
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5260 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 13 168 208 53 85 149 277), lower := (rows 259 98 13 168 208 32 64 128 256), losses := [] }

theorem u5260 : Upper (D 3) (R 3) [258,96,9,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5260
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5261 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 28 41 145 229 197 197 453), lower := (rows 259 98 28 41 145 32 64 128 256), losses := [] }

theorem u5261 : Upper (D 3) (R 3) [258,96,24,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5261
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5262 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 28 41 148 225 193 193 449), lower := (rows 259 98 28 41 148 32 64 128 256), losses := [] }

theorem u5262 : Upper (D 3) (R 3) [258,96,24,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5262
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5263 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 28 41 208 165 197 133 389), lower := (rows 259 98 28 41 208 32 64 128 256), losses := [] }

theorem u5263 : Upper (D 3) (R 3) [258,96,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5263
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5264 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 28 44 145 225 193 193 449), lower := (rows 259 98 28 44 145 32 64 128 256), losses := [] }

theorem u5264 : Upper (D 3) (R 3) [258,96,24,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5264
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5265 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 28 44 208 161 193 129 385), lower := (rows 259 98 28 44 208 32 64 128 256), losses := [] }

theorem u5265 : Upper (D 3) (R 3) [258,96,24,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5265
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5266 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 28 104 145 165 197 133 389), lower := (rows 259 98 28 104 145 32 64 128 256), losses := [] }

theorem u5266 : Upper (D 3) (R 3) [258,96,24,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5266
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5267 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 28 104 148 161 193 129 385), lower := (rows 259 98 28 104 148 32 64 128 256), losses := [] }

theorem u5267 : Upper (D 3) (R 3) [258,96,24,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5267
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5268 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 28 137 145 101 101 229 357), lower := (rows 259 98 28 137 145 32 64 128 256), losses := [] }

theorem u5268 : Upper (D 3) (R 3) [258,96,24,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5268
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5269 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 137 148 97 97 225 353), lower := (rows 259 98 28 137 148 32 64 128 256), losses := [] }

theorem u5269 : Upper (D 3) (R 3) [258,96,24,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5269
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5270 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 28 137 176 101 69 197 325), lower := (rows 259 98 28 137 176 32 64 128 256), losses := [] }

theorem u5270 : Upper (D 3) (R 3) [258,96,24,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5270
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5271 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 140 176 97 65 193 321), lower := (rows 259 98 28 140 176 32 64 128 256), losses := [] }

theorem u5271 : Upper (D 3) (R 3) [258,96,24,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5271
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5272 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 28 168 208 37 69 133 261), lower := (rows 259 98 28 168 208 32 64 128 256), losses := [] }

theorem u5272 : Upper (D 3) (R 3) [258,96,24,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5272
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5273 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 76 145 185 217 153 409), lower := (rows 259 98 37 76 145 32 64 128 256), losses := [] }

theorem u5273 : Upper (D 3) (R 3) [258,96,33,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5273
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5274 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 76 152 177 209 145 401), lower := (rows 259 98 37 76 152 32 64 128 256), losses := [] }

theorem u5274 : Upper (D 3) (R 3) [258,96,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5274
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5275 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 88 145 173 205 141 397), lower := (rows 259 98 37 88 145 32 64 128 256), losses := [] }

theorem u5275 : Upper (D 3) (R 3) [258,96,33,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5275
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5276 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 88 148 169 201 137 393), lower := (rows 259 98 37 88 148 32 64 128 256), losses := [] }

theorem u5276 : Upper (D 3) (R 3) [258,96,33,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5276
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5277 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 137 148 121 89 217 345), lower := (rows 259 98 37 137 148 32 64 128 256), losses := [] }

theorem u5277 : Upper (D 3) (R 3) [258,96,33,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5277
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5278 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 137 208 61 93 157 285), lower := (rows 259 98 37 137 208 32 64 128 256), losses := [] }

theorem u5278 : Upper (D 3) (R 3) [258,96,33,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5278
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5279 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 140 208 57 89 153 281), lower := (rows 259 98 37 140 208 32 64 128 256), losses := [] }

theorem u5279 : Upper (D 3) (R 3) [258,96,33,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5279
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5279
end Delivery.IrregularNine14.P03
