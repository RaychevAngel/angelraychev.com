import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0104
import IrregularNine14P08C0105

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17220 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 70 41 56 240 208 208 464), lower := (rows 289 7 70 41 56 32 64 128 256), losses := [] }

theorem u17220 : Upper (D 8) (R 8) [288,5,66,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17221 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 70 41 152 240 240 240 496), lower := (rows 289 7 70 41 152 32 64 128 256), losses := [] }

theorem u17221 : Upper (D 8) (R 8) [288,5,66,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17222 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 70 41 176 248 216 216 472), lower := (rows 289 7 70 41 176 32 64 128 256), losses := [] }

theorem u17222 : Upper (D 8) (R 8) [288,5,66,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17223 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 70 56 56 225 193 193 449), lower := (rows 289 7 70 56 56 32 64 128 256), losses := [] }

theorem u17223 : Upper (D 8) (R 8) [288,5,66,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17224 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 56 81 168 232 168 424), lower := (rows 289 7 70 56 81 32 64 128 256), losses := [] }

theorem u17224 : Upper (D 8) (R 8) [288,5,66,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17225 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 56 88 161 225 161 417), lower := (rows 289 7 70 56 88 32 64 128 256), losses := [] }

theorem u17225 : Upper (D 8) (R 8) [288,5,66,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17226 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 70 56 112 169 201 137 393), lower := (rows 289 7 70 56 112 32 64 128 256), losses := [] }

theorem u17226 : Upper (D 8) (R 8) [288,5,66,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17227 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 70 56 145 232 232 232 488), lower := (rows 289 7 70 56 145 32 64 128 256), losses := [] }

theorem u17227 : Upper (D 8) (R 8) [288,5,66,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17228 : Route 9 := (fun mask => (mask,id))

def c17228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17228 : Upper (D 8) (R 8) [288,5,66,48,136] 13 := by
  apply FastRouting.sound _ _ [288,5,66,48,136] 13 (by decide) (choices 1) [1,64,128] r17228 c17228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6283
  · exact u6284
  · exact u6285

def b17229 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 70 56 176 233 201 201 457), lower := (rows 289 7 70 56 176 32 64 128 256), losses := [] }

theorem u17229 : Upper (D 8) (R 8) [288,5,66,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17230 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 56 208 169 233 169 425), lower := (rows 289 7 70 56 208 32 64 128 256), losses := [] }

theorem u17230 : Upper (D 8) (R 8) [288,5,66,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17231 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 73 152 176 240 176 432), lower := (rows 289 7 70 73 152 32 64 128 256), losses := [] }

theorem u17231 : Upper (D 8) (R 8) [288,5,66,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17232 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 73 176 184 248 184 440), lower := (rows 289 7 70 73 176 32 64 128 256), losses := [] }

theorem u17232 : Upper (D 8) (R 8) [288,5,66,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17233 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 88 145 168 232 168 424), lower := (rows 289 7 70 88 145 32 64 128 256), losses := [] }

theorem u17233 : Upper (D 8) (R 8) [288,5,66,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17234 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 88 152 161 225 161 417), lower := (rows 289 7 70 88 152 32 64 128 256), losses := [] }

theorem u17234 : Upper (D 8) (R 8) [288,5,66,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17235 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 88 176 169 233 169 425), lower := (rows 289 7 70 88 176 32 64 128 256), losses := [] }

theorem u17235 : Upper (D 8) (R 8) [288,5,66,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17236 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 104 145 184 248 184 440), lower := (rows 289 7 70 104 145 32 64 128 256), losses := [] }

theorem u17236 : Upper (D 8) (R 8) [288,5,66,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17237 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 104 152 177 241 177 433), lower := (rows 289 7 70 104 152 32 64 128 256), losses := [] }

theorem u17237 : Upper (D 8) (R 8) [288,5,66,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17238 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 104 176 185 217 153 409), lower := (rows 289 7 70 104 176 32 64 128 256), losses := [] }

theorem u17238 : Upper (D 8) (R 8) [288,5,66,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17239 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 70 137 152 112 112 240 368), lower := (rows 289 7 70 137 152 32 64 128 256), losses := [] }

theorem u17239 : Upper (D 8) (R 8) [288,5,66,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17240 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 70 137 176 120 120 248 376), lower := (rows 289 7 70 137 176 32 64 128 256), losses := [] }

theorem u17240 : Upper (D 8) (R 8) [288,5,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17241 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 137 208 56 120 184 312), lower := (rows 289 7 70 137 208 32 64 128 256), losses := [] }

theorem u17241 : Upper (D 8) (R 8) [288,5,66,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17242 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 70 152 152 97 97 225 353), lower := (rows 289 7 70 152 152 32 64 128 256), losses := [] }

theorem u17242 : Upper (D 8) (R 8) [288,5,66,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17243 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 70 152 176 105 105 233 361), lower := (rows 289 7 70 152 176 32 64 128 256), losses := [] }

theorem u17243 : Upper (D 8) (R 8) [288,5,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17244 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 70 152 208 41 105 169 297), lower := (rows 289 7 70 152 208 32 64 128 256), losses := [] }

theorem u17244 : Upper (D 8) (R 8) [288,5,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17245 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 70 168 176 121 89 217 345), lower := (rows 289 7 70 168 176 32 64 128 256), losses := [] }

theorem u17245 : Upper (D 8) (R 8) [288,5,66,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17246 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 168 208 57 121 185 313), lower := (rows 289 7 70 168 208 32 64 128 256), losses := [] }

theorem u17246 : Upper (D 8) (R 8) [288,5,66,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17247 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 25 112 162 226 162 418), lower := (rows 289 7 76 25 112 32 64 128 256), losses := [] }

theorem u17247 : Upper (D 8) (R 8) [288,5,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17248 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 76 25 146 224 224 224 480), lower := (rows 289 7 76 25 146 32 64 128 256), losses := [] }

theorem u17248 : Upper (D 8) (R 8) [288,5,72,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17249 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 76 25 176 226 226 226 482), lower := (rows 289 7 76 25 176 32 64 128 256), losses := [] }

theorem u17249 : Upper (D 8) (R 8) [288,5,72,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17250 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 25 208 162 226 162 418), lower := (rows 289 7 76 25 208 32 64 128 256), losses := [] }

theorem u17250 : Upper (D 8) (R 8) [288,5,72,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17251 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 76 26 49 224 224 224 480), lower := (rows 289 7 76 26 49 32 64 128 256), losses := [] }

theorem u17251 : Upper (D 8) (R 8) [288,5,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17252 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 26 81 160 224 160 416), lower := (rows 289 7 76 26 81 32 64 128 256), losses := [] }

theorem u17252 : Upper (D 8) (R 8) [288,5,72,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17253 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 26 112 161 225 161 417), lower := (rows 289 7 76 26 112 32 64 128 256), losses := [] }

theorem u17253 : Upper (D 8) (R 8) [288,5,72,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17254 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 76 26 145 224 224 224 480), lower := (rows 289 7 76 26 145 32 64 128 256), losses := [] }

theorem u17254 : Upper (D 8) (R 8) [288,5,72,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17255 : Route 9 := (fun mask => (mask,id))

def c17255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17255 : Upper (D 8) (R 8) [288,5,72,18,160] 13 := by
  apply FastRouting.sound _ _ [288,5,72,18,160] 13 (by decide) (choices 1) [1,64,128] r17255 c17255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6286
  · exact u6287
  · exact u6288

def b17256 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 26 208 161 225 161 417), lower := (rows 289 7 76 26 208 32 64 128 256), losses := [] }

theorem u17256 : Upper (D 8) (R 8) [288,5,72,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17257 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 76 41 50 240 208 208 464), lower := (rows 289 7 76 41 50 32 64 128 256), losses := [] }

theorem u17257 : Upper (D 8) (R 8) [288,5,72,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17258 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 76 41 112 178 210 146 402), lower := (rows 289 7 76 41 112 32 64 128 256), losses := [] }

theorem u17258 : Upper (D 8) (R 8) [288,5,72,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17259 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 76 41 146 240 240 240 496), lower := (rows 289 7 76 41 146 32 64 128 256), losses := [] }

theorem u17259 : Upper (D 8) (R 8) [288,5,72,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17260 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 76 41 176 242 210 210 466), lower := (rows 289 7 76 41 176 32 64 128 256), losses := [] }

theorem u17260 : Upper (D 8) (R 8) [288,5,72,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17261 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 76 41 208 178 242 178 434), lower := (rows 289 7 76 41 208 32 64 128 256), losses := [] }

theorem u17261 : Upper (D 8) (R 8) [288,5,72,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17262 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 76 42 49 240 208 208 464), lower := (rows 289 7 76 42 49 32 64 128 256), losses := [] }

theorem u17262 : Upper (D 8) (R 8) [288,5,72,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17263 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 42 81 176 240 176 432), lower := (rows 289 7 76 42 81 32 64 128 256), losses := [] }

theorem u17263 : Upper (D 8) (R 8) [288,5,72,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17264 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 42 112 177 209 145 401), lower := (rows 289 7 76 42 112 32 64 128 256), losses := [] }

theorem u17264 : Upper (D 8) (R 8) [288,5,72,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17265 : Route 9 := (fun mask => (mask,id))

def c17265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17265 : Upper (D 8) (R 8) [288,5,72,34,129] 13 := by
  apply FastRouting.sound _ _ [288,5,72,34,129] 13 (by decide) (choices 1) [16,64,128] r17265 c17265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6289
  · exact u6290
  · exact u6291

def r17266 : Route 9 := (fun mask => (mask,id))

def c17266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17266 : Upper (D 8) (R 8) [288,5,72,34,160] 13 := by
  apply FastRouting.sound _ _ [288,5,72,34,160] 13 (by decide) (choices 1) [1,16,64,128] r17266 c17266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6292
  · exact u6293
  · exact u6294
  · exact u6295

def b17267 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 42 208 177 241 177 433), lower := (rows 289 7 76 42 208 32 64 128 256), losses := [] }

theorem u17267 : Upper (D 8) (R 8) [288,5,72,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17268 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 76 56 49 226 194 194 450), lower := (rows 289 7 76 56 49 32 64 128 256), losses := [] }

theorem u17268 : Upper (D 8) (R 8) [288,5,72,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17269 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 76 56 50 225 193 193 449), lower := (rows 289 7 76 56 50 32 64 128 256), losses := [] }

theorem u17269 : Upper (D 8) (R 8) [288,5,72,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17270 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 56 81 162 226 162 418), lower := (rows 289 7 76 56 81 32 64 128 256), losses := [] }

theorem u17270 : Upper (D 8) (R 8) [288,5,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17271 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 56 82 161 225 161 417), lower := (rows 289 7 76 56 82 32 64 128 256), losses := [] }

theorem u17271 : Upper (D 8) (R 8) [288,5,72,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17272 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 76 56 112 163 195 131 387), lower := (rows 289 7 76 56 112 32 64 128 256), losses := [] }

theorem u17272 : Upper (D 8) (R 8) [288,5,72,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17273 : Route 9 := (fun mask => (mask,id))

def c17273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17273 : Upper (D 8) (R 8) [288,5,72,48,129] 13 := by
  apply FastRouting.sound _ _ [288,5,72,48,129] 13 (by decide) (choices 1) [2,64,128] r17273 c17273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6296
  · exact u6297
  · exact u6298

def r17274 : Route 9 := (fun mask => (mask,id))

def c17274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17274 : Upper (D 8) (R 8) [288,5,72,48,130] 13 := by
  apply FastRouting.sound _ _ [288,5,72,48,130] 13 (by decide) (choices 1) [1,64,128] r17274 c17274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6299
  · exact u6300
  · exact u6301

def b17275 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 76 56 176 227 195 195 451), lower := (rows 289 7 76 56 176 32 64 128 256), losses := [] }

theorem u17275 : Upper (D 8) (R 8) [288,5,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17276 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 56 208 163 227 163 419), lower := (rows 289 7 76 56 208 32 64 128 256), losses := [] }

theorem u17276 : Upper (D 8) (R 8) [288,5,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17277 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 73 50 176 240 176 432), lower := (rows 289 7 76 73 50 32 64 128 256), losses := [] }

theorem u17277 : Upper (D 8) (R 8) [288,5,72,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17278 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 73 146 176 240 176 432), lower := (rows 289 7 76 73 146 32 64 128 256), losses := [] }

theorem u17278 : Upper (D 8) (R 8) [288,5,72,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17279 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 73 176 178 242 178 434), lower := (rows 289 7 76 73 176 32 64 128 256), losses := [] }

theorem u17279 : Upper (D 8) (R 8) [288,5,72,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17279
end Delivery.IrregularNine14.P08
