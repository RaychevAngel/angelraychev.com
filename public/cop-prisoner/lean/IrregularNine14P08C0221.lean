import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0071
import IrregularNine14P08C0072

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13260 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 273 178 242 178 434), lower := (rows 97 7 140 104 273 32 64 128 256), losses := [] }

theorem u13260 : Upper (D 8) (R 8) [96,5,136,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13261 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 274 177 241 177 433), lower := (rows 97 7 140 104 274 32 64 128 256), losses := [] }

theorem u13261 : Upper (D 8) (R 8) [96,5,136,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13262 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 304 179 211 147 403), lower := (rows 97 7 140 104 304 32 64 128 256), losses := [] }

theorem u13262 : Upper (D 8) (R 8) [96,5,136,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13263 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 400 51 115 179 307), lower := (rows 97 7 140 104 400 32 64 128 256), losses := [] }

theorem u13263 : Upper (D 8) (R 8) [96,5,136,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13264 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 50 368 368 496 368), lower := (rows 97 7 140 137 50 32 64 128 256), losses := [] }

theorem u13264 : Upper (D 8) (R 8) [96,5,136,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13265 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 82 304 368 432 304), lower := (rows 97 7 140 137 82 32 64 128 256), losses := [] }

theorem u13265 : Upper (D 8) (R 8) [96,5,136,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13266 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 274 112 112 240 368), lower := (rows 97 7 140 137 274 32 64 128 256), losses := [] }

theorem u13266 : Upper (D 8) (R 8) [96,5,136,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13267 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 304 114 114 242 370), lower := (rows 97 7 140 137 304 32 64 128 256), losses := [] }

theorem u13267 : Upper (D 8) (R 8) [96,5,136,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13268 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 336 50 114 178 306), lower := (rows 97 7 140 137 336 32 64 128 256), losses := [] }

theorem u13268 : Upper (D 8) (R 8) [96,5,136,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13269 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 138 273 112 112 240 368), lower := (rows 97 7 140 138 273 32 64 128 256), losses := [] }

theorem u13269 : Upper (D 8) (R 8) [96,5,136,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13270 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 138 304 113 113 241 369), lower := (rows 97 7 140 138 304 32 64 128 256), losses := [] }

theorem u13270 : Upper (D 8) (R 8) [96,5,136,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13271 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 138 336 49 113 177 305), lower := (rows 97 7 140 138 336 32 64 128 256), losses := [] }

theorem u13271 : Upper (D 8) (R 8) [96,5,136,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13272 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 50 353 353 481 353), lower := (rows 97 7 140 152 50 32 64 128 256), losses := [] }

theorem u13272 : Upper (D 8) (R 8) [96,5,136,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13273 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 82 289 353 417 289), lower := (rows 97 7 140 152 82 32 64 128 256), losses := [] }

theorem u13273 : Upper (D 8) (R 8) [96,5,136,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13274 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 273 98 98 226 354), lower := (rows 97 7 140 152 273 32 64 128 256), losses := [] }

theorem u13274 : Upper (D 8) (R 8) [96,5,136,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13275 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 274 97 97 225 353), lower := (rows 97 7 140 152 274 32 64 128 256), losses := [] }

theorem u13275 : Upper (D 8) (R 8) [96,5,136,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13276 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 304 99 99 227 355), lower := (rows 97 7 140 152 304 32 64 128 256), losses := [] }

theorem u13276 : Upper (D 8) (R 8) [96,5,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13277 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 336 35 99 163 291), lower := (rows 97 7 140 152 336 32 64 128 256), losses := [] }

theorem u13277 : Upper (D 8) (R 8) [96,5,136,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13278 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 50 369 337 465 337), lower := (rows 97 7 140 168 50 32 64 128 256), losses := [] }

theorem u13278 : Upper (D 8) (R 8) [96,5,136,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13279 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 82 305 369 433 305), lower := (rows 97 7 140 168 82 32 64 128 256), losses := [] }

theorem u13279 : Upper (D 8) (R 8) [96,5,136,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13280 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 273 114 114 242 370), lower := (rows 97 7 140 168 273 32 64 128 256), losses := [] }

theorem u13280 : Upper (D 8) (R 8) [96,5,136,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13281 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 274 113 113 241 369), lower := (rows 97 7 140 168 274 32 64 128 256), losses := [] }

theorem u13281 : Upper (D 8) (R 8) [96,5,136,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13282 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 304 115 83 211 339), lower := (rows 97 7 140 168 304 32 64 128 256), losses := [] }

theorem u13282 : Upper (D 8) (R 8) [96,5,136,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13283 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 336 51 115 179 307), lower := (rows 97 7 140 168 336 32 64 128 256), losses := [] }

theorem u13283 : Upper (D 8) (R 8) [96,5,136,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13284 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 200 50 305 369 433 305), lower := (rows 97 7 140 200 50 32 64 128 256), losses := [] }

theorem u13284 : Upper (D 8) (R 8) [96,5,136,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13285 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 200 273 50 114 178 306), lower := (rows 97 7 140 200 273 32 64 128 256), losses := [] }

theorem u13285 : Upper (D 8) (R 8) [96,5,136,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13286 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 200 274 49 113 177 305), lower := (rows 97 7 140 200 274 32 64 128 256), losses := [] }

theorem u13286 : Upper (D 8) (R 8) [96,5,136,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13287 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 200 304 51 115 179 307), lower := (rows 97 7 140 200 304 32 64 128 256), losses := [] }

theorem u13287 : Upper (D 8) (R 8) [96,5,136,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13288 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 265 50 240 240 240 496), lower := (rows 97 7 140 265 50 32 64 128 256), losses := [] }

theorem u13288 : Upper (D 8) (R 8) [96,5,136,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13289 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 265 82 176 240 176 432), lower := (rows 97 7 140 265 82 32 64 128 256), losses := [] }

theorem u13289 : Upper (D 8) (R 8) [96,5,136,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13290 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 265 146 112 112 240 368), lower := (rows 97 7 140 265 146 32 64 128 256), losses := [] }

theorem u13290 : Upper (D 8) (R 8) [96,5,136,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13291 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 265 176 114 114 242 370), lower := (rows 97 7 140 265 176 32 64 128 256), losses := [] }

theorem u13291 : Upper (D 8) (R 8) [96,5,136,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13292 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 265 208 50 114 178 306), lower := (rows 97 7 140 265 208 32 64 128 256), losses := [] }

theorem u13292 : Upper (D 8) (R 8) [96,5,136,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13293 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 266 49 240 240 240 496), lower := (rows 97 7 140 266 49 32 64 128 256), losses := [] }

theorem u13293 : Upper (D 8) (R 8) [96,5,136,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13294 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 266 81 176 240 176 432), lower := (rows 97 7 140 266 81 32 64 128 256), losses := [] }

theorem u13294 : Upper (D 8) (R 8) [96,5,136,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13295 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 266 112 177 241 177 433), lower := (rows 97 7 140 266 112 32 64 128 256), losses := [] }

theorem u13295 : Upper (D 8) (R 8) [96,5,136,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13296 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 266 145 112 112 240 368), lower := (rows 97 7 140 266 145 32 64 128 256), losses := [] }

theorem u13296 : Upper (D 8) (R 8) [96,5,136,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13297 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 266 176 113 113 241 369), lower := (rows 97 7 140 266 176 32 64 128 256), losses := [] }

theorem u13297 : Upper (D 8) (R 8) [96,5,136,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13298 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 266 208 49 113 177 305), lower := (rows 97 7 140 266 208 32 64 128 256), losses := [] }

theorem u13298 : Upper (D 8) (R 8) [96,5,136,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13299 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 280 49 226 226 226 482), lower := (rows 97 7 140 280 49 32 64 128 256), losses := [] }

theorem u13299 : Upper (D 8) (R 8) [96,5,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13300 : Route 9 := (fun mask => (mask,id))

def c13300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13300 : Upper (D 8) (R 8) [96,5,136,272,34] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,34] 13 (by decide) (choices 1) [1,64,128] r13300 c13300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4301
  · exact u4302
  · exact u4303

def b13301 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 280 81 162 226 162 418), lower := (rows 97 7 140 280 81 32 64 128 256), losses := [] }

theorem u13301 : Upper (D 8) (R 8) [96,5,136,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13302 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 97 7 140 280 82 161 225 161 417), lower := (rows 97 7 140 280 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 140 284 446 32 0 128 256) }] }

theorem u13302 : Upper (D 8) (R 8) [96,5,136,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13303 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 280 112 163 227 163 419), lower := (rows 97 7 140 280 112 32 64 128 256), losses := [] }

theorem u13303 : Upper (D 8) (R 8) [96,5,136,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13304 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 280 145 98 98 226 354), lower := (rows 97 7 140 280 145 32 64 128 256), losses := [] }

theorem u13304 : Upper (D 8) (R 8) [96,5,136,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13305 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 280 146 97 97 225 353), lower := (rows 97 7 140 280 146 32 64 128 256), losses := [] }

theorem u13305 : Upper (D 8) (R 8) [96,5,136,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13306 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 280 176 99 99 227 355), lower := (rows 97 7 140 280 176 32 64 128 256), losses := [] }

theorem u13306 : Upper (D 8) (R 8) [96,5,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13307 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 280 208 35 99 163 291), lower := (rows 97 7 140 280 208 32 64 128 256), losses := [] }

theorem u13307 : Upper (D 8) (R 8) [96,5,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13308 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 296 49 242 210 210 466), lower := (rows 97 7 140 296 49 32 64 128 256), losses := [] }

theorem u13308 : Upper (D 8) (R 8) [96,5,136,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13309 : Route 9 := (fun mask => (mask,id))

def c13309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13309 : Upper (D 8) (R 8) [96,5,136,288,34] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,34] 13 (by decide) (choices 1) [1,16,64,128] r13309 c13309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4304
  · exact u4305
  · exact u4306
  · exact u4307

def b13310 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 296 81 178 242 178 434), lower := (rows 97 7 140 296 81 32 64 128 256), losses := [] }

theorem u13310 : Upper (D 8) (R 8) [96,5,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13311 : Route 9 := (fun mask => (mask,id))

def c13311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13311 : Upper (D 8) (R 8) [96,5,136,288,66] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,66] 13 (by decide) (choices 1) [1,16,128] r13311 c13311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4308
  · exact u4309
  · exact u4310

def b13312 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 296 112 179 211 147 403), lower := (rows 97 7 140 296 112 32 64 128 256), losses := [] }

theorem u13312 : Upper (D 8) (R 8) [96,5,136,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13313 : Route 9 := (fun mask => (mask,id))

def c13313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13313 : Upper (D 8) (R 8) [96,5,136,288,129] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,129] 13 (by decide) (choices 1) [2,16,64] r13313 c13313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4311
  · exact u4312
  · exact u4313

def b13314 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 296 146 113 113 241 369), lower := (rows 97 7 140 296 146 32 64 128 256), losses := [] }

theorem u13314 : Upper (D 8) (R 8) [96,5,136,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13315 : Route 9 := (fun mask => (mask,id))

def c13315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13315 : Upper (D 8) (R 8) [96,5,136,288,160] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,160] 13 (by decide) (choices 1) [1,2,16,64] r13315 c13315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4314
  · exact u4315
  · exact u4316
  · exact u4317

def r13316 : Route 9 := (fun mask => (mask,id))

def c13316 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13316 : Upper (D 8) (R 8) [96,5,136,288,192] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,192] 13 (by decide) (choices 1) [1,2,16] r13316 c13316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4318
  · exact u4319
  · exact u4320

def b13317 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 328 50 177 241 177 433), lower := (rows 97 7 140 328 50 32 64 128 256), losses := [] }

theorem u13317 : Upper (D 8) (R 8) [96,5,136,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13318 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 328 145 50 114 178 306), lower := (rows 97 7 140 328 145 32 64 128 256), losses := [] }

theorem u13318 : Upper (D 8) (R 8) [96,5,136,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13319 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 328 146 49 113 177 305), lower := (rows 97 7 140 328 146 32 64 128 256), losses := [] }

theorem u13319 : Upper (D 8) (R 8) [96,5,136,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13319
end Delivery.IrregularNine14.P08
