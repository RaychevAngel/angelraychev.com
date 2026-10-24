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

def b13200 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 26 145 352 352 480 352), lower := (rows 97 7 140 26 145 32 64 128 256), losses := [] }

theorem u13200 : Upper (D 8) (R 8) [96,5,136,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13201 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 26 176 353 353 481 353), lower := (rows 97 7 140 26 176 32 64 128 256), losses := [] }

theorem u13201 : Upper (D 8) (R 8) [96,5,136,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13202 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 26 208 289 353 417 289), lower := (rows 97 7 140 26 208 32 64 128 256), losses := [] }

theorem u13202 : Upper (D 8) (R 8) [96,5,136,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13203 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 140 26 273 224 224 224 480), lower := (rows 97 7 140 26 273 32 64 128 256), losses := [] }

theorem u13203 : Upper (D 8) (R 8) [96,5,136,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13204 : Route 9 := (fun mask => (mask,id))

def c13204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13204 : Upper (D 8) (R 8) [96,5,136,18,288] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,288] 13 (by decide) (choices 1) [1,64,128] r13204 c13204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4279
  · exact u4280
  · exact u4281

def b13205 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 97 7 140 26 336 161 225 161 417), lower := (rows 97 7 140 26 336 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 140 446 272 32 0 128 256) }] }

theorem u13205 : Upper (D 8) (R 8) [96,5,136,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13206 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 26 400 97 97 225 353), lower := (rows 97 7 140 26 400 32 64 128 256), losses := [] }

theorem u13206 : Upper (D 8) (R 8) [96,5,136,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13207 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 50 496 464 464 464), lower := (rows 97 7 140 41 50 32 64 128 256), losses := [] }

theorem u13207 : Upper (D 8) (R 8) [96,5,136,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13208 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 82 432 496 432 432), lower := (rows 97 7 140 41 82 32 64 128 256), losses := [] }

theorem u13208 : Upper (D 8) (R 8) [96,5,136,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13209 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 176 370 338 466 338), lower := (rows 97 7 140 41 176 32 64 128 256), losses := [] }

theorem u13209 : Upper (D 8) (R 8) [96,5,136,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13210 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 208 306 370 434 306), lower := (rows 97 7 140 41 208 32 64 128 256), losses := [] }

theorem u13210 : Upper (D 8) (R 8) [96,5,136,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13211 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 274 240 240 240 496), lower := (rows 97 7 140 41 274 32 64 128 256), losses := [] }

theorem u13211 : Upper (D 8) (R 8) [96,5,136,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13212 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 304 242 210 210 466), lower := (rows 97 7 140 41 304 32 64 128 256), losses := [] }

theorem u13212 : Upper (D 8) (R 8) [96,5,136,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13213 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 336 178 242 178 434), lower := (rows 97 7 140 41 336 32 64 128 256), losses := [] }

theorem u13213 : Upper (D 8) (R 8) [96,5,136,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13214 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 400 114 114 242 370), lower := (rows 97 7 140 41 400 32 64 128 256), losses := [] }

theorem u13214 : Upper (D 8) (R 8) [96,5,136,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13215 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 42 49 496 464 464 464), lower := (rows 97 7 140 42 49 32 64 128 256), losses := [] }

theorem u13215 : Upper (D 8) (R 8) [96,5,136,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13216 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 42 81 432 496 432 432), lower := (rows 97 7 140 42 81 32 64 128 256), losses := [] }

theorem u13216 : Upper (D 8) (R 8) [96,5,136,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13217 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 42 112 433 465 401 401), lower := (rows 97 7 140 42 112 32 64 128 256), losses := [] }

theorem u13217 : Upper (D 8) (R 8) [96,5,136,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13218 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 42 145 368 368 496 368), lower := (rows 97 7 140 42 145 32 64 128 256), losses := [] }

theorem u13218 : Upper (D 8) (R 8) [96,5,136,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13219 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 42 176 369 337 465 337), lower := (rows 97 7 140 42 176 32 64 128 256), losses := [] }

theorem u13219 : Upper (D 8) (R 8) [96,5,136,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13220 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 42 208 305 369 433 305), lower := (rows 97 7 140 42 208 32 64 128 256), losses := [] }

theorem u13220 : Upper (D 8) (R 8) [96,5,136,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13221 : Route 9 := (fun mask => (mask,id))

def c13221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13221 : Upper (D 8) (R 8) [96,5,136,34,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,257] 13 (by decide) (choices 1) [16,64,128] r13221 c13221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4282
  · exact u4283
  · exact u4284

def r13222 : Route 9 := (fun mask => (mask,id))

def c13222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13222 : Upper (D 8) (R 8) [96,5,136,34,288] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,288] 13 (by decide) (choices 1) [1,16,64,128] r13222 c13222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4285
  · exact u4286
  · exact u4287
  · exact u4288

def r13223 : Route 9 := (fun mask => (mask,id))

def c13223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13223 : Upper (D 8) (R 8) [96,5,136,34,320] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,320] 13 (by decide) (choices 1) [1,16,128] r13223 c13223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4289
  · exact u4290
  · exact u4291

def b13224 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 42 400 113 113 241 369), lower := (rows 97 7 140 42 400 32 64 128 256), losses := [] }

theorem u13224 : Upper (D 8) (R 8) [96,5,136,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13225 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 56 49 482 450 450 450), lower := (rows 97 7 140 56 49 32 64 128 256), losses := [] }

theorem u13225 : Upper (D 8) (R 8) [96,5,136,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13226 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 56 50 481 449 449 449), lower := (rows 97 7 140 56 50 32 64 128 256), losses := [] }

theorem u13226 : Upper (D 8) (R 8) [96,5,136,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13227 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 56 81 418 482 418 418), lower := (rows 97 7 140 56 81 32 64 128 256), losses := [] }

theorem u13227 : Upper (D 8) (R 8) [96,5,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13228 : PairBound 9 := { available := 417, camps := [], pairs := [(2,6)], upper := (rows 97 7 140 56 82 417 481 417 417), lower := (rows 97 7 140 56 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 140 60 446 32 0 128 256) }] }

theorem u13228 : Upper (D 8) (R 8) [96,5,136,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13229 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 56 112 419 451 387 387), lower := (rows 97 7 140 56 112 32 64 128 256), losses := [] }

theorem u13229 : Upper (D 8) (R 8) [96,5,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13230 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 145 354 354 482 354), lower := (rows 97 7 140 56 145 32 64 128 256), losses := [] }

theorem u13230 : Upper (D 8) (R 8) [96,5,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13231 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 146 353 353 481 353), lower := (rows 97 7 140 56 146 32 64 128 256), losses := [] }

theorem u13231 : Upper (D 8) (R 8) [96,5,136,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13232 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 140 56 176 355 323 451 323), lower := (rows 97 7 140 56 176 32 64 128 256), losses := [] }

theorem u13232 : Upper (D 8) (R 8) [96,5,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13233 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 208 291 355 419 291), lower := (rows 97 7 140 56 208 32 64 128 256), losses := [] }

theorem u13233 : Upper (D 8) (R 8) [96,5,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13234 : Route 9 := (fun mask => (mask,id))

def c13234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13234 : Upper (D 8) (R 8) [96,5,136,48,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,257] 13 (by decide) (choices 1) [2,64,128] r13234 c13234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4292
  · exact u4293
  · exact u4294

def r13235 : Route 9 := (fun mask => (mask,id))

def c13235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13235 : Upper (D 8) (R 8) [96,5,136,48,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,258] 13 (by decide) (choices 1) [1,64,128] r13235 c13235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4295
  · exact u4296
  · exact u4297

def b13236 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 56 304 227 195 195 451), lower := (rows 97 7 140 56 304 32 64 128 256), losses := [] }

theorem u13236 : Upper (D 8) (R 8) [96,5,136,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13237 : Route 9 := (fun mask => (mask,id))

def c13237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13237 : Upper (D 8) (R 8) [96,5,136,48,320] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,320] 13 (by decide) (choices 1) [1,2,128] r13237 c13237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4298
  · exact u4299
  · exact u4300

def b13238 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 400 99 99 227 355), lower := (rows 97 7 140 56 400 32 64 128 256), losses := [] }

theorem u13238 : Upper (D 8) (R 8) [96,5,136,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13239 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 73 50 432 496 432 432), lower := (rows 97 7 140 73 50 32 64 128 256), losses := [] }

theorem u13239 : Upper (D 8) (R 8) [96,5,136,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13240 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 73 176 306 370 434 306), lower := (rows 97 7 140 73 176 32 64 128 256), losses := [] }

theorem u13240 : Upper (D 8) (R 8) [96,5,136,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13241 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 73 274 176 240 176 432), lower := (rows 97 7 140 73 274 32 64 128 256), losses := [] }

theorem u13241 : Upper (D 8) (R 8) [96,5,136,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13242 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 73 304 178 242 178 434), lower := (rows 97 7 140 73 304 32 64 128 256), losses := [] }

theorem u13242 : Upper (D 8) (R 8) [96,5,136,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13243 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 73 400 50 114 178 306), lower := (rows 97 7 140 73 400 32 64 128 256), losses := [] }

theorem u13243 : Upper (D 8) (R 8) [96,5,136,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13244 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 74 145 304 368 432 304), lower := (rows 97 7 140 74 145 32 64 128 256), losses := [] }

theorem u13244 : Upper (D 8) (R 8) [96,5,136,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13245 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 74 176 305 369 433 305), lower := (rows 97 7 140 74 176 32 64 128 256), losses := [] }

theorem u13245 : Upper (D 8) (R 8) [96,5,136,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13246 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 74 273 176 240 176 432), lower := (rows 97 7 140 74 273 32 64 128 256), losses := [] }

theorem u13246 : Upper (D 8) (R 8) [96,5,136,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13247 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 74 304 177 241 177 433), lower := (rows 97 7 140 74 304 32 64 128 256), losses := [] }

theorem u13247 : Upper (D 8) (R 8) [96,5,136,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13248 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 74 400 49 113 177 305), lower := (rows 97 7 140 74 400 32 64 128 256), losses := [] }

theorem u13248 : Upper (D 8) (R 8) [96,5,136,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13249 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 88 50 417 481 417 417), lower := (rows 97 7 140 88 50 32 64 128 256), losses := [] }

theorem u13249 : Upper (D 8) (R 8) [96,5,136,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13250 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 88 145 290 354 418 290), lower := (rows 97 7 140 88 145 32 64 128 256), losses := [] }

theorem u13250 : Upper (D 8) (R 8) [96,5,136,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13251 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 88 146 289 353 417 289), lower := (rows 97 7 140 88 146 32 64 128 256), losses := [] }

theorem u13251 : Upper (D 8) (R 8) [96,5,136,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13252 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 88 176 291 355 419 291), lower := (rows 97 7 140 88 176 32 64 128 256), losses := [] }

theorem u13252 : Upper (D 8) (R 8) [96,5,136,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13253 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 88 273 162 226 162 418), lower := (rows 97 7 140 88 273 32 64 128 256), losses := [] }

theorem u13253 : Upper (D 8) (R 8) [96,5,136,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13254 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 88 274 161 225 161 417), lower := (rows 97 7 140 88 274 32 64 128 256), losses := [] }

theorem u13254 : Upper (D 8) (R 8) [96,5,136,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13255 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 88 304 163 227 163 419), lower := (rows 97 7 140 88 304 32 64 128 256), losses := [] }

theorem u13255 : Upper (D 8) (R 8) [96,5,136,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13256 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 88 400 35 99 163 291), lower := (rows 97 7 140 88 400 32 64 128 256), losses := [] }

theorem u13256 : Upper (D 8) (R 8) [96,5,136,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13257 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 50 433 465 401 401), lower := (rows 97 7 140 104 50 32 64 128 256), losses := [] }

theorem u13257 : Upper (D 8) (R 8) [96,5,136,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13258 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 145 306 370 434 306), lower := (rows 97 7 140 104 145 32 64 128 256), losses := [] }

theorem u13258 : Upper (D 8) (R 8) [96,5,136,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13259 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 176 307 339 403 275), lower := (rows 97 7 140 104 176 32 64 128 256), losses := [] }

theorem u13259 : Upper (D 8) (R 8) [96,5,136,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13259
end Delivery.IrregularNine14.P08
