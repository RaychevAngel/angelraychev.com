import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0089

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15240 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 56 273 226 226 226 482), lower := (rows 193 7 44 56 273 32 64 128 256), losses := [] }

theorem u15240 : Upper (D 8) (R 8) [192,5,40,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15241 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 56 274 225 225 225 481), lower := (rows 193 7 44 56 274 32 64 128 256), losses := [] }

theorem u15241 : Upper (D 8) (R 8) [192,5,40,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15242 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 56 304 227 195 195 451), lower := (rows 193 7 44 56 304 32 64 128 256), losses := [] }

theorem u15242 : Upper (D 8) (R 8) [192,5,40,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15243 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 56 336 163 227 163 419), lower := (rows 193 7 44 56 336 32 64 128 256), losses := [] }

theorem u15243 : Upper (D 8) (R 8) [192,5,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15244 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 73 50 432 496 432 432), lower := (rows 193 7 44 73 50 32 64 128 256), losses := [] }

theorem u15244 : Upper (D 8) (R 8) [192,5,40,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15245 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 73 146 304 368 432 304), lower := (rows 193 7 44 73 146 32 64 128 256), losses := [] }

theorem u15245 : Upper (D 8) (R 8) [192,5,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15246 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 73 176 306 370 434 306), lower := (rows 193 7 44 73 176 32 64 128 256), losses := [] }

theorem u15246 : Upper (D 8) (R 8) [192,5,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15247 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 73 274 176 240 176 432), lower := (rows 193 7 44 73 274 32 64 128 256), losses := [] }

theorem u15247 : Upper (D 8) (R 8) [192,5,40,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15248 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 73 304 178 242 178 434), lower := (rows 193 7 44 73 304 32 64 128 256), losses := [] }

theorem u15248 : Upper (D 8) (R 8) [192,5,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15249 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 73 400 50 114 178 306), lower := (rows 193 7 44 73 400 32 64 128 256), losses := [] }

theorem u15249 : Upper (D 8) (R 8) [192,5,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15250 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 74 49 432 496 432 432), lower := (rows 193 7 44 74 49 32 64 128 256), losses := [] }

theorem u15250 : Upper (D 8) (R 8) [192,5,40,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15251 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 74 176 305 369 433 305), lower := (rows 193 7 44 74 176 32 64 128 256), losses := [] }

theorem u15251 : Upper (D 8) (R 8) [192,5,40,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15252 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 74 273 176 240 176 432), lower := (rows 193 7 44 74 273 32 64 128 256), losses := [] }

theorem u15252 : Upper (D 8) (R 8) [192,5,40,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15253 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 74 304 177 241 177 433), lower := (rows 193 7 44 74 304 32 64 128 256), losses := [] }

theorem u15253 : Upper (D 8) (R 8) [192,5,40,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15254 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 74 400 49 113 177 305), lower := (rows 193 7 44 74 400 32 64 128 256), losses := [] }

theorem u15254 : Upper (D 8) (R 8) [192,5,40,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15255 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 49 418 482 418 418), lower := (rows 193 7 44 88 49 32 64 128 256), losses := [] }

theorem u15255 : Upper (D 8) (R 8) [192,5,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15256 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 50 417 481 417 417), lower := (rows 193 7 44 88 50 32 64 128 256), losses := [] }

theorem u15256 : Upper (D 8) (R 8) [192,5,40,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15257 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 146 289 353 417 289), lower := (rows 193 7 44 88 146 32 64 128 256), losses := [] }

theorem u15257 : Upper (D 8) (R 8) [192,5,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15258 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 176 291 355 419 291), lower := (rows 193 7 44 88 176 32 64 128 256), losses := [] }

theorem u15258 : Upper (D 8) (R 8) [192,5,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15259 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 273 162 226 162 418), lower := (rows 193 7 44 88 273 32 64 128 256), losses := [] }

theorem u15259 : Upper (D 8) (R 8) [192,5,40,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15260 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 274 161 225 161 417), lower := (rows 193 7 44 88 274 32 64 128 256), losses := [] }

theorem u15260 : Upper (D 8) (R 8) [192,5,40,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15261 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 304 163 227 163 419), lower := (rows 193 7 44 88 304 32 64 128 256), losses := [] }

theorem u15261 : Upper (D 8) (R 8) [192,5,40,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15262 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 400 35 99 163 291), lower := (rows 193 7 44 88 400 32 64 128 256), losses := [] }

theorem u15262 : Upper (D 8) (R 8) [192,5,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15263 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 49 434 466 402 402), lower := (rows 193 7 44 104 49 32 64 128 256), losses := [] }

theorem u15263 : Upper (D 8) (R 8) [192,5,40,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15264 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 50 433 465 401 401), lower := (rows 193 7 44 104 50 32 64 128 256), losses := [] }

theorem u15264 : Upper (D 8) (R 8) [192,5,40,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15265 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 146 305 369 433 305), lower := (rows 193 7 44 104 146 32 64 128 256), losses := [] }

theorem u15265 : Upper (D 8) (R 8) [192,5,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15266 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 176 307 339 403 275), lower := (rows 193 7 44 104 176 32 64 128 256), losses := [] }

theorem u15266 : Upper (D 8) (R 8) [192,5,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15267 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 273 178 242 178 434), lower := (rows 193 7 44 104 273 32 64 128 256), losses := [] }

theorem u15267 : Upper (D 8) (R 8) [192,5,40,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15268 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 274 177 241 177 433), lower := (rows 193 7 44 104 274 32 64 128 256), losses := [] }

theorem u15268 : Upper (D 8) (R 8) [192,5,40,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15269 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 304 179 211 147 403), lower := (rows 193 7 44 104 304 32 64 128 256), losses := [] }

theorem u15269 : Upper (D 8) (R 8) [192,5,40,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15270 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 400 51 115 179 307), lower := (rows 193 7 44 104 400 32 64 128 256), losses := [] }

theorem u15270 : Upper (D 8) (R 8) [192,5,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15271 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 44 200 49 306 370 434 306), lower := (rows 193 7 44 200 49 32 64 128 256), losses := [] }

theorem u15271 : Upper (D 8) (R 8) [192,5,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15272 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 44 200 50 305 369 433 305), lower := (rows 193 7 44 200 50 32 64 128 256), losses := [] }

theorem u15272 : Upper (D 8) (R 8) [192,5,40,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15273 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 44 200 273 50 114 178 306), lower := (rows 193 7 44 200 273 32 64 128 256), losses := [] }

theorem u15273 : Upper (D 8) (R 8) [192,5,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15274 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 44 200 274 49 113 177 305), lower := (rows 193 7 44 200 274 32 64 128 256), losses := [] }

theorem u15274 : Upper (D 8) (R 8) [192,5,40,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15275 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 44 200 304 51 115 179 307), lower := (rows 193 7 44 200 304 32 64 128 256), losses := [] }

theorem u15275 : Upper (D 8) (R 8) [192,5,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15276 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 265 50 240 240 240 496), lower := (rows 193 7 44 265 50 32 64 128 256), losses := [] }

theorem u15276 : Upper (D 8) (R 8) [192,5,40,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15277 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 265 82 176 240 176 432), lower := (rows 193 7 44 265 82 32 64 128 256), losses := [] }

theorem u15277 : Upper (D 8) (R 8) [192,5,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15278 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 265 112 178 242 178 434), lower := (rows 193 7 44 265 112 32 64 128 256), losses := [] }

theorem u15278 : Upper (D 8) (R 8) [192,5,40,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15279 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u15279 : Upper (D 8) (R 8) [192,5,40,258,33] 13 := by
  apply FastRouting.sound _ _ [192,5,40,258,33] 13 (by decide) (choices 1) [16,64] r15279 c15279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5365
  · exact u5366

def b15280 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 266 81 176 240 176 432), lower := (rows 193 7 44 266 81 32 64 128 256), losses := [] }

theorem u15280 : Upper (D 8) (R 8) [192,5,40,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15281 : Route 9 := (fun mask => (mask,id))

def c15281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15281 : Upper (D 8) (R 8) [192,5,40,258,96] 13 := by
  apply FastRouting.sound _ _ [192,5,40,258,96] 13 (by decide) (choices 1) [1,16,128] r15281 c15281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5367
  · exact u5368
  · exact u5369

def b15282 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 266 208 49 113 177 305), lower := (rows 193 7 44 266 208 32 64 128 256), losses := [] }

theorem u15282 : Upper (D 8) (R 8) [192,5,40,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15283 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15283 : Upper (D 8) (R 8) [192,5,40,272,33] 13 := by
  apply FastRouting.sound _ _ [192,5,40,272,33] 13 (by decide) (choices 1) [2,64] r15283 c15283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5370
  · exact u5371

def r15284 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15284 : Upper (D 8) (R 8) [192,5,40,272,34] 13 := by
  apply FastRouting.sound _ _ [192,5,40,272,34] 13 (by decide) (choices 1) [1,64] r15284 c15284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5372
  · exact u5373

def b15285 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 280 81 162 226 162 418), lower := (rows 193 7 44 280 81 32 64 128 256), losses := [] }

theorem u15285 : Upper (D 8) (R 8) [192,5,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15286 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 193 7 44 280 82 161 225 161 417), lower := (rows 193 7 44 280 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 44 284 446 32 0 128 256) }] }

theorem u15286 : Upper (D 8) (R 8) [192,5,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15287 : Route 9 := (fun mask => (mask,id))

def c15287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15287 : Upper (D 8) (R 8) [192,5,40,272,96] 13 := by
  apply FastRouting.sound _ _ [192,5,40,272,96] 13 (by decide) (choices 1) [1,2,128] r15287 c15287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5374
  · exact u5375
  · exact u5376

def b15288 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 280 208 35 99 163 291), lower := (rows 193 7 44 280 208 32 64 128 256), losses := [] }

theorem u15288 : Upper (D 8) (R 8) [192,5,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15289 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 296 49 242 210 210 466), lower := (rows 193 7 44 296 49 32 64 128 256), losses := [] }

theorem u15289 : Upper (D 8) (R 8) [192,5,40,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15290 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 296 50 241 209 209 465), lower := (rows 193 7 44 296 50 32 64 128 256), losses := [] }

theorem u15290 : Upper (D 8) (R 8) [192,5,40,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15291 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 296 82 177 241 177 433), lower := (rows 193 7 44 296 82 32 64 128 256), losses := [] }

theorem u15291 : Upper (D 8) (R 8) [192,5,40,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15292 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 296 112 179 211 147 403), lower := (rows 193 7 44 296 112 32 64 128 256), losses := [] }

theorem u15292 : Upper (D 8) (R 8) [192,5,40,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15293 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 328 49 178 242 178 434), lower := (rows 193 7 44 328 49 32 64 128 256), losses := [] }

theorem u15293 : Upper (D 8) (R 8) [192,5,40,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15294 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 328 50 177 241 177 433), lower := (rows 193 7 44 328 50 32 64 128 256), losses := [] }

theorem u15294 : Upper (D 8) (R 8) [192,5,40,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15295 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 328 146 49 113 177 305), lower := (rows 193 7 44 328 146 32 64 128 256), losses := [] }

theorem u15295 : Upper (D 8) (R 8) [192,5,40,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15296 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 328 176 51 115 179 307), lower := (rows 193 7 44 328 176 32 64 128 256), losses := [] }

theorem u15296 : Upper (D 8) (R 8) [192,5,40,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15297 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 26 56 416 480 416 416), lower := (rows 193 7 69 26 56 32 64 128 256), losses := [] }

theorem u15297 : Upper (D 8) (R 8) [192,5,65,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15298 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 26 176 296 360 424 296), lower := (rows 193 7 69 26 176 32 64 128 256), losses := [] }

theorem u15298 : Upper (D 8) (R 8) [192,5,65,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15299 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 26 280 160 224 160 416), lower := (rows 193 7 69 26 280 32 64 128 256), losses := [] }

theorem u15299 : Upper (D 8) (R 8) [192,5,65,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15299
end Delivery.IrregularNine14.P08
