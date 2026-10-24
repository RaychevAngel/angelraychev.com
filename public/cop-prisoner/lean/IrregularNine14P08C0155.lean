import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0039

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9300 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 400 49 113 177 305), lower := (rows 35 194 13 76 400 32 64 128 256), losses := [] }

theorem u9300 : Upper (D 8) (R 8) [34,192,9,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9301 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 88 52 417 481 417 417), lower := (rows 35 194 13 88 52 32 64 128 256), losses := [] }

theorem u9301 : Upper (D 8) (R 8) [34,192,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9302 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 88 148 289 353 417 289), lower := (rows 35 194 13 88 148 32 64 128 256), losses := [] }

theorem u9302 : Upper (D 8) (R 8) [34,192,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9303 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 88 176 293 357 421 293), lower := (rows 35 194 13 88 176 32 64 128 256), losses := [] }

theorem u9303 : Upper (D 8) (R 8) [34,192,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9304 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 88 273 164 228 164 420), lower := (rows 35 194 13 88 273 32 64 128 256), losses := [] }

theorem u9304 : Upper (D 8) (R 8) [34,192,9,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9305 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 88 276 161 225 161 417), lower := (rows 35 194 13 88 276 32 64 128 256), losses := [] }

theorem u9305 : Upper (D 8) (R 8) [34,192,9,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9306 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 88 304 165 229 165 421), lower := (rows 35 194 13 88 304 32 64 128 256), losses := [] }

theorem u9306 : Upper (D 8) (R 8) [34,192,9,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9307 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 88 400 37 101 165 293), lower := (rows 35 194 13 88 400 32 64 128 256), losses := [] }

theorem u9307 : Upper (D 8) (R 8) [34,192,9,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9308 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 104 52 433 465 401 401), lower := (rows 35 194 13 104 52 32 64 128 256), losses := [] }

theorem u9308 : Upper (D 8) (R 8) [34,192,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9309 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 104 148 305 369 433 305), lower := (rows 35 194 13 104 148 32 64 128 256), losses := [] }

theorem u9309 : Upper (D 8) (R 8) [34,192,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9310 : PairBound 9 := { available := 277, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 104 176 309 341 405 277), lower := (rows 35 194 13 104 176 32 64 128 256), losses := [] }

theorem u9310 : Upper (D 8) (R 8) [34,192,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9311 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 104 273 180 244 180 436), lower := (rows 35 194 13 104 273 32 64 128 256), losses := [] }

theorem u9311 : Upper (D 8) (R 8) [34,192,9,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9312 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 104 276 177 241 177 433), lower := (rows 35 194 13 104 276 32 64 128 256), losses := [] }

theorem u9312 : Upper (D 8) (R 8) [34,192,9,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9313 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 104 304 181 213 149 405), lower := (rows 35 194 13 104 304 32 64 128 256), losses := [] }

theorem u9313 : Upper (D 8) (R 8) [34,192,9,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9314 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 104 400 53 117 181 309), lower := (rows 35 194 13 104 400 32 64 128 256), losses := [] }

theorem u9314 : Upper (D 8) (R 8) [34,192,9,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9315 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 52 305 369 433 305), lower := (rows 35 194 13 200 52 32 64 128 256), losses := [] }

theorem u9315 : Upper (D 8) (R 8) [34,192,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9316 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 273 52 116 180 308), lower := (rows 35 194 13 200 273 32 64 128 256), losses := [] }

theorem u9316 : Upper (D 8) (R 8) [34,192,9,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9317 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 276 49 113 177 305), lower := (rows 35 194 13 200 276 32 64 128 256), losses := [] }

theorem u9317 : Upper (D 8) (R 8) [34,192,9,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9318 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 304 53 117 181 309), lower := (rows 35 194 13 200 304 32 64 128 256), losses := [] }

theorem u9318 : Upper (D 8) (R 8) [34,192,9,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9319 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 265 52 240 240 240 496), lower := (rows 35 194 13 265 52 32 64 128 256), losses := [] }

theorem u9319 : Upper (D 8) (R 8) [34,192,9,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9320 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 265 84 176 240 176 432), lower := (rows 35 194 13 265 84 32 64 128 256), losses := [] }

theorem u9320 : Upper (D 8) (R 8) [34,192,9,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9321 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 265 112 180 244 180 436), lower := (rows 35 194 13 265 112 32 64 128 256), losses := [] }

theorem u9321 : Upper (D 8) (R 8) [34,192,9,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9322 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 268 49 240 240 240 496), lower := (rows 35 194 13 268 49 32 64 128 256), losses := [] }

theorem u9322 : Upper (D 8) (R 8) [34,192,9,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9323 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 268 81 176 240 176 432), lower := (rows 35 194 13 268 81 32 64 128 256), losses := [] }

theorem u9323 : Upper (D 8) (R 8) [34,192,9,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9324 : Route 9 := (fun mask => (mask,id))

def c9324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9324 : Upper (D 8) (R 8) [34,192,9,260,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,96] 13 (by decide) (choices 1) [1,16,128] r9324 c9324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2341
  · exact u2342
  · exact u2343

def b9325 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 13 268 208 49 113 177 305), lower := (rows 35 194 13 268 208 32 64 128 256), losses := [] }

theorem u9325 : Upper (D 8) (R 8) [34,192,9,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9326 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 280 49 228 228 228 484), lower := (rows 35 194 13 280 49 32 64 128 256), losses := [] }

theorem u9326 : Upper (D 8) (R 8) [34,192,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9327 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9327 : Upper (D 8) (R 8) [34,192,9,272,36] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,36] 13 (by decide) (choices 1) [1,64] r9327 c9327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2344
  · exact u2345

def b9328 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 280 81 164 228 164 420), lower := (rows 35 194 13 280 81 32 64 128 256), losses := [] }

theorem u9328 : Upper (D 8) (R 8) [34,192,9,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9329 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 280 84 161 225 161 417), lower := (rows 35 194 13 280 84 32 64 128 256), losses := [] }

theorem u9329 : Upper (D 8) (R 8) [34,192,9,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9330 : Route 9 := (fun mask => (mask,id))

def c9330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9330 : Upper (D 8) (R 8) [34,192,9,272,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,96] 13 (by decide) (choices 1) [1,4,128] r9330 c9330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2346
  · exact u2347
  · exact u2348

def b9331 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 13 280 208 37 101 165 293), lower := (rows 35 194 13 280 208 32 64 128 256), losses := [] }

theorem u9331 : Upper (D 8) (R 8) [34,192,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9332 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 296 49 244 212 212 468), lower := (rows 35 194 13 296 49 32 64 128 256), losses := [] }

theorem u9332 : Upper (D 8) (R 8) [34,192,9,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9333 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u9333 : Upper (D 8) (R 8) [34,192,9,288,36] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,36] 13 (by decide) (choices 1) [1,16,64] r9333 c9333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2349
  · exact u2350
  · exact u2351

def b9334 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 296 81 180 244 180 436), lower := (rows 35 194 13 296 81 32 64 128 256), losses := [] }

theorem u9334 : Upper (D 8) (R 8) [34,192,9,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9335 : Route 9 := (fun mask => (mask,id))

def c9335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9335 : Upper (D 8) (R 8) [34,192,9,288,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,68] 13 (by decide) (choices 1) [1,16,128] r9335 c9335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2352
  · exact u2353
  · exact u2354

def r9336 : Route 9 := (fun mask => (mask,id))

def c9336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9336 : Upper (D 8) (R 8) [34,192,9,288,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,96] 13 (by decide) (choices 1) [1,4,16,128] r9336 c9336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2355
  · exact u2356
  · exact u2357
  · exact u2358

def b9337 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 13 296 208 53 117 181 309), lower := (rows 35 194 13 296 208 32 64 128 256), losses := [] }

theorem u9337 : Upper (D 8) (R 8) [34,192,9,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9338 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 328 52 177 241 177 433), lower := (rows 35 194 13 328 52 32 64 128 256), losses := [] }

theorem u9338 : Upper (D 8) (R 8) [34,192,9,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9339 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 328 148 49 113 177 305), lower := (rows 35 194 13 328 148 32 64 128 256), losses := [] }

theorem u9339 : Upper (D 8) (R 8) [34,192,9,320,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9340 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 328 176 53 117 181 309), lower := (rows 35 194 13 328 176 32 64 128 256), losses := [] }

theorem u9340 : Upper (D 8) (R 8) [34,192,9,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9341 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 41 52 481 449 449 449), lower := (rows 35 194 28 41 52 32 64 128 256), losses := [] }

theorem u9341 : Upper (D 8) (R 8) [34,192,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9342 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 28 41 112 421 453 389 389), lower := (rows 35 194 28 41 112 32 64 128 256), losses := [] }

theorem u9342 : Upper (D 8) (R 8) [34,192,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9343 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 28 41 273 228 228 228 484), lower := (rows 35 194 28 41 273 32 64 128 256), losses := [] }

theorem u9343 : Upper (D 8) (R 8) [34,192,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9344 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 28 41 276 225 225 225 481), lower := (rows 35 194 28 41 276 32 64 128 256), losses := [] }

theorem u9344 : Upper (D 8) (R 8) [34,192,24,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9345 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 28 41 304 229 197 197 453), lower := (rows 35 194 28 41 304 32 64 128 256), losses := [] }

theorem u9345 : Upper (D 8) (R 8) [34,192,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9346 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 28 41 336 165 229 165 421), lower := (rows 35 194 28 41 336 32 64 128 256), losses := [] }

theorem u9346 : Upper (D 8) (R 8) [34,192,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9347 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 44 81 417 481 417 417), lower := (rows 35 194 28 44 81 32 64 128 256), losses := [] }

theorem u9347 : Upper (D 8) (R 8) [34,192,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9348 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 28 44 112 417 449 385 385), lower := (rows 35 194 28 44 112 32 64 128 256), losses := [] }

theorem u9348 : Upper (D 8) (R 8) [34,192,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9349 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 28 44 208 289 353 417 289), lower := (rows 35 194 28 44 208 32 64 128 256), losses := [] }

theorem u9349 : Upper (D 8) (R 8) [34,192,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9350 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9350 : Upper (D 8) (R 8) [34,192,24,36,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,36,257] 13 (by decide) (choices 1) [1,64] r9350 c9350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2359
  · exact u2360

def b9351 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 28 44 304 225 193 193 449), lower := (rows 35 194 28 44 304 32 64 128 256), losses := [] }

theorem u9351 : Upper (D 8) (R 8) [34,192,24,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9352 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 44 336 161 225 161 417), lower := (rows 35 194 28 44 336 32 64 128 256), losses := [] }

theorem u9352 : Upper (D 8) (R 8) [34,192,24,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9353 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 176 293 357 421 293), lower := (rows 35 194 28 73 176 32 64 128 256), losses := [] }

theorem u9353 : Upper (D 8) (R 8) [34,192,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9354 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 273 164 228 164 420), lower := (rows 35 194 28 73 273 32 64 128 256), losses := [] }

theorem u9354 : Upper (D 8) (R 8) [34,192,24,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9355 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 276 161 225 161 417), lower := (rows 35 194 28 73 276 32 64 128 256), losses := [] }

theorem u9355 : Upper (D 8) (R 8) [34,192,24,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9356 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 304 165 229 165 421), lower := (rows 35 194 28 73 304 32 64 128 256), losses := [] }

theorem u9356 : Upper (D 8) (R 8) [34,192,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9357 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 73 400 37 101 165 293), lower := (rows 35 194 28 73 400 32 64 128 256), losses := [] }

theorem u9357 : Upper (D 8) (R 8) [34,192,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9358 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 76 176 289 353 417 289), lower := (rows 35 194 28 76 176 32 64 128 256), losses := [] }

theorem u9358 : Upper (D 8) (R 8) [34,192,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9359 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 76 273 161 225 161 417), lower := (rows 35 194 28 76 273 32 64 128 256), losses := [] }

theorem u9359 : Upper (D 8) (R 8) [34,192,24,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9359
end Delivery.IrregularNine14.P08
