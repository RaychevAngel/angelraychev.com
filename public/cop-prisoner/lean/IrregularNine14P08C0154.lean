import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0038
import IrregularNine14P08C0039

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9240 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 56 81 169 233 169 425), lower := (rows 35 70 388 56 81 32 64 128 256), losses := [] }

theorem u9240 : Upper (D 8) (R 8) [34,68,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9241 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 56 88 161 225 161 417), lower := (rows 35 70 388 56 88 32 64 128 256), losses := [] }

theorem u9241 : Upper (D 8) (R 8) [34,68,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9242 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 388 56 112 169 201 137 393), lower := (rows 35 70 388 56 112 32 64 128 256), losses := [] }

theorem u9242 : Upper (D 8) (R 8) [34,68,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9243 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 388 56 145 105 105 233 361), lower := (rows 35 70 388 56 145 32 64 128 256), losses := [] }

theorem u9243 : Upper (D 8) (R 8) [34,68,384,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9244 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 56 152 97 97 225 353), lower := (rows 35 70 388 56 152 32 64 128 256), losses := [] }

theorem u9244 : Upper (D 8) (R 8) [34,68,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9245 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 388 56 176 105 73 201 329), lower := (rows 35 70 388 56 176 32 64 128 256), losses := [] }

theorem u9245 : Upper (D 8) (R 8) [34,68,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9246 : Route 9 := (fun mask => (mask,id))

def c9246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9246 : Upper (D 8) (R 8) [34,68,384,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,192] 13 (by decide) (choices 1) [1,8] r9246 c9246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2325
  · exact u2326

def b9247 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 73 152 49 113 177 305), lower := (rows 35 70 388 73 152 32 64 128 256), losses := [] }

theorem u9247 : Upper (D 8) (R 8) [34,68,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9248 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 73 176 57 121 185 313), lower := (rows 35 70 388 73 176 32 64 128 256), losses := [] }

theorem u9248 : Upper (D 8) (R 8) [34,68,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9249 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 388 88 145 41 105 169 297), lower := (rows 35 70 388 88 145 32 64 128 256), losses := [] }

theorem u9249 : Upper (D 8) (R 8) [34,68,384,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9250 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 88 152 33 97 161 289), lower := (rows 35 70 388 88 152 32 64 128 256), losses := [] }

theorem u9250 : Upper (D 8) (R 8) [34,68,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9251 : Route 9 := (fun mask => (mask,id))

def c9251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9251 : Upper (D 8) (R 8) [34,68,384,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,160] 13 (by decide) (choices 1) [1,8] r9251 c9251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2327
  · exact u2328

def b9252 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 388 104 145 57 121 185 313), lower := (rows 35 70 388 104 145 32 64 128 256), losses := [] }

theorem u9252 : Upper (D 8) (R 8) [34,68,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9253 : Route 9 := (fun mask => (mask,id))

def c9253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9253 : Upper (D 8) (R 8) [34,68,384,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,136] 13 (by decide) (choices 1) [1,16] r9253 c9253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2329
  · exact u2330

def r9254 : Route 9 := (fun mask => (mask,id))

def c9254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9254 : Upper (D 8) (R 8) [34,68,384,96,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,160] 13 (by decide) (choices 1) [1,8,16] r9254 c9254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2331
  · exact u2332
  · exact u2333

def b9255 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 112 432 496 432 432), lower := (rows 35 194 13 13 112 32 64 128 256), losses := [] }

theorem u9255 : Upper (D 8) (R 8) [34,192,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9256 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 304 240 240 240 496), lower := (rows 35 194 13 13 304 32 64 128 256), losses := [] }

theorem u9256 : Upper (D 8) (R 8) [34,192,9,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9257 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 336 176 240 176 432), lower := (rows 35 194 13 13 336 32 64 128 256), losses := [] }

theorem u9257 : Upper (D 8) (R 8) [34,192,9,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9258 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 25 52 480 480 480 480), lower := (rows 35 194 13 25 52 32 64 128 256), losses := [] }

theorem u9258 : Upper (D 8) (R 8) [34,192,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9259 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 25 84 416 480 416 416), lower := (rows 35 194 13 25 84 32 64 128 256), losses := [] }

theorem u9259 : Upper (D 8) (R 8) [34,192,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9260 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 25 112 420 484 420 420), lower := (rows 35 194 13 25 112 32 64 128 256), losses := [] }

theorem u9260 : Upper (D 8) (R 8) [34,192,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9261 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 25 276 224 224 224 480), lower := (rows 35 194 13 25 276 32 64 128 256), losses := [] }

theorem u9261 : Upper (D 8) (R 8) [34,192,9,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9262 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 25 304 228 228 228 484), lower := (rows 35 194 13 25 304 32 64 128 256), losses := [] }

theorem u9262 : Upper (D 8) (R 8) [34,192,9,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9263 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 25 336 164 228 164 420), lower := (rows 35 194 13 25 336 32 64 128 256), losses := [] }

theorem u9263 : Upper (D 8) (R 8) [34,192,9,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9264 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 28 49 480 480 480 480), lower := (rows 35 194 13 28 49 32 64 128 256), losses := [] }

theorem u9264 : Upper (D 8) (R 8) [34,192,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9265 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 28 81 416 480 416 416), lower := (rows 35 194 13 28 81 32 64 128 256), losses := [] }

theorem u9265 : Upper (D 8) (R 8) [34,192,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9266 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 28 112 417 481 417 417), lower := (rows 35 194 13 28 112 32 64 128 256), losses := [] }

theorem u9266 : Upper (D 8) (R 8) [34,192,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9267 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 13 28 208 289 353 417 289), lower := (rows 35 194 13 28 208 32 64 128 256), losses := [] }

theorem u9267 : Upper (D 8) (R 8) [34,192,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9268 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 28 273 224 224 224 480), lower := (rows 35 194 13 28 273 32 64 128 256), losses := [] }

theorem u9268 : Upper (D 8) (R 8) [34,192,9,20,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9269 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9269 : Upper (D 8) (R 8) [34,192,9,20,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,288] 13 (by decide) (choices 1) [1,64] r9269 c9269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2334
  · exact u2335

def b9270 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 28 336 161 225 161 417), lower := (rows 35 194 13 28 336 32 64 128 256), losses := [] }

theorem u9270 : Upper (D 8) (R 8) [34,192,9,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9271 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 52 496 464 464 464), lower := (rows 35 194 13 41 52 32 64 128 256), losses := [] }

theorem u9271 : Upper (D 8) (R 8) [34,192,9,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9272 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 84 432 496 432 432), lower := (rows 35 194 13 41 84 32 64 128 256), losses := [] }

theorem u9272 : Upper (D 8) (R 8) [34,192,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9273 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 112 436 468 404 404), lower := (rows 35 194 13 41 112 32 64 128 256), losses := [] }

theorem u9273 : Upper (D 8) (R 8) [34,192,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9274 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 276 240 240 240 496), lower := (rows 35 194 13 41 276 32 64 128 256), losses := [] }

theorem u9274 : Upper (D 8) (R 8) [34,192,9,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9275 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 304 244 212 212 468), lower := (rows 35 194 13 41 304 32 64 128 256), losses := [] }

theorem u9275 : Upper (D 8) (R 8) [34,192,9,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9276 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 336 180 244 180 436), lower := (rows 35 194 13 41 336 32 64 128 256), losses := [] }

theorem u9276 : Upper (D 8) (R 8) [34,192,9,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9277 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 44 112 433 465 401 401), lower := (rows 35 194 13 44 112 32 64 128 256), losses := [] }

theorem u9277 : Upper (D 8) (R 8) [34,192,9,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9278 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 44 273 240 240 240 496), lower := (rows 35 194 13 44 273 32 64 128 256), losses := [] }

theorem u9278 : Upper (D 8) (R 8) [34,192,9,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9279 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 44 304 241 209 209 465), lower := (rows 35 194 13 44 304 32 64 128 256), losses := [] }

theorem u9279 : Upper (D 8) (R 8) [34,192,9,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9280 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 44 336 177 241 177 433), lower := (rows 35 194 13 44 336 32 64 128 256), losses := [] }

theorem u9280 : Upper (D 8) (R 8) [34,192,9,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9281 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 56 49 484 452 452 452), lower := (rows 35 194 13 56 49 32 64 128 256), losses := [] }

theorem u9281 : Upper (D 8) (R 8) [34,192,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9282 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 56 52 481 449 449 449), lower := (rows 35 194 13 56 52 32 64 128 256), losses := [] }

theorem u9282 : Upper (D 8) (R 8) [34,192,9,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9283 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 56 81 420 484 420 420), lower := (rows 35 194 13 56 81 32 64 128 256), losses := [] }

theorem u9283 : Upper (D 8) (R 8) [34,192,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9284 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 56 84 417 481 417 417), lower := (rows 35 194 13 56 84 32 64 128 256), losses := [] }

theorem u9284 : Upper (D 8) (R 8) [34,192,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9285 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 56 112 421 453 389 389), lower := (rows 35 194 13 56 112 32 64 128 256), losses := [] }

theorem u9285 : Upper (D 8) (R 8) [34,192,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9286 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 194 13 56 208 293 357 421 293), lower := (rows 35 194 13 56 208 32 64 128 256), losses := [] }

theorem u9286 : Upper (D 8) (R 8) [34,192,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9287 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 56 273 228 228 228 484), lower := (rows 35 194 13 56 273 32 64 128 256), losses := [] }

theorem u9287 : Upper (D 8) (R 8) [34,192,9,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9288 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9288 : Upper (D 8) (R 8) [34,192,9,48,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,260] 13 (by decide) (choices 1) [1,64] r9288 c9288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2336
  · exact u2337

def b9289 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 56 304 229 197 197 453), lower := (rows 35 194 13 56 304 32 64 128 256), losses := [] }

theorem u9289 : Upper (D 8) (R 8) [34,192,9,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9290 : Route 9 := (fun mask => (mask,id))

def c9290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9290 : Upper (D 8) (R 8) [34,192,9,48,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,320] 13 (by decide) (choices 1) [1,4,128] r9290 c9290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2338
  · exact u2339
  · exact u2340

def b9291 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 73 52 432 496 432 432), lower := (rows 35 194 13 73 52 32 64 128 256), losses := [] }

theorem u9291 : Upper (D 8) (R 8) [34,192,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9292 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 73 148 304 368 432 304), lower := (rows 35 194 13 73 148 32 64 128 256), losses := [] }

theorem u9292 : Upper (D 8) (R 8) [34,192,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9293 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 73 176 308 372 436 308), lower := (rows 35 194 13 73 176 32 64 128 256), losses := [] }

theorem u9293 : Upper (D 8) (R 8) [34,192,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9294 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 73 276 176 240 176 432), lower := (rows 35 194 13 73 276 32 64 128 256), losses := [] }

theorem u9294 : Upper (D 8) (R 8) [34,192,9,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9295 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 73 304 180 244 180 436), lower := (rows 35 194 13 73 304 32 64 128 256), losses := [] }

theorem u9295 : Upper (D 8) (R 8) [34,192,9,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9296 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 73 400 52 116 180 308), lower := (rows 35 194 13 73 400 32 64 128 256), losses := [] }

theorem u9296 : Upper (D 8) (R 8) [34,192,9,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9297 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 176 305 369 433 305), lower := (rows 35 194 13 76 176 32 64 128 256), losses := [] }

theorem u9297 : Upper (D 8) (R 8) [34,192,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9298 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 273 176 240 176 432), lower := (rows 35 194 13 76 273 32 64 128 256), losses := [] }

theorem u9298 : Upper (D 8) (R 8) [34,192,9,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9299 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 304 177 241 177 433), lower := (rows 35 194 13 76 304 32 64 128 256), losses := [] }

theorem u9299 : Upper (D 8) (R 8) [34,192,9,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9299
end Delivery.IrregularNine14.P08
