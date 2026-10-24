import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0270
import IrregularNine14P06C0271

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33240 : Route 9 := (fun mask => (mask,id))

def c33240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33240 : Upper (D 6) (R 6) [10,132,48,33,260] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,260] 13 (by decide) (choices 1) [1,2,64] r33240 c33240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16228
  · exact u16229
  · exact u16230

def r33241 : Route 9 := (fun mask => (mask,id))

def c33241 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33241 : Upper (D 6) (R 6) [10,132,48,33,320] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,320] 13 (by decide) (choices 1) [1,2,4,64] r33241 c33241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16231
  · exact u16232
  · exact u16233
  · exact u16234

def b33242 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 52 73 19 356 356 484 356), lower := (rows 11 134 52 73 19 32 64 128 256), losses := [] }

theorem u33242 : Upper (D 6) (R 6) [10,132,48,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33243 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 4, region := 482, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 134 52 73 21 354 354 482 354), lower := (rows 11 134 52 73 21 32 64 128 256), losses := [] }

theorem u33243 : Upper (D 6) (R 6) [10,132,48,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33244 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 52 73 22 353 353 481 353), lower := (rows 11 134 52 73 22 32 64 128 256), losses := [] }

theorem u33244 : Upper (D 6) (R 6) [10,132,48,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33245 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 73 49 358 326 454 326), lower := (rows 11 134 52 73 49 32 64 128 256), losses := [] }

theorem u33245 : Upper (D 6) (R 6) [10,132,48,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33246 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 73 50 357 325 453 325), lower := (rows 11 134 52 73 50 32 64 128 256), losses := [] }

theorem u33246 : Upper (D 6) (R 6) [10,132,48,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33247 : PairBound 9 := { available := 323, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 73 52 355 323 451 323), lower := (rows 11 134 52 73 52 32 64 128 256), losses := [] }

theorem u33247 : Upper (D 6) (R 6) [10,132,48,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33248 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 134 52 73 81 294 358 422 294), lower := (rows 11 134 52 73 81 32 64 128 256), losses := [] }

theorem u33248 : Upper (D 6) (R 6) [10,132,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33249 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 52 73 82 293 357 421 293), lower := (rows 11 134 52 73 82 32 64 128 256), losses := [] }

theorem u33249 : Upper (D 6) (R 6) [10,132,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33250 : Route 9 := (fun mask => (mask,id))

def c33250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33250 : Upper (D 6) (R 6) [10,132,48,65,68] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,68] 13 (by decide) (choices 1) [1,2,256] r33250 c33250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16235
  · exact u16236
  · exact u16237

def b33251 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 73 112 295 327 391 263), lower := (rows 11 134 52 73 112 32 64 128 256), losses := [] }

theorem u33251 : Upper (D 6) (R 6) [10,132,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33252 : Route 9 := (fun mask => (mask,id))

def c33252 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33252 : Upper (D 6) (R 6) [10,132,48,65,257] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,257] 13 (by decide) (choices 1) [2,4,64] r33252 c33252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16238
  · exact u16239
  · exact u16240

def r33253 : Route 9 := (fun mask => (mask,id))

def c33253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33253 : Upper (D 6) (R 6) [10,132,48,65,258] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,258] 13 (by decide) (choices 1) [1,4,64] r33253 c33253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16241
  · exact u16242
  · exact u16243

def r33254 : Route 9 := (fun mask => (mask,id))

def c33254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33254 : Upper (D 6) (R 6) [10,132,48,65,260] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,260] 13 (by decide) (choices 1) [1,2,64] r33254 c33254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16244
  · exact u16245
  · exact u16246

def b33255 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 73 304 103 71 199 327), lower := (rows 11 134 52 73 304 32 64 128 256), losses := [] }

theorem u33255 : Upper (D 6) (R 6) [10,132,48,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33256 : Route 9 := (fun mask => (mask,id))

def c33256 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33256 : Upper (D 6) (R 6) [10,132,48,65,320] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,320] 13 (by decide) (choices 1) [1,2,4] r33256 c33256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16247
  · exact u16248
  · exact u16249

def b33257 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 134 52 76 19 353 353 481 353), lower := (rows 11 134 52 76 19 32 64 128 256), losses := [] }

theorem u33257 : Upper (D 6) (R 6) [10,132,48,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33258 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 76 49 355 323 451 323), lower := (rows 11 134 52 76 49 32 64 128 256), losses := [] }

theorem u33258 : Upper (D 6) (R 6) [10,132,48,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33259 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 76 50 353 321 449 321), lower := (rows 11 134 52 76 50 32 64 128 256), losses := [] }

theorem u33259 : Upper (D 6) (R 6) [10,132,48,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33260 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 134 52 76 81 291 355 419 291), lower := (rows 11 134 52 76 81 32 64 128 256), losses := [] }

theorem u33260 : Upper (D 6) (R 6) [10,132,48,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33261 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 134 52 76 82 289 353 417 289), lower := (rows 11 134 52 76 82 32 64 128 256), losses := [] }

theorem u33261 : Upper (D 6) (R 6) [10,132,48,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33262 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 134 52 76 112 291 323 387 259), lower := (rows 11 134 52 76 112 32 64 128 256), losses := [] }

theorem u33262 : Upper (D 6) (R 6) [10,132,48,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33263 : Route 9 := (fun mask => (mask,id))

def c33263 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33263 : Upper (D 6) (R 6) [10,132,48,68,257] 13 := by
  apply FastRouting.sound _ _ [10,132,48,68,257] 13 (by decide) (choices 1) [1,2,64] r33263 c33263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16250
  · exact u16251
  · exact u16252

def r33264 : Route 9 := (fun mask => (mask,id))

def c33264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33264 : Upper (D 6) (R 6) [10,132,48,68,258] 13 := by
  apply FastRouting.sound _ _ [10,132,48,68,258] 13 (by decide) (choices 1) [1,64] r33264 c33264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16253
  · exact u16254

def b33265 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 76 304 99 67 195 323), lower := (rows 11 134 52 76 304 32 64 128 256), losses := [] }

theorem u33265 : Upper (D 6) (R 6) [10,132,48,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33266 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 134 52 76 336 35 99 163 291), lower := (rows 11 134 52 76 336 32 64 128 256), losses := [] }

theorem u33266 : Upper (D 6) (R 6) [10,132,48,68,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33267 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 52 104 19 357 325 453 325), lower := (rows 11 134 52 104 19 32 64 128 256), losses := [] }

theorem u33267 : Upper (D 6) (R 6) [10,132,48,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33268 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 11 134 52 104 21 355 323 451 323), lower := (rows 11 134 52 104 21 32 64 128 256), losses := [] }

theorem u33268 : Upper (D 6) (R 6) [10,132,48,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33269 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 52 104 22 353 321 449 321), lower := (rows 11 134 52 104 22 32 64 128 256), losses := [] }

theorem u33269 : Upper (D 6) (R 6) [10,132,48,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33270 : Route 9 := (fun mask => (mask,id))

def c33270 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33270 : Upper (D 6) (R 6) [10,132,48,96,65] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,65] 13 (by decide) (choices 1) [1,2,4,256] r33270 c33270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16255
  · exact u16256
  · exact u16257
  · exact u16258

def r33271 : Route 9 := (fun mask => (mask,id))

def c33271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33271 : Upper (D 6) (R 6) [10,132,48,96,66] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,66] 13 (by decide) (choices 1) [1,4,256] r33271 c33271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16259
  · exact u16260
  · exact u16261

def b33272 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 104 84 291 323 387 259), lower := (rows 11 134 52 104 84 32 64 128 256), losses := [] }

theorem u33272 : Upper (D 6) (R 6) [10,132,48,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33273 : Route 9 := (fun mask => (mask,id))

def c33273 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33273 : Upper (D 6) (R 6) [10,132,48,96,257] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,257] 13 (by decide) (choices 1) [1,2,4,64] r33273 c33273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16262
  · exact u16263
  · exact u16264
  · exact u16265

def r33274 : Route 9 := (fun mask => (mask,id))

def c33274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33274 : Upper (D 6) (R 6) [10,132,48,96,258] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,258] 13 (by decide) (choices 1) [1,4,64] r33274 c33274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16266
  · exact u16267
  · exact u16268

def r33275 : Route 9 := (fun mask => (mask,id))

def c33275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33275 : Upper (D 6) (R 6) [10,132,48,96,260] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,260] 13 (by decide) (choices 1) [1,2,64] r33275 c33275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16269
  · exact u16270
  · exact u16271

def r33276 : Route 9 := (fun mask => (mask,id))

def c33276 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33276 : Upper (D 6) (R 6) [10,132,48,96,320] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,320] 13 (by decide) (choices 1) [1,2,4] r33276 c33276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16272
  · exact u16273
  · exact u16274

def b33277 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 52 265 19 100 100 228 356), lower := (rows 11 134 52 265 19 32 64 128 256), losses := [] }

theorem u33277 : Upper (D 6) (R 6) [10,132,48,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33278 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 134 52 265 21 98 98 226 354), lower := (rows 11 134 52 265 21 32 64 128 256), losses := [] }

theorem u33278 : Upper (D 6) (R 6) [10,132,48,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33279 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 52 265 22 97 97 225 353), lower := (rows 11 134 52 265 22 32 64 128 256), losses := [] }

theorem u33279 : Upper (D 6) (R 6) [10,132,48,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33280 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 265 49 102 70 198 326), lower := (rows 11 134 52 265 49 32 64 128 256), losses := [] }

theorem u33280 : Upper (D 6) (R 6) [10,132,48,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33281 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 265 50 101 69 197 325), lower := (rows 11 134 52 265 50 32 64 128 256), losses := [] }

theorem u33281 : Upper (D 6) (R 6) [10,132,48,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33282 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 265 52 99 67 195 323), lower := (rows 11 134 52 265 52 32 64 128 256), losses := [] }

theorem u33282 : Upper (D 6) (R 6) [10,132,48,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33283 : Route 9 := (fun mask => (mask,id))

def c33283 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33283 : Upper (D 6) (R 6) [10,132,48,257,65] 13 := by
  apply FastRouting.sound _ _ [10,132,48,257,65] 13 (by decide) (choices 1) [2,4,64] r33283 c33283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16275
  · exact u16276
  · exact u16277

def r33284 : Route 9 := (fun mask => (mask,id))

def c33284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33284 : Upper (D 6) (R 6) [10,132,48,257,66] 13 := by
  apply FastRouting.sound _ _ [10,132,48,257,66] 13 (by decide) (choices 1) [1,4,64] r33284 c33284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16278
  · exact u16279
  · exact u16280

def r33285 : Route 9 := (fun mask => (mask,id))

def c33285 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33285 : Upper (D 6) (R 6) [10,132,48,257,68] 13 := by
  apply FastRouting.sound _ _ [10,132,48,257,68] 13 (by decide) (choices 1) [1,2,64] r33285 c33285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16281
  · exact u16282
  · exact u16283

def b33286 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 265 112 103 71 199 327), lower := (rows 11 134 52 265 112 32 64 128 256), losses := [] }

theorem u33286 : Upper (D 6) (R 6) [10,132,48,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33287 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 134 52 268 19 97 97 225 353), lower := (rows 11 134 52 268 19 32 64 128 256), losses := [] }

theorem u33287 : Upper (D 6) (R 6) [10,132,48,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33288 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 268 49 99 67 195 323), lower := (rows 11 134 52 268 49 32 64 128 256), losses := [] }

theorem u33288 : Upper (D 6) (R 6) [10,132,48,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33289 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 268 50 97 65 193 321), lower := (rows 11 134 52 268 50 32 64 128 256), losses := [] }

theorem u33289 : Upper (D 6) (R 6) [10,132,48,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33290 : Route 9 := (fun mask => (mask,id))

def c33290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33290 : Upper (D 6) (R 6) [10,132,48,260,65] 13 := by
  apply FastRouting.sound _ _ [10,132,48,260,65] 13 (by decide) (choices 1) [1,2,64] r33290 c33290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16284
  · exact u16285
  · exact u16286

def r33291 : Route 9 := (fun mask => (mask,id))

def c33291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33291 : Upper (D 6) (R 6) [10,132,48,260,66] 13 := by
  apply FastRouting.sound _ _ [10,132,48,260,66] 13 (by decide) (choices 1) [1,64] r33291 c33291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16287
  · exact u16288

def b33292 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 52 268 112 99 67 195 323), lower := (rows 11 134 52 268 112 32 64 128 256), losses := [] }

theorem u33292 : Upper (D 6) (R 6) [10,132,48,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33293 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 52 296 19 101 69 197 325), lower := (rows 11 134 52 296 19 32 64 128 256), losses := [] }

theorem u33293 : Upper (D 6) (R 6) [10,132,48,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33294 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 11 134 52 296 21 99 67 195 323), lower := (rows 11 134 52 296 21 32 64 128 256), losses := [] }

theorem u33294 : Upper (D 6) (R 6) [10,132,48,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33295 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 52 296 22 97 65 193 321), lower := (rows 11 134 52 296 22 32 64 128 256), losses := [] }

theorem u33295 : Upper (D 6) (R 6) [10,132,48,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33296 : Route 9 := (fun mask => (mask,id))

def c33296 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33296 : Upper (D 6) (R 6) [10,132,48,288,65] 13 := by
  apply FastRouting.sound _ _ [10,132,48,288,65] 13 (by decide) (choices 1) [1,2,4,64] r33296 c33296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16289
  · exact u16290
  · exact u16291
  · exact u16292

def r33297 : Route 9 := (fun mask => (mask,id))

def c33297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33297 : Upper (D 6) (R 6) [10,132,48,288,66] 13 := by
  apply FastRouting.sound _ _ [10,132,48,288,66] 13 (by decide) (choices 1) [1,4,64] r33297 c33297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16293
  · exact u16294
  · exact u16295

def r33298 : Route 9 := (fun mask => (mask,id))

def c33298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33298 : Upper (D 6) (R 6) [10,132,48,288,68] 13 := by
  apply FastRouting.sound _ _ [10,132,48,288,68] 13 (by decide) (choices 1) [1,2,64] r33298 c33298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16296
  · exact u16297
  · exact u16298

def b33299 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 52 328 19 101 101 229 357), lower := (rows 11 134 52 328 19 32 64 128 256), losses := [] }

theorem u33299 : Upper (D 6) (R 6) [10,132,48,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u33299
end Delivery.IrregularNine14.P06
