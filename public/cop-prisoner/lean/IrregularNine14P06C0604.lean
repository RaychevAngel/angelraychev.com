import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0343
import IrregularNine14P06C0344

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36240 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 140 296 82 53 85 149 277), lower := (rows 35 70 140 296 82 32 64 128 256), losses := [] }

theorem u36240 : Upper (D 6) (R 6) [34,68,136,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36241 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 140 296 84 51 83 147 275), lower := (rows 35 70 140 296 84 32 64 128 256), losses := [] }

theorem u36241 : Upper (D 6) (R 6) [34,68,136,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36242 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 140 328 19 53 117 181 309), lower := (rows 35 70 140 328 19 32 64 128 256), losses := [] }

theorem u36242 : Upper (D 6) (R 6) [34,68,136,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36243 : Route 9 := (fun mask => (mask,id))

def c36243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36243 : Upper (D 6) (R 6) [34,68,136,320,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,5] 13 (by decide) (choices 1) [1,2,16] r36243 c36243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20587
  · exact u20588
  · exact u20589

def b36244 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,0),(4,5)], upper := (rows 35 70 140 328 22 49 113 177 305), lower := (rows 35 70 140 328 22 32 64 128 256), losses := [] }

theorem u36244 : Upper (D 6) (R 6) [34,68,136,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36245 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 140 328 49 55 87 151 279), lower := (rows 35 70 140 328 49 32 64 128 256), losses := [] }

theorem u36245 : Upper (D 6) (R 6) [34,68,136,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36246 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 70 140 328 50 53 85 149 277), lower := (rows 35 70 140 328 50 32 64 128 256), losses := [] }

theorem u36246 : Upper (D 6) (R 6) [34,68,136,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36247 : Route 9 := (fun mask => (mask,id))

def c36247 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36247 : Upper (D 6) (R 6) [34,68,136,320,36] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,36] 13 (by decide) (choices 1) [1,2,16] r36247 c36247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20590
  · exact u20591
  · exact u20592

def b36248 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 21 376 344 472 344), lower := (rows 35 70 164 11 21 32 64 128 256), losses := [] }

theorem u36248 : Upper (D 6) (R 6) [34,68,160,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36249 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 25 372 340 468 340), lower := (rows 35 70 164 11 25 32 64 128 256), losses := [] }

theorem u36249 : Upper (D 6) (R 6) [34,68,160,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36250 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 28 369 337 465 337), lower := (rows 35 70 164 11 28 32 64 128 256), losses := [] }

theorem u36250 : Upper (D 6) (R 6) [34,68,160,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36251 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 81 316 348 412 284), lower := (rows 35 70 164 11 81 32 64 128 256), losses := [] }

theorem u36251 : Upper (D 6) (R 6) [34,68,160,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36252 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 88 309 341 405 277), lower := (rows 35 70 164 11 88 32 64 128 256), losses := [] }

theorem u36252 : Upper (D 6) (R 6) [34,68,160,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36253 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 273 124 92 220 348), lower := (rows 35 70 164 11 273 32 64 128 256), losses := [] }

theorem u36253 : Upper (D 6) (R 6) [34,68,160,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36254 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 276 121 89 217 345), lower := (rows 35 70 164 11 276 32 64 128 256), losses := [] }

theorem u36254 : Upper (D 6) (R 6) [34,68,160,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36255 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 280 117 85 213 341), lower := (rows 35 70 164 11 280 32 64 128 256), losses := [] }

theorem u36255 : Upper (D 6) (R 6) [34,68,160,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36256 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 11 336 61 93 157 285), lower := (rows 35 70 164 11 336 32 64 128 256), losses := [] }

theorem u36256 : Upper (D 6) (R 6) [34,68,160,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36257 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 164 13 25 370 338 466 338), lower := (rows 35 70 164 13 25 32 64 128 256), losses := [] }

theorem u36257 : Upper (D 6) (R 6) [34,68,160,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36258 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 338, targets := 32 },{ cop := 4, region := 353, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 70 164 13 26 369 337 465 337), lower := (rows 35 70 164 13 26 32 64 128 256), losses := [] }

theorem u36258 : Upper (D 6) (R 6) [34,68,160,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36259 : Route 9 := (fun mask => (mask,id))

def c36259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36259 : Upper (D 6) (R 6) [34,68,160,5,65] 13 := by
  apply FastRouting.sound _ _ [34,68,160,5,65] 13 (by decide) (choices 1) [2,8,16,256] r36259 c36259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20593
  · exact u20594
  · exact u20595
  · exact u20596

def b36260 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 164 13 82 313 345 409 281), lower := (rows 35 70 164 13 82 32 64 128 256), losses := [] }

theorem u36260 : Upper (D 6) (R 6) [34,68,160,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36261 : Route 9 := (fun mask => (mask,id))

def c36261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36261 : Upper (D 6) (R 6) [34,68,160,5,72] 13 := by
  apply FastRouting.sound _ _ [34,68,160,5,72] 13 (by decide) (choices 1) [1,2,16,256] r36261 c36261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20597
  · exact u20598
  · exact u20599
  · exact u20600

def r36262 : Route 9 := (fun mask => (mask,id))

def c36262 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36262 : Upper (D 6) (R 6) [34,68,160,5,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,5,257] 13 (by decide) (choices 1) [2,8,16,64] r36262 c36262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20601
  · exact u20602
  · exact u20603
  · exact u20604

def r36263 : Route 9 := (fun mask => (mask,id))

def c36263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36263 : Upper (D 6) (R 6) [34,68,160,5,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,5,258] 13 (by decide) (choices 1) [1,8,16,64] r36263 c36263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20605
  · exact u20606
  · exact u20607
  · exact u20608

def r36264 : Route 9 := (fun mask => (mask,id))

def c36264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36264 : Upper (D 6) (R 6) [34,68,160,5,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,5,264] 13 (by decide) (choices 1) [1,2,16,64] r36264 c36264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20609
  · exact u20610
  · exact u20611
  · exact u20612

def r36265 : Route 9 := (fun mask => (mask,id))

def c36265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36265 : Upper (D 6) (R 6) [34,68,160,5,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,5,320] 13 (by decide) (choices 1) [1,2,8,16] r36265 c36265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20613
  · exact u20614
  · exact u20615
  · exact u20616

def b36266 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 164 14 25 369 337 465 337), lower := (rows 35 70 164 14 25 32 64 128 256), losses := [] }

theorem u36266 : Upper (D 6) (R 6) [34,68,160,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36267 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 164 14 81 313 345 409 281), lower := (rows 35 70 164 14 81 32 64 128 256), losses := [] }

theorem u36267 : Upper (D 6) (R 6) [34,68,160,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36268 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 14 88 305 337 401 273), lower := (rows 35 70 164 14 88 32 64 128 256), losses := [] }

theorem u36268 : Upper (D 6) (R 6) [34,68,160,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36269 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 164 14 273 121 89 217 345), lower := (rows 35 70 164 14 273 32 64 128 256), losses := [] }

theorem u36269 : Upper (D 6) (R 6) [34,68,160,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36270 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 164 14 280 113 81 209 337), lower := (rows 35 70 164 14 280 32 64 128 256), losses := [] }

theorem u36270 : Upper (D 6) (R 6) [34,68,160,6,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36271 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 164 14 336 57 89 153 281), lower := (rows 35 70 164 14 336 32 64 128 256), losses := [] }

theorem u36271 : Upper (D 6) (R 6) [34,68,160,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36272 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 164 25 25 358 326 454 326), lower := (rows 35 70 164 25 25 32 64 128 256), losses := [] }

theorem u36272 : Upper (D 6) (R 6) [34,68,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36273 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 164 25 26 357 325 453 325), lower := (rows 35 70 164 25 26 32 64 128 256), losses := [] }

theorem u36273 : Upper (D 6) (R 6) [34,68,160,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36274 : Route 9 := (fun mask => (mask,id))

def c36274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36274 : Upper (D 6) (R 6) [34,68,160,17,12] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,12] 13 (by decide) (choices 1) [1,2,64,256] r36274 c36274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20617
  · exact u20618
  · exact u20619
  · exact u20620

def b36275 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 164 25 81 302 334 398 270), lower := (rows 35 70 164 25 81 32 64 128 256), losses := [] }

theorem u36275 : Upper (D 6) (R 6) [34,68,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36276 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 164 25 82 301 333 397 269), lower := (rows 35 70 164 25 82 32 64 128 256), losses := [] }

theorem u36276 : Upper (D 6) (R 6) [34,68,160,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36277 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 164 25 84 299 331 395 267), lower := (rows 35 70 164 25 84 32 64 128 256), losses := [] }

theorem u36277 : Upper (D 6) (R 6) [34,68,160,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36278 : Route 9 := (fun mask => (mask,id))

def c36278 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36278 : Upper (D 6) (R 6) [34,68,160,17,72] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,72] 13 (by decide) (choices 1) [1,2,4,256] r36278 c36278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20621
  · exact u20622
  · exact u20623
  · exact u20624

def b36279 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 164 25 273 110 78 206 334), lower := (rows 35 70 164 25 273 32 64 128 256), losses := [] }

theorem u36279 : Upper (D 6) (R 6) [34,68,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36280 : Route 9 := (fun mask => (mask,id))

def c36280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36280 : Upper (D 6) (R 6) [34,68,160,17,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,258] 13 (by decide) (choices 1) [1,4,8,64] r36280 c36280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20625
  · exact u20626
  · exact u20627
  · exact u20628

def r36281 : Route 9 := (fun mask => (mask,id))

def c36281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36281 : Upper (D 6) (R 6) [34,68,160,17,260] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,260] 13 (by decide) (choices 1) [1,2,8,64] r36281 c36281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20629
  · exact u20630
  · exact u20631
  · exact u20632

def r36282 : Route 9 := (fun mask => (mask,id))

def c36282 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36282 : Upper (D 6) (R 6) [34,68,160,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,264] 13 (by decide) (choices 1) [1,2,4,64] r36282 c36282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20633
  · exact u20634
  · exact u20635
  · exact u20636

def r36283 : Route 9 := (fun mask => (mask,id))

def c36283 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36283 : Upper (D 6) (R 6) [34,68,160,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,320] 13 (by decide) (choices 1) [1,2,4,8] r36283 c36283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20637
  · exact u20638
  · exact u20639
  · exact u20640

def b36284 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 164 26 28 353 321 449 321), lower := (rows 35 70 164 26 28 32 64 128 256), losses := [] }

theorem u36284 : Upper (D 6) (R 6) [34,68,160,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36285 : Route 9 := (fun mask => (mask,id))

def c36285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36285 : Upper (D 6) (R 6) [34,68,160,18,65] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,65] 13 (by decide) (choices 1) [1,4,8,256] r36285 c36285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20641
  · exact u20642
  · exact u20643
  · exact u20644

def b36286 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 26 84 297 329 393 265), lower := (rows 35 70 164 26 84 32 64 128 256), losses := [] }

theorem u36286 : Upper (D 6) (R 6) [34,68,160,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36287 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 164 26 88 293 325 389 261), lower := (rows 35 70 164 26 88 32 64 128 256), losses := [] }

theorem u36287 : Upper (D 6) (R 6) [34,68,160,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36288 : Route 9 := (fun mask => (mask,id))

def c36288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36288 : Upper (D 6) (R 6) [34,68,160,18,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,257] 13 (by decide) (choices 1) [1,4,8,64] r36288 c36288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20645
  · exact u20646
  · exact u20647
  · exact u20648

def r36289 : Route 9 := (fun mask => (mask,id))

def c36289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36289 : Upper (D 6) (R 6) [34,68,160,18,260] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,260] 13 (by decide) (choices 1) [1,8,64] r36289 c36289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20649
  · exact u20650
  · exact u20651

def r36290 : Route 9 := (fun mask => (mask,id))

def c36290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36290 : Upper (D 6) (R 6) [34,68,160,18,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,264] 13 (by decide) (choices 1) [1,4,64] r36290 c36290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20652
  · exact u20653
  · exact u20654

def r36291 : Route 9 := (fun mask => (mask,id))

def c36291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36291 : Upper (D 6) (R 6) [34,68,160,18,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,320] 13 (by decide) (choices 1) [1,4,8] r36291 c36291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20655
  · exact u20656
  · exact u20657

def r36292 : Route 9 := (fun mask => (mask,id))

def c36292 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36292 : Upper (D 6) (R 6) [34,68,160,20,65] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,65] 13 (by decide) (choices 1) [1,2,8,256] r36292 c36292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20658
  · exact u20659
  · exact u20660
  · exact u20661

def b36293 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 28 82 297 329 393 265), lower := (rows 35 70 164 28 82 32 64 128 256), losses := [] }

theorem u36293 : Upper (D 6) (R 6) [34,68,160,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36294 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 164 28 88 291 323 387 259), lower := (rows 35 70 164 28 88 32 64 128 256), losses := [] }

theorem u36294 : Upper (D 6) (R 6) [34,68,160,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36295 : Route 9 := (fun mask => (mask,id))

def c36295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36295 : Upper (D 6) (R 6) [34,68,160,20,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,257] 13 (by decide) (choices 1) [1,2,8,64] r36295 c36295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20662
  · exact u20663
  · exact u20664
  · exact u20665

def r36296 : Route 9 := (fun mask => (mask,id))

def c36296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36296 : Upper (D 6) (R 6) [34,68,160,20,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,258] 13 (by decide) (choices 1) [1,8,64] r36296 c36296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20666
  · exact u20667
  · exact u20668

def r36297 : Route 9 := (fun mask => (mask,id))

def c36297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36297 : Upper (D 6) (R 6) [34,68,160,20,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,264] 13 (by decide) (choices 1) [1,2,64] r36297 c36297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20669
  · exact u20670
  · exact u20671

def r36298 : Route 9 := (fun mask => (mask,id))

def c36298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36298 : Upper (D 6) (R 6) [34,68,160,20,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,320] 13 (by decide) (choices 1) [1,2,8] r36298 c36298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20672
  · exact u20673
  · exact u20674

def r36299 : Route 9 := (fun mask => (mask,id))

def c36299 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36299 : Upper (D 6) (R 6) [34,68,160,65,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,257] 13 (by decide) (choices 1) [2,4,8,16] r36299 c36299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20675
  · exact u20676
  · exact u20677
  · exact u20678

#print axioms u36299
end Delivery.IrregularNine14.P06
