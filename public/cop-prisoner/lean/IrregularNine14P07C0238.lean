import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0039

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14280 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 98 164 73 152 48 323 387 259), lower := (rows 7 98 164 73 152 48 64 128 256), losses := [] }

theorem u14280 : Upper (D 7) (R 7) [6,96,160,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14280 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14281 : Route 9 := (fun mask => (mask,id))

def c14281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14281 : Upper (D 7) (R 7) [6,96,160,65,136,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,136,256] 13 (by decide) (choices 1) [1,2,16] r14281 c14281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2352
  · exact u2353
  · exact u2354

def b14282 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 73 273 34 216 152 408), lower := (rows 7 98 164 73 273 34 64 128 256), losses := [] }

theorem u14282 : Upper (D 7) (R 7) [6,96,160,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14283 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 73 273 40 210 146 402), lower := (rows 7 98 164 73 273 40 64 128 256), losses := [] }

theorem u14283 : Upper (D 7) (R 7) [6,96,160,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14283 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14284 : Route 9 := (fun mask => (mask,id))

def c14284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14284 : Upper (D 7) (R 7) [6,96,160,65,257,16] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,257,16] 13 (by decide) (choices 1) [2,8,128] r14284 c14284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2355
  · exact u2356
  · exact u2357

def b14285 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 73 273 160 90 154 282), lower := (rows 7 98 164 73 273 160 64 128 256), losses := [] }

theorem u14285 : Upper (D 7) (R 7) [6,96,160,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14286 : Route 9 := (fun mask => (mask,id))

def c14286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14286 : Upper (D 7) (R 7) [6,96,160,65,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,258,1] 13 (by decide) (choices 1) [8,16,128] r14286 c14286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2358
  · exact u2359
  · exact u2360

def b14287 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 73 274 40 209 145 401), lower := (rows 7 98 164 73 274 40 64 128 256), losses := [] }

theorem u14287 : Upper (D 7) (R 7) [6,96,160,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14287 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14288 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 98 164 73 274 48 201 137 393), lower := (rows 7 98 164 73 274 48 64 128 256), losses := [] }

theorem u14288 : Upper (D 7) (R 7) [6,96,160,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14288 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14289 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 73 274 160 89 153 281), lower := (rows 7 98 164 73 274 160 64 128 256), losses := [] }

theorem u14289 : Upper (D 7) (R 7) [6,96,160,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14290 : Route 9 := (fun mask => (mask,id))

def c14290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14290 : Upper (D 7) (R 7) [6,96,160,65,264,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,264,1] 13 (by decide) (choices 1) [2,16,128] r14290 c14290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2361
  · exact u2362
  · exact u2363

def b14291 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 73 280 34 209 145 401), lower := (rows 7 98 164 73 280 34 64 128 256), losses := [] }

theorem u14291 : Upper (D 7) (R 7) [6,96,160,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14292 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 73 280 48 195 131 387), lower := (rows 7 98 164 73 280 48 64 128 256), losses := [] }

theorem u14292 : Upper (D 7) (R 7) [6,96,160,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14292 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14293 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 73 280 160 83 147 275), lower := (rows 7 98 164 73 280 160 64 128 256), losses := [] }

theorem u14293 : Upper (D 7) (R 7) [6,96,160,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14294 : Route 9 := (fun mask => (mask,id))

def c14294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14294 : Upper (D 7) (R 7) [6,96,160,65,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,384,1] 13 (by decide) (choices 1) [2,8,16] r14294 c14294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2364
  · exact u2365
  · exact u2366

def b14295 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 73 400 34 89 153 281), lower := (rows 7 98 164 73 400 34 64 128 256), losses := [] }

theorem u14295 : Upper (D 7) (R 7) [6,96,160,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14296 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 73 400 40 83 147 275), lower := (rows 7 98 164 73 400 40 64 128 256), losses := [] }

theorem u14296 : Upper (D 7) (R 7) [6,96,160,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14296 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14297 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 98 164 73 400 48 75 139 267), lower := (rows 7 98 164 73 400 48 64 128 256), losses := [] }

theorem u14297 : Upper (D 7) (R 7) [6,96,160,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14297 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14298 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 88 146 33 329 393 265), lower := (rows 7 98 164 88 146 33 64 128 256), losses := [] }

theorem u14298 : Upper (D 7) (R 7) [6,96,160,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14299 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 88 146 40 321 385 257), lower := (rows 7 98 164 88 146 40 64 128 256), losses := [] }

theorem u14299 : Upper (D 7) (R 7) [6,96,160,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14299 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14300 : Route 9 := (fun mask => (mask,id))

def c14300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14300 : Upper (D 7) (R 7) [6,96,160,80,130,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,130,256] 13 (by decide) (choices 1) [1,8] r14300 c14300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2367
  · exact u2368

def r14301 : Route 9 := (fun mask => (mask,id))

def c14301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14301 : Upper (D 7) (R 7) [6,96,160,80,257,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,257,1] 13 (by decide) (choices 1) [2,8,128] r14301 c14301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2369
  · exact u2370
  · exact u2371

def b14302 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 88 273 34 201 137 393), lower := (rows 7 98 164 88 273 34 64 128 256), losses := [] }

theorem u14302 : Upper (D 7) (R 7) [6,96,160,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14303 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 88 273 40 195 131 387), lower := (rows 7 98 164 88 273 40 64 128 256), losses := [] }

theorem u14303 : Upper (D 7) (R 7) [6,96,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14303 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14304 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 88 273 160 75 139 267), lower := (rows 7 98 164 88 273 160 64 128 256), losses := [] }

theorem u14304 : Upper (D 7) (R 7) [6,96,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14305 : Route 9 := (fun mask => (mask,id))

def c14305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14305 : Upper (D 7) (R 7) [6,96,160,80,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,258,1] 13 (by decide) (choices 1) [1,8,128] r14305 c14305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2372
  · exact u2373
  · exact u2374

def b14306 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 88 274 40 193 129 385), lower := (rows 7 98 164 88 274 40 64 128 256), losses := [] }

theorem u14306 : Upper (D 7) (R 7) [6,96,160,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14306 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14307 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 88 274 160 73 137 265), lower := (rows 7 98 164 88 274 160 64 128 256), losses := [] }

theorem u14307 : Upper (D 7) (R 7) [6,96,160,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14308 : Route 9 := (fun mask => (mask,id))

def c14308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14308 : Upper (D 7) (R 7) [6,96,160,80,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,384,1] 13 (by decide) (choices 1) [1,2,8] r14308 c14308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2375
  · exact u2376
  · exact u2377

def b14309 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 88 400 34 73 137 265), lower := (rows 7 98 164 88 400 34 64 128 256), losses := [] }

theorem u14309 : Upper (D 7) (R 7) [6,96,160,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14310 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 88 400 40 67 131 259), lower := (rows 7 98 164 88 400 40 64 128 256), losses := [] }

theorem u14310 : Upper (D 7) (R 7) [6,96,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14310 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14311 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 138 273 33 88 216 344), lower := (rows 7 98 164 138 273 33 64 128 256), losses := [] }

theorem u14311 : Upper (D 7) (R 7) [6,96,160,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14312 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 98 164 138 273 40 81 209 337), lower := (rows 7 98 164 138 273 40 64 128 256), losses := [] }

theorem u14312 : Upper (D 7) (R 7) [6,96,160,130,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14312 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14313 : Route 9 := (fun mask => (mask,id))

def c14313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14313 : Upper (D 7) (R 7) [6,96,160,130,257,16] 13 := by
  apply FastRouting.sound _ _ [6,96,160,130,257,16] 13 (by decide) (choices 1) [1,8] r14313 c14313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2378
  · exact u2379

def b14314 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 138 273 96 89 153 281), lower := (rows 7 98 164 138 273 96 64 128 256), losses := [] }

theorem u14314 : Upper (D 7) (R 7) [6,96,160,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14315 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 138 280 33 81 209 337), lower := (rows 7 98 164 138 280 33 64 128 256), losses := [] }

theorem u14315 : Upper (D 7) (R 7) [6,96,160,130,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14316 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 164 138 280 48 65 193 321), lower := (rows 7 98 164 138 280 48 64 128 256), losses := [] }

theorem u14316 : Upper (D 7) (R 7) [6,96,160,130,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14316 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14317 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 138 280 96 81 145 273), lower := (rows 7 98 164 138 280 96 64 128 256), losses := [] }

theorem u14317 : Upper (D 7) (R 7) [6,96,160,130,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14318 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 138 336 33 89 153 281), lower := (rows 7 98 164 138 336 33 64 128 256), losses := [] }

theorem u14318 : Upper (D 7) (R 7) [6,96,160,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14319 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 98 164 138 336 40 81 145 273), lower := (rows 7 98 164 138 336 40 64 128 256), losses := [] }

theorem u14319 : Upper (D 7) (R 7) [6,96,160,130,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14319 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14320 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 164 138 336 48 73 137 265), lower := (rows 7 98 164 138 336 48 64 128 256), losses := [] }

theorem u14320 : Upper (D 7) (R 7) [6,96,160,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14320 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14321 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 152 273 33 74 202 330), lower := (rows 7 98 164 152 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 64 128 256), good := (rows 37 96 164 188 305 33 64 128 256) },{ target := 6, region := (rows 1 2 12 8 16 49 0 128 256), good := (rows 39 34 164 188 305 33 0 128 256) }] }

theorem u14321 : Upper (D 7) (R 7) [6,96,160,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14322 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 152 273 34 73 201 329), lower := (rows 7 98 164 152 273 34 64 128 256), losses := [] }

theorem u14322 : Upper (D 7) (R 7) [6,96,160,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14323 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 98 164 152 273 40 67 195 323), lower := (rows 7 98 164 152 273 40 64 128 256), losses := [] }

theorem u14323 : Upper (D 7) (R 7) [6,96,160,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14323 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14324 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 152 273 96 75 139 267), lower := (rows 7 98 164 152 273 96 64 128 256), losses := [] }

theorem u14324 : Upper (D 7) (R 7) [6,96,160,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14325 : Route 9 := (fun mask => (mask,id))

def c14325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14325 : Upper (D 7) (R 7) [6,96,160,144,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,144,258,1] 13 (by decide) (choices 1) [1,8] r14325 c14325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2380
  · exact u2381

def b14326 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 98 164 152 274 40 65 193 321), lower := (rows 7 98 164 152 274 40 64 128 256), losses := [] }

theorem u14326 : Upper (D 7) (R 7) [6,96,160,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14326 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14327 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 152 274 96 73 137 265), lower := (rows 7 98 164 152 274 96 64 128 256), losses := [] }

theorem u14327 : Upper (D 7) (R 7) [6,96,160,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14328 : Route 9 := (fun mask => (mask,id))

def c14328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14328 : Upper (D 7) (R 7) [6,96,160,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,144,320,1] 13 (by decide) (choices 1) [1,2,8] r14328 c14328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2382
  · exact u2383
  · exact u2384

def b14329 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 152 336 34 73 137 265), lower := (rows 7 98 164 152 336 34 64 128 256), losses := [] }

theorem u14329 : Upper (D 7) (R 7) [6,96,160,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14330 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 98 164 152 336 40 67 131 259), lower := (rows 7 98 164 152 336 40 64 128 256), losses := [] }

theorem u14330 : Upper (D 7) (R 7) [6,96,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14330 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14331 : Route 9 := (fun mask => (mask,id))

def c14331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14331 : Upper (D 7) (R 7) [6,96,160,192,257,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257,1] 13 (by decide) (choices 1) [2,8,16] r14331 c14331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2385
  · exact u2386
  · exact u2387

def b14332 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 200 273 34 89 153 281), lower := (rows 7 98 164 200 273 34 64 128 256), losses := [] }

theorem u14332 : Upper (D 7) (R 7) [6,96,160,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14333 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 200 273 40 83 147 275), lower := (rows 7 98 164 200 273 40 64 128 256), losses := [] }

theorem u14333 : Upper (D 7) (R 7) [6,96,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14333 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14334 : Route 9 := (fun mask => (mask,id))

def c14334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14334 : Upper (D 7) (R 7) [6,96,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257,16] 13 (by decide) (choices 1) [1,2,8] r14334 c14334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2388
  · exact u2389
  · exact u2390

def r14335 : Route 9 := (fun mask => (mask,id))

def c14335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14335 : Upper (D 7) (R 7) [6,96,160,192,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,258,1] 13 (by decide) (choices 1) [1,8,16] r14335 c14335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2391
  · exact u2392
  · exact u2393

def b14336 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 200 274 40 81 145 273), lower := (rows 7 98 164 200 274 40 64 128 256), losses := [] }

theorem u14336 : Upper (D 7) (R 7) [6,96,160,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14336 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14337 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 98 164 200 274 48 73 137 265), lower := (rows 7 98 164 200 274 48 64 128 256), losses := [] }

theorem u14337 : Upper (D 7) (R 7) [6,96,160,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14337 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14338 : Route 9 := (fun mask => (mask,id))

def c14338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14338 : Upper (D 7) (R 7) [6,96,160,192,264,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,264,1] 13 (by decide) (choices 1) [1,2,16] r14338 c14338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2394
  · exact u2395
  · exact u2396

def b14339 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 200 280 34 81 145 273), lower := (rows 7 98 164 200 280 34 64 128 256), losses := [] }

theorem u14339 : Upper (D 7) (R 7) [6,96,160,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14339
end Delivery.IrregularNine14.P07
