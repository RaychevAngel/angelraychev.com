import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0338
import IrregularNine14P07C0339
import IrregularNine14P07C0340

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35280 : Route 9 := (fun mask => (mask,id))

def c35280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35280 : Upper (D 7) (R 7) [34,192,10,20,96] 13 := by
  apply FastRouting.sound _ _ [34,192,10,20,96] 13 (by decide) (choices 1) [1,128,256] r35280 c35280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20320
  · exact u20321
  · exact u20322

def b35281 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 28, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 14 28 208 289 353 417 289), lower := (rows 35 194 14 28 208 32 64 128 256), losses := [] }

theorem u35281 : Upper (D 7) (R 7) [34,192,10,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35282 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35282 : Upper (D 7) (R 7) [34,192,10,20,257] 13 := by
  apply FastRouting.sound _ _ [34,192,10,20,257] 13 (by decide) (choices 1) [1,64] r35282 c35282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20323
  · exact u20324

def r35283 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35283 : Upper (D 7) (R 7) [34,192,10,20,288] 13 := by
  apply FastRouting.sound _ _ [34,192,10,20,288] 13 (by decide) (choices 1) [1,64] r35283 c35283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20325
  · exact u20326

def r35284 : Route 9 := (fun mask => (mask,id))

def c35284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35284 : Upper (D 7) (R 7) [34,192,10,20,320] 13 := by
  apply FastRouting.sound _ _ [34,192,10,20,320] 13 (by decide) (choices 1) [1,128] r35284 c35284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20327
  · exact u20328

def b35285 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 41 81 436 468 404 404), lower := (rows 35 194 14 41 81 32 64 128 256), losses := [] }

theorem u35285 : Upper (D 7) (R 7) [34,192,10,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35286 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 41 84 433 465 401 401), lower := (rows 35 194 14 41 84 32 64 128 256), losses := [] }

theorem u35286 : Upper (D 7) (R 7) [34,192,10,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35287 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 41 273 244 212 212 468), lower := (rows 35 194 14 41 273 32 64 128 256), losses := [] }

theorem u35287 : Upper (D 7) (R 7) [34,192,10,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35288 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 41 276 241 209 209 465), lower := (rows 35 194 14 41 276 32 64 128 256), losses := [] }

theorem u35288 : Upper (D 7) (R 7) [34,192,10,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35289 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 41 336 181 213 149 405), lower := (rows 35 194 14 41 336 32 64 128 256), losses := [] }

theorem u35289 : Upper (D 7) (R 7) [34,192,10,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35290 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 44 81 433 465 401 401), lower := (rows 35 194 14 44 81 32 64 128 256), losses := [] }

theorem u35290 : Upper (D 7) (R 7) [34,192,10,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35291 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 44 273 241 209 209 465), lower := (rows 35 194 14 44 273 32 64 128 256), losses := [] }

theorem u35291 : Upper (D 7) (R 7) [34,192,10,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35292 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 44 336 177 209 145 401), lower := (rows 35 194 14 44 336 32 64 128 256), losses := [] }

theorem u35292 : Upper (D 7) (R 7) [34,192,10,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35293 : Route 9 := (fun mask => (mask,id))

def c35293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35293 : Upper (D 7) (R 7) [34,192,10,48,65] 13 := by
  apply FastRouting.sound _ _ [34,192,10,48,65] 13 (by decide) (choices 1) [1,4,128,256] r35293 c35293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20329
  · exact u20330
  · exact u20331
  · exact u20332

def r35294 : Route 9 := (fun mask => (mask,id))

def c35294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35294 : Upper (D 7) (R 7) [34,192,10,48,68] 13 := by
  apply FastRouting.sound _ _ [34,192,10,48,68] 13 (by decide) (choices 1) [1,128,256] r35294 c35294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20333
  · exact u20334
  · exact u20335

def b35295 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 14 56 208 293 325 389 261), lower := (rows 35 194 14 56 208 32 64 128 256), losses := [] }

theorem u35295 : Upper (D 7) (R 7) [34,192,10,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35296 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35296 : Upper (D 7) (R 7) [34,192,10,48,257] 13 := by
  apply FastRouting.sound _ _ [34,192,10,48,257] 13 (by decide) (choices 1) [1,4,64] r35296 c35296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20336
  · exact u20337
  · exact u20338

def r35297 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35297 : Upper (D 7) (R 7) [34,192,10,48,260] 13 := by
  apply FastRouting.sound _ _ [34,192,10,48,260] 13 (by decide) (choices 1) [1,64] r35297 c35297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20339
  · exact u20340

def r35298 : Route 9 := (fun mask => (mask,id))

def c35298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35298 : Upper (D 7) (R 7) [34,192,10,48,320] 13 := by
  apply FastRouting.sound _ _ [34,192,10,48,320] 13 (by decide) (choices 1) [1,4,128] r35298 c35298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20341
  · exact u20342
  · exact u20343

def b35299 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 14 73 49 436 468 404 404), lower := (rows 35 194 14 73 49 32 64 128 256), losses := [] }

theorem u35299 : Upper (D 7) (R 7) [34,192,10,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35300 : Route 9 := (fun mask => (mask,id))

def c35300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u35300 : Upper (D 7) (R 7) [34,192,10,65,36] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,36] 13 (by decide) (choices 1) [1,16,128,256] r35300 c35300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20344
  · exact u20345
  · exact u20346
  · exact u20347

def r35301 : Route 9 := (fun mask => (mask,id))

def c35301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35301 : Upper (D 7) (R 7) [34,192,10,65,129] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,129] 13 (by decide) (choices 1) [4,16,256] r35301 c35301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20348
  · exact u20349
  · exact u20350

def r35302 : Route 9 := (fun mask => (mask,id))

def c35302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35302 : Upper (D 7) (R 7) [34,192,10,65,132] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,132] 13 (by decide) (choices 1) [1,16,256] r35302 c35302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20351
  · exact u20352
  · exact u20353

def r35303 : Route 9 := (fun mask => (mask,id))

def c35303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35303 : Upper (D 7) (R 7) [34,192,10,65,160] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,160] 13 (by decide) (choices 1) [1,4,16,256] r35303 c35303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20354
  · exact u20355
  · exact u20356
  · exact u20357

def r35304 : Route 9 := (fun mask => (mask,id))

def c35304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35304 : Upper (D 7) (R 7) [34,192,10,65,257] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,257] 13 (by decide) (choices 1) [4,16,128] r35304 c35304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20358
  · exact u20359
  · exact u20360

def r35305 : Route 9 := (fun mask => (mask,id))

def c35305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35305 : Upper (D 7) (R 7) [34,192,10,65,260] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,260] 13 (by decide) (choices 1) [1,16,128] r35305 c35305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20361
  · exact u20362
  · exact u20363

def r35306 : Route 9 := (fun mask => (mask,id))

def c35306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35306 : Upper (D 7) (R 7) [34,192,10,65,288] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,288] 13 (by decide) (choices 1) [1,4,16,128] r35306 c35306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20364
  · exact u20365
  · exact u20366
  · exact u20367

def r35307 : Route 9 := (fun mask => (mask,id))

def c35307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35307 : Upper (D 7) (R 7) [34,192,10,65,384] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,384] 13 (by decide) (choices 1) [1,4,16] r35307 c35307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20368
  · exact u20369
  · exact u20370

def b35308 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 35 194 14 76 145 305 369 433 305), lower := (rows 35 194 14 76 145 32 64 128 256), losses := [] }

theorem u35308 : Upper (D 7) (R 7) [34,192,10,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35309 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 35 194 14 76 176 305 337 401 273), lower := (rows 35 194 14 76 176 32 64 128 256), losses := [] }

theorem u35309 : Upper (D 7) (R 7) [34,192,10,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35310 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 35 194 14 76 273 177 241 177 433), lower := (rows 35 194 14 76 273 32 64 128 256), losses := [] }

theorem u35310 : Upper (D 7) (R 7) [34,192,10,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35311 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 35 194 14 76 304 177 209 145 401), lower := (rows 35 194 14 76 304 32 64 128 256), losses := [] }

theorem u35311 : Upper (D 7) (R 7) [34,192,10,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35312 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 35 194 14 76 400 49 113 177 305), lower := (rows 35 194 14 76 400 32 64 128 256), losses := [] }

theorem u35312 : Upper (D 7) (R 7) [34,192,10,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35313 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 14 88 49 421 453 389 389), lower := (rows 35 194 14 88 49 32 64 128 256), losses := [] }

theorem u35313 : Upper (D 7) (R 7) [34,192,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35314 : Route 9 := (fun mask => (mask,id))

def c35314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35314 : Upper (D 7) (R 7) [34,192,10,80,36] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,36] 13 (by decide) (choices 1) [1,128,256] r35314 c35314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20371
  · exact u20372
  · exact u20373

def r35315 : Route 9 := (fun mask => (mask,id))

def c35315 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35315 : Upper (D 7) (R 7) [34,192,10,80,129] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,129] 13 (by decide) (choices 1) [1,4,256] r35315 c35315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20374
  · exact u20375
  · exact u20376

def b35316 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 28, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 14 88 148 289 353 417 289), lower := (rows 35 194 14 88 148 32 64 128 256), losses := [] }

theorem u35316 : Upper (D 7) (R 7) [34,192,10,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35317 : Route 9 := (fun mask => (mask,id))

def c35317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35317 : Upper (D 7) (R 7) [34,192,10,80,160] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,160] 13 (by decide) (choices 1) [1,4,256] r35317 c35317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20377
  · exact u20378
  · exact u20379

def r35318 : Route 9 := (fun mask => (mask,id))

def c35318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35318 : Upper (D 7) (R 7) [34,192,10,80,257] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,257] 13 (by decide) (choices 1) [1,4,128] r35318 c35318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20380
  · exact u20381
  · exact u20382

def r35319 : Route 9 := (fun mask => (mask,id))

def c35319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35319 : Upper (D 7) (R 7) [34,192,10,80,260] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,260] 13 (by decide) (choices 1) [1,128] r35319 c35319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20383
  · exact u20384

def r35320 : Route 9 := (fun mask => (mask,id))

def c35320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35320 : Upper (D 7) (R 7) [34,192,10,80,288] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,288] 13 (by decide) (choices 1) [1,4,128] r35320 c35320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20385
  · exact u20386
  · exact u20387

def r35321 : Route 9 := (fun mask => (mask,id))

def c35321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35321 : Upper (D 7) (R 7) [34,192,10,80,384] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,384] 13 (by decide) (choices 1) [1,4] r35321 c35321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20388
  · exact u20389

def r35322 : Route 9 := (fun mask => (mask,id))

def c35322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35322 : Upper (D 7) (R 7) [34,192,10,96,129] 13 := by
  apply FastRouting.sound _ _ [34,192,10,96,129] 13 (by decide) (choices 1) [1,4,16,256] r35322 c35322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20390
  · exact u20391
  · exact u20392
  · exact u20393

def r35323 : Route 9 := (fun mask => (mask,id))

def c35323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35323 : Upper (D 7) (R 7) [34,192,10,96,132] 13 := by
  apply FastRouting.sound _ _ [34,192,10,96,132] 13 (by decide) (choices 1) [1,16,256] r35323 c35323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20394
  · exact u20395
  · exact u20396

def r35324 : Route 9 := (fun mask => (mask,id))

def c35324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35324 : Upper (D 7) (R 7) [34,192,10,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,10,96,257] 13 (by decide) (choices 1) [1,4,16,128] r35324 c35324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20397
  · exact u20398
  · exact u20399
  · exact u20400

def r35325 : Route 9 := (fun mask => (mask,id))

def c35325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35325 : Upper (D 7) (R 7) [34,192,10,96,260] 13 := by
  apply FastRouting.sound _ _ [34,192,10,96,260] 13 (by decide) (choices 1) [1,16,128] r35325 c35325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20401
  · exact u20402
  · exact u20403

def r35326 : Route 9 := (fun mask => (mask,id))

def c35326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35326 : Upper (D 7) (R 7) [34,192,10,96,384] 13 := by
  apply FastRouting.sound _ _ [34,192,10,96,384] 13 (by decide) (choices 1) [1,4,16] r35326 c35326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20404
  · exact u20405
  · exact u20406

def b35327 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 14 200 52 305 337 401 273), lower := (rows 35 194 14 200 52 32 64 128 256), losses := [] }

theorem u35327 : Upper (D 7) (R 7) [34,192,10,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35328 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 14 200 273 53 117 181 309), lower := (rows 35 194 14 200 273 32 64 128 256), losses := [] }

theorem u35328 : Upper (D 7) (R 7) [34,192,10,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35329 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 14 200 276 49 113 177 305), lower := (rows 35 194 14 200 276 32 64 128 256), losses := [] }

theorem u35329 : Upper (D 7) (R 7) [34,192,10,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35330 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 14 200 304 53 85 149 277), lower := (rows 35 194 14 200 304 32 64 128 256), losses := [] }

theorem u35330 : Upper (D 7) (R 7) [34,192,10,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35331 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 194 14 265 49 244 212 212 468), lower := (rows 35 194 14 265 49 32 64 128 256), losses := [] }

theorem u35331 : Upper (D 7) (R 7) [34,192,10,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35332 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35332 : Upper (D 7) (R 7) [34,192,10,257,36] 13 := by
  apply FastRouting.sound _ _ [34,192,10,257,36] 13 (by decide) (choices 1) [1,16,64] r35332 c35332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20407
  · exact u20408
  · exact u20409

def r35333 : Route 9 := (fun mask => (mask,id))

def c35333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35333 : Upper (D 7) (R 7) [34,192,10,257,65] 13 := by
  apply FastRouting.sound _ _ [34,192,10,257,65] 13 (by decide) (choices 1) [4,16,128] r35333 c35333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20410
  · exact u20411
  · exact u20412

def r35334 : Route 9 := (fun mask => (mask,id))

def c35334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35334 : Upper (D 7) (R 7) [34,192,10,257,68] 13 := by
  apply FastRouting.sound _ _ [34,192,10,257,68] 13 (by decide) (choices 1) [1,16,128] r35334 c35334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20413
  · exact u20414
  · exact u20415

def r35335 : Route 9 := (fun mask => (mask,id))

def c35335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35335 : Upper (D 7) (R 7) [34,192,10,257,96] 13 := by
  apply FastRouting.sound _ _ [34,192,10,257,96] 13 (by decide) (choices 1) [1,4,16,128] r35335 c35335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20416
  · exact u20417
  · exact u20418
  · exact u20419

def b35336 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 14 265 208 53 117 181 309), lower := (rows 35 194 14 265 208 32 64 128 256), losses := [] }

theorem u35336 : Upper (D 7) (R 7) [34,192,10,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35337 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 194 14 268 49 241 209 209 465), lower := (rows 35 194 14 268 49 32 64 128 256), losses := [] }

theorem u35337 : Upper (D 7) (R 7) [34,192,10,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35338 : Route 9 := (fun mask => (mask,id))

def c35338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35338 : Upper (D 7) (R 7) [34,192,10,260,65] 13 := by
  apply FastRouting.sound _ _ [34,192,10,260,65] 13 (by decide) (choices 1) [1,16,128] r35338 c35338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20420
  · exact u20421
  · exact u20422

def r35339 : Route 9 := (fun mask => (mask,id))

def c35339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35339 : Upper (D 7) (R 7) [34,192,10,260,96] 13 := by
  apply FastRouting.sound _ _ [34,192,10,260,96] 13 (by decide) (choices 1) [1,16,128] r35339 c35339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20423
  · exact u20424
  · exact u20425

#print axioms u35339
end Delivery.IrregularNine14.P07
