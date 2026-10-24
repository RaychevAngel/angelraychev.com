import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0038
import IrregularNine14P06C0039

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12240 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 84 140 52 33 322 450 322), lower := (rows 11 35 84 140 52 33 64 128 256), losses := [] }

theorem u12240 : Upper (D 6) (R 6) [10,33,80,132,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12241 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 84 140 52 34 321 449 321), lower := (rows 11 35 84 140 52 34 64 128 256), losses := [] }

theorem u12241 : Upper (D 6) (R 6) [10,33,80,132,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12242 : PairBound 9 := { available := 259, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 140 52 96 323 387 259), lower := (rows 11 35 84 140 52 96 64 128 256), losses := [] }

theorem u12242 : Upper (D 6) (R 6) [10,33,80,132,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12243 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 84 140 52 288 67 195 323), lower := (rows 11 35 84 140 52 288 64 128 256), losses := [] }

theorem u12243 : Upper (D 6) (R 6) [10,33,80,132,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12243 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12244 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 140 273 34 100 228 356), lower := (rows 11 35 84 140 273 34 64 128 256), losses := [] }

theorem u12244 : Upper (D 6) (R 6) [10,33,80,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12245 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 84 140 273 36 98 226 354), lower := (rows 11 35 84 140 273 36 64 128 256), losses := [] }

theorem u12245 : Upper (D 6) (R 6) [10,33,80,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12246 : Route 9 := (fun mask => (mask,id))

def c12246 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12246 : Upper (D 6) (R 6) [10,33,80,132,257,64] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,257,64] 13 (by decide) (choices 1) [2,4,32] r12246 c12246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2311
  · exact u2312
  · exact u2313

def b12247 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 140 274 33 100 228 356), lower := (rows 11 35 84 140 274 33 64 128 256), losses := [] }

theorem u12247 : Upper (D 6) (R 6) [10,33,80,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12248 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 84 140 274 36 97 225 353), lower := (rows 11 35 84 140 274 36 64 128 256), losses := [] }

theorem u12248 : Upper (D 6) (R 6) [10,33,80,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12249 : Route 9 := (fun mask => (mask,id))

def c12249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12249 : Upper (D 6) (R 6) [10,33,80,132,258,64] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,258,64] 13 (by decide) (choices 1) [1,4,32] r12249 c12249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2314
  · exact u2315
  · exact u2316

def b12250 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 84 140 276 33 98 226 354), lower := (rows 11 35 84 140 276 33 64 128 256), losses := [] }

theorem u12250 : Upper (D 6) (R 6) [10,33,80,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12251 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 84 140 276 34 97 225 353), lower := (rows 11 35 84 140 276 34 64 128 256), losses := [] }

theorem u12251 : Upper (D 6) (R 6) [10,33,80,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12252 : Route 9 := (fun mask => (mask,id))

def c12252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12252 : Upper (D 6) (R 6) [10,33,80,132,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,260,64] 13 (by decide) (choices 1) [1,2,32] r12252 c12252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2317
  · exact u2318
  · exact u2319

def b12253 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 140 304 33 70 198 326), lower := (rows 11 35 84 140 304 33 64 128 256), losses := [] }

theorem u12253 : Upper (D 6) (R 6) [10,33,80,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12254 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 140 304 34 69 197 325), lower := (rows 11 35 84 140 304 34 64 128 256), losses := [] }

theorem u12254 : Upper (D 6) (R 6) [10,33,80,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12255 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 84 140 304 36 67 195 323), lower := (rows 11 35 84 140 304 36 64 128 256), losses := [] }

theorem u12255 : Upper (D 6) (R 6) [10,33,80,132,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12256 : Route 9 := (fun mask => (mask,id))

def c12256 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12256 : Upper (D 6) (R 6) [10,33,80,132,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,288,64] 13 (by decide) (choices 1) [1,2,4] r12256 c12256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2320
  · exact u2321
  · exact u2322

def b12257 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 21 34 356 420 292), lower := (rows 11 35 84 200 21 34 64 128 256), losses := [] }

theorem u12257 : Upper (D 6) (R 6) [10,33,80,192,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12258 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 200 21 36 354 418 290), lower := (rows 11 35 84 200 21 36 64 128 256), losses := [] }

theorem u12258 : Upper (D 6) (R 6) [10,33,80,192,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12259 : Route 9 := (fun mask => (mask,id))

def c12259 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12259 : Upper (D 6) (R 6) [10,33,80,192,5,256] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,5,256] 13 (by decide) (choices 1) [2,4,32] r12259 c12259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2323
  · exact u2324
  · exact u2325

def b12260 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 22 33 356 420 292), lower := (rows 11 35 84 200 22 33 64 128 256), losses := [] }

theorem u12260 : Upper (D 6) (R 6) [10,33,80,192,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12261 : PairBound 9 := { available := 289, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 200 22 36 353 417 289), lower := (rows 11 35 84 200 22 36 64 128 256), losses := [] }

theorem u12261 : Upper (D 6) (R 6) [10,33,80,192,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12262 : Route 9 := (fun mask => (mask,id))

def c12262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12262 : Upper (D 6) (R 6) [10,33,80,192,6,256] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,6,256] 13 (by decide) (choices 1) [1,4,32] r12262 c12262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2326
  · exact u2327
  · exact u2328

def b12263 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 52 33 326 390 262), lower := (rows 11 35 84 200 52 33 64 128 256), losses := [] }

theorem u12263 : Upper (D 6) (R 6) [10,33,80,192,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12264 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 52 34 325 389 261), lower := (rows 11 35 84 200 52 34 64 128 256), losses := [] }

theorem u12264 : Upper (D 6) (R 6) [10,33,80,192,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12265 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 84 200 52 36 323 387 259), lower := (rows 11 35 84 200 52 36 64 128 256), losses := [] }

theorem u12265 : Upper (D 6) (R 6) [10,33,80,192,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12266 : Route 9 := (fun mask => (mask,id))

def c12266 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12266 : Upper (D 6) (R 6) [10,33,80,192,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,36,256] 13 (by decide) (choices 1) [1,2,4] r12266 c12266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2329
  · exact u2330
  · exact u2331

def b12267 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 273 34 100 164 292), lower := (rows 11 35 84 200 273 34 64 128 256), losses := [] }

theorem u12267 : Upper (D 6) (R 6) [10,33,80,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12268 : Route 9 := (fun mask => (mask,id))

def c12268 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12268 : Upper (D 6) (R 6) [10,33,80,192,257,4] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,257,4] 13 (by decide) (choices 1) [2,4,32] r12268 c12268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2332
  · exact u2333
  · exact u2334

def b12269 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 274 33 100 164 292), lower := (rows 11 35 84 200 274 33 64 128 256), losses := [] }

theorem u12269 : Upper (D 6) (R 6) [10,33,80,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12270 : Route 9 := (fun mask => (mask,id))

def c12270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12270 : Upper (D 6) (R 6) [10,33,80,192,258,4] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,258,4] 13 (by decide) (choices 1) [1,4,32] r12270 c12270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2335
  · exact u2336
  · exact u2337

def b12271 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 276 33 102 166 294), lower := (rows 11 35 84 200 276 33 64 128 256), losses := [] }

theorem u12271 : Upper (D 6) (R 6) [10,33,80,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12272 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 276 34 101 165 293), lower := (rows 11 35 84 200 276 34 64 128 256), losses := [] }

theorem u12272 : Upper (D 6) (R 6) [10,33,80,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12273 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 200 276 36 99 163 291), lower := (rows 11 35 84 200 276 36 64 128 256), losses := [] }

theorem u12273 : Upper (D 6) (R 6) [10,33,80,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12274 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 304 33 70 134 262), lower := (rows 11 35 84 200 304 33 64 128 256), losses := [] }

theorem u12274 : Upper (D 6) (R 6) [10,33,80,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12275 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 200 304 34 69 133 261), lower := (rows 11 35 84 200 304 34 64 128 256), losses := [] }

theorem u12275 : Upper (D 6) (R 6) [10,33,80,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12276 : Route 9 := (fun mask => (mask,id))

def c12276 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12276 : Upper (D 6) (R 6) [10,33,80,192,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,288,4] 13 (by decide) (choices 1) [1,2,4] r12276 c12276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2338
  · exact u2339
  · exact u2340

def b12277 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 392 21 34 100 228 356), lower := (rows 11 35 84 392 21 34 64 128 256), losses := [] }

theorem u12277 : Upper (D 6) (R 6) [10,33,80,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12278 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 392 21 36 98 226 354), lower := (rows 11 35 84 392 21 36 64 128 256), losses := [] }

theorem u12278 : Upper (D 6) (R 6) [10,33,80,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12279 : Route 9 := (fun mask => (mask,id))

def c12279 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12279 : Upper (D 6) (R 6) [10,33,80,384,5,64] 13 := by
  apply FastRouting.sound _ _ [10,33,80,384,5,64] 13 (by decide) (choices 1) [2,4,32] r12279 c12279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2341
  · exact u2342
  · exact u2343

def b12280 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 392 22 33 100 228 356), lower := (rows 11 35 84 392 22 33 64 128 256), losses := [] }

theorem u12280 : Upper (D 6) (R 6) [10,33,80,384,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12281 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 392 22 36 97 225 353), lower := (rows 11 35 84 392 22 36 64 128 256), losses := [] }

theorem u12281 : Upper (D 6) (R 6) [10,33,80,384,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12282 : Route 9 := (fun mask => (mask,id))

def c12282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12282 : Upper (D 6) (R 6) [10,33,80,384,6,64] 13 := by
  apply FastRouting.sound _ _ [10,33,80,384,6,64] 13 (by decide) (choices 1) [1,4,32] r12282 c12282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2344
  · exact u2345
  · exact u2346

def b12283 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 392 52 33 70 198 326), lower := (rows 11 35 84 392 52 33 64 128 256), losses := [] }

theorem u12283 : Upper (D 6) (R 6) [10,33,80,384,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12284 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 392 52 34 69 197 325), lower := (rows 11 35 84 392 52 34 64 128 256), losses := [] }

theorem u12284 : Upper (D 6) (R 6) [10,33,80,384,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12285 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 84 392 52 36 67 195 323), lower := (rows 11 35 84 392 52 36 64 128 256), losses := [] }

theorem u12285 : Upper (D 6) (R 6) [10,33,80,384,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12286 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 392 52 96 71 135 263), lower := (rows 11 35 84 392 52 96 64 128 256), losses := [] }

theorem u12286 : Upper (D 6) (R 6) [10,33,80,384,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12287 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 25 148 34 324 452 324), lower := (rows 11 35 100 25 148 34 64 128 256), losses := [] }

theorem u12287 : Upper (D 6) (R 6) [10,33,96,17,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12288 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 25 148 36 322 450 322), lower := (rows 11 35 100 25 148 36 64 128 256), losses := [] }

theorem u12288 : Upper (D 6) (R 6) [10,33,96,17,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12289 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 25 148 96 326 390 262), lower := (rows 11 35 100 25 148 96 64 128 256), losses := [] }

theorem u12289 : Upper (D 6) (R 6) [10,33,96,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12290 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 100 25 148 288 70 198 326), lower := (rows 11 35 100 25 148 288 64 128 256), losses := [] }

theorem u12290 : Upper (D 6) (R 6) [10,33,96,17,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12290 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12291 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 25 208 34 324 388 260), lower := (rows 11 35 100 25 208 34 64 128 256), losses := [] }

theorem u12291 : Upper (D 6) (R 6) [10,33,96,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12292 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 100 25 208 36 326 390 262), lower := (rows 11 35 100 25 208 36 64 128 256), losses := [] }

theorem u12292 : Upper (D 6) (R 6) [10,33,96,17,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12293 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 100 25 208 288 70 134 262), lower := (rows 11 35 100 25 208 288 64 128 256), losses := [] }

theorem u12293 : Upper (D 6) (R 6) [10,33,96,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12293 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12294 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 25 400 34 68 196 324), lower := (rows 11 35 100 25 400 34 64 128 256), losses := [] }

theorem u12294 : Upper (D 6) (R 6) [10,33,96,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12295 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 100 25 400 36 70 198 326), lower := (rows 11 35 100 25 400 36 64 128 256), losses := [] }

theorem u12295 : Upper (D 6) (R 6) [10,33,96,17,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12296 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 25 400 96 70 134 262), lower := (rows 11 35 100 25 400 96 64 128 256), losses := [] }

theorem u12296 : Upper (D 6) (R 6) [10,33,96,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12297 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 100 28 145 34 324 452 324), lower := (rows 11 35 100 28 145 34 64 128 256), losses := [] }

theorem u12297 : Upper (D 6) (R 6) [10,33,96,20,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12298 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 100 28 145 36 322 450 322), lower := (rows 11 35 100 28 145 36 64 128 256), losses := [] }

theorem u12298 : Upper (D 6) (R 6) [10,33,96,20,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12299 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 28 145 96 326 390 262), lower := (rows 11 35 100 28 145 96 64 128 256), losses := [] }

theorem u12299 : Upper (D 6) (R 6) [10,33,96,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12299
end Delivery.IrregularNine14.P06
