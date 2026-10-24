import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0038
import IrregularNine14P07C0039

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14220 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 280 49 96 195 131 387), lower := (rows 7 98 140 280 49 96 64 128 256), losses := [] }

theorem u14220 : Upper (D 7) (R 7) [6,96,136,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14221 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 330, targets := 128 }], pairs := [(1,7),(2,5),(3,7),(4,1)], upper := (rows 7 98 140 280 49 160 67 195 323), lower := (rows 7 98 140 280 49 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 164 64 128 256), good := (rows 53 96 172 280 49 160 64 160 256) },{ target := 5, region := (rows 1 2 20 24 16 0 65 129 257), good := (rows 455 66 140 284 477 128 64 128 256) }] }

theorem u14221 : Upper (D 7) (R 7) [6,96,136,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14222 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 362, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 7 98 140 280 145 33 98 226 354), lower := (rows 7 98 140 280 145 33 64 128 256), losses := [] }

theorem u14222 : Upper (D 7) (R 7) [6,96,136,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14223 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 362, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 7 98 140 280 145 34 97 225 353), lower := (rows 7 98 140 280 145 34 64 128 256), losses := [] }

theorem u14223 : Upper (D 7) (R 7) [6,96,136,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14224 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 280 145 96 99 163 291), lower := (rows 7 98 140 280 145 96 64 128 256), losses := [] }

theorem u14224 : Upper (D 7) (R 7) [6,96,136,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14225 : Route 9 := (fun mask => (mask,id))

def c14225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14225 : Upper (D 7) (R 7) [6,96,136,272,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,130,1] 13 (by decide) (choices 1) [1,32] r14225 c14225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2314
  · exact u2315

def b14226 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 280 146 96 97 161 289), lower := (rows 7 98 140 280 146 96 64 128 256), losses := [] }

theorem u14226 : Upper (D 7) (R 7) [6,96,136,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14227 : Route 9 := (fun mask => (mask,id))

def c14227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14227 : Upper (D 7) (R 7) [6,96,136,272,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,160,1] 13 (by decide) (choices 1) [1,2] r14227 c14227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2316
  · exact u2317

def r14228 : Route 9 := (fun mask => (mask,id))

def c14228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14228 : Upper (D 7) (R 7) [6,96,136,272,160,2] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,160,2] 13 (by decide) (choices 1) [1] r14228 c14228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u2318

def b14229 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 280 176 96 67 131 259), lower := (rows 7 98 140 280 176 96 64 128 256), losses := [] }

theorem u14229 : Upper (D 7) (R 7) [6,96,136,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14230 : Route 9 := (fun mask => (mask,id))

def c14230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14230 : Upper (D 7) (R 7) [6,96,136,288,65,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,65,1] 13 (by decide) (choices 1) [2,16,128] r14230 c14230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2319
  · exact u2320
  · exact u2321

def b14231 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 140 296 81 34 209 145 401), lower := (rows 7 98 140 296 81 34 64 128 256), losses := [] }

theorem u14231 : Upper (D 7) (R 7) [6,96,136,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14232 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 296 81 48 195 131 387), lower := (rows 7 98 140 296 81 48 64 128 256), losses := [] }

theorem u14232 : Upper (D 7) (R 7) [6,96,136,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14232 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14233 : Route 9 := (fun mask => (mask,id))

def c14233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14233 : Upper (D 7) (R 7) [6,96,136,288,65,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,65,128] 13 (by decide) (choices 1) [1,2,16] r14233 c14233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2322
  · exact u2323
  · exact u2324

def r14234 : Route 9 := (fun mask => (mask,id))

def c14234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14234 : Upper (D 7) (R 7) [6,96,136,288,129,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,129,1] 13 (by decide) (choices 1) [2,16] r14234 c14234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2325
  · exact u2326

def b14235 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,5)], upper := (rows 7 98 140 296 145 34 81 209 337), lower := (rows 7 98 140 296 145 34 64 128 256), losses := [] }

theorem u14235 : Upper (D 7) (R 7) [6,96,136,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14236 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,7),(3,7),(4,5)], upper := (rows 7 98 140 296 145 48 67 195 323), lower := (rows 7 98 140 296 145 48 64 128 256), losses := [] }

theorem u14236 : Upper (D 7) (R 7) [6,96,136,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14236 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14237 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 296 145 96 83 147 275), lower := (rows 7 98 140 296 145 96 64 128 256), losses := [] }

theorem u14237 : Upper (D 7) (R 7) [6,96,136,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14238 : Route 9 := (fun mask => (mask,id))

def c14238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14238 : Upper (D 7) (R 7) [6,96,136,288,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,130,1] 13 (by decide) (choices 1) [1,16] r14238 c14238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2327
  · exact u2328

def r14239 : Route 9 := (fun mask => (mask,id))

def c14239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14239 : Upper (D 7) (R 7) [6,96,136,288,130,16] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,130,16] 13 (by decide) (choices 1) [1] r14239 c14239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u2329

def b14240 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 296 146 96 81 145 273), lower := (rows 7 98 140 296 146 96 64 128 256), losses := [] }

theorem u14240 : Upper (D 7) (R 7) [6,96,136,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14241 : Route 9 := (fun mask => (mask,id))

def c14241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14241 : Upper (D 7) (R 7) [6,96,136,288,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,192,1] 13 (by decide) (choices 1) [1,2,16] r14241 c14241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2330
  · exact u2331
  · exact u2332

def b14242 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 140 296 208 34 81 145 273), lower := (rows 7 98 140 296 208 34 64 128 256), losses := [] }

theorem u14242 : Upper (D 7) (R 7) [6,96,136,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14243 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 296 208 48 67 131 259), lower := (rows 7 98 140 296 208 48 64 128 256), losses := [] }

theorem u14243 : Upper (D 7) (R 7) [6,96,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14243 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14244 : Route 9 := (fun mask => (mask,id))

def c14244 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u14244 : Upper (D 7) (R 7) [6,96,160,17,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,192,1] 13 (by decide) (choices 1) [2,8,256] r14244 c14244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2333
  · exact u2334
  · exact u2335

def b14245 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 25 208 34 329 393 265), lower := (rows 7 98 164 25 208 34 64 128 256), losses := [] }

theorem u14245 : Upper (D 7) (R 7) [6,96,160,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14246 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 25 208 40 323 387 259), lower := (rows 7 98 164 25 208 40 64 128 256), losses := [] }

theorem u14246 : Upper (D 7) (R 7) [6,96,160,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14246 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14247 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(3,5),(4,5)], upper := (rows 7 98 164 25 208 288 75 139 267), lower := (rows 7 98 164 25 208 288 64 128 256), losses := [] }

theorem u14247 : Upper (D 7) (R 7) [6,96,160,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14247 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14248 : Route 9 := (fun mask => (mask,id))

def c14248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14248 : Upper (D 7) (R 7) [6,96,160,17,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,258,1] 13 (by decide) (choices 1) [8,128] r14248 c14248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2336
  · exact u2337

def b14249 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 164 25 274 40 193 193 449), lower := (rows 7 98 164 25 274 40 64 128 256), losses := [] }

theorem u14249 : Upper (D 7) (R 7) [6,96,160,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14249 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14250 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 25 274 96 201 137 393), lower := (rows 7 98 164 25 274 96 64 128 256), losses := [] }

theorem u14250 : Upper (D 7) (R 7) [6,96,160,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14251 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 25 274 160 73 201 329), lower := (rows 7 98 164 25 274 160 64 128 256), losses := [] }

theorem u14251 : Upper (D 7) (R 7) [6,96,160,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14252 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 7 98 164 25 280 33 194 194 450), lower := (rows 7 98 164 25 280 33 64 128 256), losses := [] }

theorem u14252 : Upper (D 7) (R 7) [6,96,160,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14253 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 25 280 34 193 193 449), lower := (rows 7 98 164 25 280 34 64 128 256), losses := [] }

theorem u14253 : Upper (D 7) (R 7) [6,96,160,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14254 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 25 280 96 195 131 387), lower := (rows 7 98 164 25 280 96 64 128 256), losses := [] }

theorem u14254 : Upper (D 7) (R 7) [6,96,160,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14255 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 25 280 160 67 195 323), lower := (rows 7 98 164 25 280 160 64 128 256), losses := [] }

theorem u14255 : Upper (D 7) (R 7) [6,96,160,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14256 : Route 9 := (fun mask => (mask,id))

def c14256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14256 : Upper (D 7) (R 7) [6,96,160,17,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,320,1] 13 (by decide) (choices 1) [2,8,128] r14256 c14256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2338
  · exact u2339
  · exact u2340

def b14257 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 25 336 34 201 137 393), lower := (rows 7 98 164 25 336 34 64 128 256), losses := [] }

theorem u14257 : Upper (D 7) (R 7) [6,96,160,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14258 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 25 336 40 195 131 387), lower := (rows 7 98 164 25 336 40 64 128 256), losses := [] }

theorem u14258 : Upper (D 7) (R 7) [6,96,160,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14258 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14259 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 25 336 160 75 139 267), lower := (rows 7 98 164 25 336 160 64 128 256), losses := [] }

theorem u14259 : Upper (D 7) (R 7) [6,96,160,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14260 : Route 9 := (fun mask => (mask,id))

def c14260 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14260 : Upper (D 7) (R 7) [6,96,160,17,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,384,1] 13 (by decide) (choices 1) [2,8] r14260 c14260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2341
  · exact u2342

def b14261 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 25 400 34 73 201 329), lower := (rows 7 98 164 25 400 34 64 128 256), losses := [] }

theorem u14261 : Upper (D 7) (R 7) [6,96,160,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14262 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 164 25 400 40 67 195 323), lower := (rows 7 98 164 25 400 40 64 128 256), losses := [] }

theorem u14262 : Upper (D 7) (R 7) [6,96,160,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14262 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14263 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 25 400 96 75 139 267), lower := (rows 7 98 164 25 400 96 64 128 256), losses := [] }

theorem u14263 : Upper (D 7) (R 7) [6,96,160,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14264 : Route 9 := (fun mask => (mask,id))

def c14264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14264 : Upper (D 7) (R 7) [6,96,160,18,257,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,257,1] 13 (by decide) (choices 1) [8,128] r14264 c14264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2343
  · exact u2344

def b14265 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 98 164 26 273 40 193 193 449), lower := (rows 7 98 164 26 273 40 64 128 256), losses := [] }

theorem u14265 : Upper (D 7) (R 7) [6,96,160,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14265 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14266 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 26 273 96 201 137 393), lower := (rows 7 98 164 26 273 96 64 128 256), losses := [] }

theorem u14266 : Upper (D 7) (R 7) [6,96,160,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14267 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 26 273 160 73 201 329), lower := (rows 7 98 164 26 273 160 64 128 256), losses := [] }

theorem u14267 : Upper (D 7) (R 7) [6,96,160,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14268 : Route 9 := (fun mask => (mask,id))

def c14268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14268 : Upper (D 7) (R 7) [6,96,160,18,264,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,264,1] 13 (by decide) (choices 1) [1,128] r14268 c14268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2345
  · exact u2346

def b14269 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 26 280 96 193 129 385), lower := (rows 7 98 164 26 280 96 64 128 256), losses := [] }

theorem u14269 : Upper (D 7) (R 7) [6,96,160,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14270 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 98 164 26 280 160 65 193 321), lower := (rows 7 98 164 26 280 160 64 128 256), losses := [] }

theorem u14270 : Upper (D 7) (R 7) [6,96,160,18,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14271 : Route 9 := (fun mask => (mask,id))

def c14271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14271 : Upper (D 7) (R 7) [6,96,160,18,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,384,1] 13 (by decide) (choices 1) [1,8] r14271 c14271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2347
  · exact u2348

def b14272 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 164 26 400 40 65 193 321), lower := (rows 7 98 164 26 400 40 64 128 256), losses := [] }

theorem u14272 : Upper (D 7) (R 7) [6,96,160,18,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14272 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14273 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 164 26 400 96 73 137 265), lower := (rows 7 98 164 26 400 96 64 128 256), losses := [] }

theorem u14273 : Upper (D 7) (R 7) [6,96,160,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14274 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 73 146 33 344 408 280), lower := (rows 7 98 164 73 146 33 64 128 256), losses := [] }

theorem u14274 : Upper (D 7) (R 7) [6,96,160,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14275 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 73 146 40 337 401 273), lower := (rows 7 98 164 73 146 40 64 128 256), losses := [] }

theorem u14275 : Upper (D 7) (R 7) [6,96,160,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14275 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14276 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 98 164 73 146 48 329 393 265), lower := (rows 7 98 164 73 146 48 64 128 256), losses := [] }

theorem u14276 : Upper (D 7) (R 7) [6,96,160,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14276 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14277 : Route 9 := (fun mask => (mask,id))

def c14277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14277 : Upper (D 7) (R 7) [6,96,160,65,130,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,130,256] 13 (by decide) (choices 1) [1,8,16] r14277 c14277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2349
  · exact u2350
  · exact u2351

def b14278 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(2,1),(3,5),(4,5)], upper := (rows 7 98 164 73 152 33 338 402 274), lower := (rows 7 98 164 73 152 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 41 64 128 256), good := (rows 37 96 164 105 188 33 64 128 256) }] }

theorem u14278 : Upper (D 7) (R 7) [6,96,160,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14279 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 164 73 152 34 337 401 273), lower := (rows 7 98 164 73 152 34 64 128 256), losses := [] }

theorem u14279 : Upper (D 7) (R 7) [6,96,160,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14279
end Delivery.IrregularNine14.P07
