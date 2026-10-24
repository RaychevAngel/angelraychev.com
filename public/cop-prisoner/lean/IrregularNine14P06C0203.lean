import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0037
import IrregularNine14P06C0038

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12180 : Route 9 := (fun mask => (mask,id))

def c12180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12180 : Upper (D 6) (R 6) [10,33,66,144,96,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,96,256] 13 (by decide) (choices 1) [1,4] r12180 c12180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2266
  · exact u2267

def b12181 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 70 152 273 36 100 228 356), lower := (rows 11 35 70 152 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) },{ target := 1, region := (rows 1 0 4 14 18 36 100 164 292), good := (rows 25 505 508 152 273 492 64 128 256) }] }

theorem u12181 : Upper (D 6) (R 6) [10,33,66,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12182 : Route 9 := (fun mask => (mask,id))

def c12182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12182 : Upper (D 6) (R 6) [10,33,66,144,257,64] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,257,64] 13 (by decide) (choices 1) [4,32] r12182 c12182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2268
  · exact u2269

def b12183 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 152 276 33 100 228 356), lower := (rows 11 35 70 152 276 33 64 128 256), losses := [] }

theorem u12183 : Upper (D 6) (R 6) [10,33,66,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12184 : PairBound 9 := { available := 97, camps := [], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 35 70 152 276 36 97 225 353), lower := (rows 11 35 70 152 276 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 52 66 130 258), good := (rows 457 481 508 184 316 60 64 128 256) },{ target := 6, region := (rows 9 10 4 8 16 52 0 128 256), good := (rows 11 35 38 187 308 36 0 128 256) }] }

theorem u12184 : Upper (D 6) (R 6) [10,33,66,144,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12185 : Route 9 := (fun mask => (mask,id))

def c12185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12185 : Upper (D 6) (R 6) [10,33,66,144,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,260,64] 13 (by decide) (choices 1) [1,4,32] r12185 c12185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2270
  · exact u2271
  · exact u2272

def b12186 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 152 304 33 68 196 324), lower := (rows 11 35 70 152 304 33 64 128 256), losses := [] }

theorem u12186 : Upper (D 6) (R 6) [10,33,66,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12187 : Route 9 := (fun mask => (mask,id))

def c12187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12187 : Upper (D 6) (R 6) [10,33,66,144,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,288,4] 13 (by decide) (choices 1) [1,4] r12187 c12187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2273
  · exact u2274

def r12188 : Route 9 := (fun mask => (mask,id))

def c12188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12188 : Upper (D 6) (R 6) [10,33,66,144,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,288,64] 13 (by decide) (choices 1) [1,4] r12188 c12188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2275
  · exact u2276

def b12189 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 152 336 33 100 164 292), lower := (rows 11 35 70 152 336 33 64 128 256), losses := [] }

theorem u12189 : Upper (D 6) (R 6) [10,33,66,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12190 : Route 9 := (fun mask => (mask,id))

def c12190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12190 : Upper (D 6) (R 6) [10,33,66,144,320,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,320,4] 13 (by decide) (choices 1) [1,4,32] r12190 c12190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2277
  · exact u2278
  · exact u2279

def b12191 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 200 52 33 340 404 276), lower := (rows 11 35 70 200 52 33 64 128 256), losses := [] }

theorem u12191 : Upper (D 6) (R 6) [10,33,66,192,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12192 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 70 200 52 36 337 401 273), lower := (rows 11 35 70 200 52 36 64 128 256), losses := [] }

theorem u12192 : Upper (D 6) (R 6) [10,33,66,192,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12193 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 70 200 52 48 325 389 261), lower := (rows 11 35 70 200 52 48 64 128 256), losses := [] }

theorem u12193 : Upper (D 6) (R 6) [10,33,66,192,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12193 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12194 : Route 9 := (fun mask => (mask,id))

def c12194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12194 : Upper (D 6) (R 6) [10,33,66,192,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,36,256] 13 (by decide) (choices 1) [1,4,16] r12194 c12194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2280
  · exact u2281
  · exact u2282

def r12195 : Route 9 := (fun mask => (mask,id))

def c12195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12195 : Upper (D 6) (R 6) [10,33,66,192,257,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,257,4] 13 (by decide) (choices 1) [4,16,32] r12195 c12195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2283
  · exact u2284
  · exact u2285

def b12196 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 70 200 273 48 100 164 292), lower := (rows 11 35 70 200 273 48 64 128 256), losses := [] }

theorem u12196 : Upper (D 6) (R 6) [10,33,66,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12196 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12197 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 200 276 33 116 180 308), lower := (rows 11 35 70 200 276 33 64 128 256), losses := [] }

theorem u12197 : Upper (D 6) (R 6) [10,33,66,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12198 : Route 9 := (fun mask => (mask,id))

def c12198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12198 : Upper (D 6) (R 6) [10,33,66,192,260,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,260,4] 13 (by decide) (choices 1) [1,16,32] r12198 c12198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2286
  · exact u2287
  · exact u2288

def r12199 : Route 9 := (fun mask => (mask,id))

def c12199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12199 : Upper (D 6) (R 6) [10,33,66,192,260,16] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,260,16] 13 (by decide) (choices 1) [1,4,32] r12199 c12199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2289
  · exact u2290
  · exact u2291

def b12200 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 200 304 33 84 148 276), lower := (rows 11 35 70 200 304 33 64 128 256), losses := [] }

theorem u12200 : Upper (D 6) (R 6) [10,33,66,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12201 : Route 9 := (fun mask => (mask,id))

def c12201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12201 : Upper (D 6) (R 6) [10,33,66,192,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192,288,4] 13 (by decide) (choices 1) [1,4,16] r12201 c12201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2292
  · exact u2293
  · exact u2294

def b12202 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 70 200 304 48 69 133 261), lower := (rows 11 35 70 200 304 48 64 128 256), losses := [] }

theorem u12202 : Upper (D 6) (R 6) [10,33,66,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12202 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12203 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 488, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 70 392 21 36 112 240 368), lower := (rows 11 35 70 392 21 36 64 128 256), losses := [] }

theorem u12203 : Upper (D 6) (R 6) [10,33,66,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12204 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 70 392 21 48 100 228 356), lower := (rows 11 35 70 392 21 48 64 128 256), losses := [] }

theorem u12204 : Upper (D 6) (R 6) [10,33,66,384,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12204 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12205 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 488, targets := 3 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 35 70 392 21 96 116 180 308), lower := (rows 11 35 70 392 21 96 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 100 64 128 256), good := (rows 11 35 98 392 51 96 96 128 256) }] }

theorem u12205 : Upper (D 6) (R 6) [10,33,66,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12206 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 392 52 33 84 212 340), lower := (rows 11 35 70 392 52 33 64 128 256), losses := [] }

theorem u12206 : Upper (D 6) (R 6) [10,33,66,384,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12207 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 70 392 52 36 81 209 337), lower := (rows 11 35 70 392 52 36 64 128 256), losses := [] }

theorem u12207 : Upper (D 6) (R 6) [10,33,66,384,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12208 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 70 392 52 48 69 197 325), lower := (rows 11 35 70 392 52 48 64 128 256), losses := [] }

theorem u12208 : Upper (D 6) (R 6) [10,33,66,384,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12208 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12209 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 70 392 52 96 85 149 277), lower := (rows 11 35 70 392 52 96 64 128 256), losses := [] }

theorem u12209 : Upper (D 6) (R 6) [10,33,66,384,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12210 : Route 9 := (fun mask => (mask,id))

def c12210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12210 : Upper (D 6) (R 6) [10,33,66,384,65,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,384,65,4] 13 (by decide) (choices 1) [4,16,32] r12210 c12210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2295
  · exact u2296
  · exact u2297

def b12211 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 70 392 81 48 100 164 292), lower := (rows 11 35 70 392 81 48 64 128 256), losses := [] }

theorem u12211 : Upper (D 6) (R 6) [10,33,66,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12211 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12212 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 392 112 33 84 148 276), lower := (rows 11 35 70 392 112 33 64 128 256), losses := [] }

theorem u12212 : Upper (D 6) (R 6) [10,33,66,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12213 : Route 9 := (fun mask => (mask,id))

def c12213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12213 : Upper (D 6) (R 6) [10,33,66,384,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,384,96,4] 13 (by decide) (choices 1) [1,4,16] r12213 c12213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2298
  · exact u2299
  · exact u2300

def b12214 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 70 392 112 48 69 133 261), lower := (rows 11 35 70 392 112 48 64 128 256), losses := [] }

theorem u12214 : Upper (D 6) (R 6) [10,33,66,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12214 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12215 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 13 176 34 324 452 324), lower := (rows 11 35 84 13 176 34 64 128 256), losses := [] }

theorem u12215 : Upper (D 6) (R 6) [10,33,80,5,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12216 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 13 176 36 322 450 322), lower := (rows 11 35 84 13 176 36 64 128 256), losses := [] }

theorem u12216 : Upper (D 6) (R 6) [10,33,80,5,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12217 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 84 13 176 96 326 390 262), lower := (rows 11 35 84 13 176 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 100 64 128 256), good := (rows 11 35 112 43 176 96 96 128 256) }] }

theorem u12217 : Upper (D 6) (R 6) [10,33,80,5,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12218 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 84 13 176 288 70 198 326), lower := (rows 11 35 84 13 176 288 64 128 256), losses := [] }

theorem u12218 : Upper (D 6) (R 6) [10,33,80,5,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12218 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12219 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 13 400 34 100 228 356), lower := (rows 11 35 84 13 400 34 64 128 256), losses := [] }

theorem u12219 : Upper (D 6) (R 6) [10,33,80,5,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12220 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 84 13 400 36 98 226 354), lower := (rows 11 35 84 13 400 36 64 128 256), losses := [] }

theorem u12220 : Upper (D 6) (R 6) [10,33,80,5,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12221 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 84 13 400 96 102 166 294), lower := (rows 11 35 84 13 400 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 100 64 128 256), good := (rows 11 35 112 43 400 96 96 128 256) }] }

theorem u12221 : Upper (D 6) (R 6) [10,33,80,5,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12222 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 73 148 34 356 420 292), lower := (rows 11 35 84 73 148 34 64 128 256), losses := [] }

theorem u12222 : Upper (D 6) (R 6) [10,33,80,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12223 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 73 148 36 354 418 290), lower := (rows 11 35 84 73 148 36 64 128 256), losses := [] }

theorem u12223 : Upper (D 6) (R 6) [10,33,80,65,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12224 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 84 73 148 288 102 166 294), lower := (rows 11 35 84 73 148 288 64 128 256), losses := [] }

theorem u12224 : Upper (D 6) (R 6) [10,33,80,65,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12224 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12225 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 73 176 34 324 388 260), lower := (rows 11 35 84 73 176 34 64 128 256), losses := [] }

theorem u12225 : Upper (D 6) (R 6) [10,33,80,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12226 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 84 73 176 36 326 390 262), lower := (rows 11 35 84 73 176 36 64 128 256), losses := [{ target := 2, region := (rows 37 50 0 12 16 32 64 128 256), good := (rows 11 35 91 73 179 43 64 128 256) }] }

theorem u12226 : Upper (D 6) (R 6) [10,33,80,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12227 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 84 73 176 288 70 134 262), lower := (rows 11 35 84 73 176 288 64 128 256), losses := [] }

theorem u12227 : Upper (D 6) (R 6) [10,33,80,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12227 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12228 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 73 400 34 100 164 292), lower := (rows 11 35 84 73 400 34 64 128 256), losses := [] }

theorem u12228 : Upper (D 6) (R 6) [10,33,80,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12229 : Route 9 := (fun mask => (mask,id))

def c12229 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12229 : Upper (D 6) (R 6) [10,33,80,65,384,4] 13 := by
  apply FastRouting.sound _ _ [10,33,80,65,384,4] 13 (by decide) (choices 1) [2,4,32] r12229 c12229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2301
  · exact u2302
  · exact u2303

def b12230 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 137 52 34 324 452 324), lower := (rows 11 35 84 137 52 34 64 128 256), losses := [] }

theorem u12230 : Upper (D 6) (R 6) [10,33,80,129,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12231 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 84 137 52 36 322 450 322), lower := (rows 11 35 84 137 52 36 64 128 256), losses := [] }

theorem u12231 : Upper (D 6) (R 6) [10,33,80,129,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12232 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 52 96 326 390 262), lower := (rows 11 35 84 137 52 96 64 128 256), losses := [] }

theorem u12232 : Upper (D 6) (R 6) [10,33,80,129,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12233 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 84 137 52 288 70 198 326), lower := (rows 11 35 84 137 52 288 64 128 256), losses := [] }

theorem u12233 : Upper (D 6) (R 6) [10,33,80,129,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12233 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12234 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 137 276 34 100 228 356), lower := (rows 11 35 84 137 276 34 64 128 256), losses := [] }

theorem u12234 : Upper (D 6) (R 6) [10,33,80,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12235 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 137 276 36 98 226 354), lower := (rows 11 35 84 137 276 36 64 128 256), losses := [] }

theorem u12235 : Upper (D 6) (R 6) [10,33,80,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12236 : Route 9 := (fun mask => (mask,id))

def c12236 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12236 : Upper (D 6) (R 6) [10,33,80,129,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,80,129,260,64] 13 (by decide) (choices 1) [2,4,32] r12236 c12236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2304
  · exact u2305
  · exact u2306

def b12237 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 137 304 34 68 196 324), lower := (rows 11 35 84 137 304 34 64 128 256), losses := [] }

theorem u12237 : Upper (D 6) (R 6) [10,33,80,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12238 : Route 9 := (fun mask => (mask,id))

def c12238 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12238 : Upper (D 6) (R 6) [10,33,80,129,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,80,129,288,4] 13 (by decide) (choices 1) [2,4] r12238 c12238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2307
  · exact u2308

def r12239 : Route 9 := (fun mask => (mask,id))

def c12239 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12239 : Upper (D 6) (R 6) [10,33,80,129,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,80,129,288,64] 13 (by decide) (choices 1) [2,4] r12239 c12239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2309
  · exact u2310

#print axioms u12239
end Delivery.IrregularNine14.P06
