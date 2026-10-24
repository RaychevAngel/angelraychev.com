import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0037
import IrregularNine14P08C0038

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9180 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 152 176 97 97 225 353), lower := (rows 35 70 268 152 176 32 64 128 256), losses := [] }

theorem u9180 : Upper (D 8) (R 8) [34,68,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9181 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 152 208 33 97 161 289), lower := (rows 35 70 268 152 208 32 64 128 256), losses := [] }

theorem u9181 : Upper (D 8) (R 8) [34,68,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9182 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 268 168 49 241 209 209 465), lower := (rows 35 70 268 168 49 32 64 128 256), losses := [] }

theorem u9182 : Upper (D 8) (R 8) [34,68,264,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9183 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 168 81 177 241 177 433), lower := (rows 35 70 268 168 81 32 64 128 256), losses := [] }

theorem u9183 : Upper (D 8) (R 8) [34,68,264,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9184 : Route 9 := (fun mask => (mask,id))

def c9184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9184 : Upper (D 8) (R 8) [34,68,264,160,96] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160,96] 13 (by decide) (choices 1) [1,16,128] r9184 c9184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2274
  · exact u2275
  · exact u2276

def r9185 : Route 9 := (fun mask => (mask,id))

def c9185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9185 : Upper (D 8) (R 8) [34,68,264,160,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160,129] 13 (by decide) (choices 1) [1,16,64] r9185 c9185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2277
  · exact u2278
  · exact u2279

def b9186 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 268 168 176 113 81 209 337), lower := (rows 35 70 268 168 176 32 64 128 256), losses := [] }

theorem u9186 : Upper (D 8) (R 8) [34,68,264,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9187 : Route 9 := (fun mask => (mask,id))

def c9187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9187 : Upper (D 8) (R 8) [34,68,264,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160,192] 13 (by decide) (choices 1) [1,16] r9187 c9187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2280
  · exact u2281

def b9188 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 292 25 25 224 224 224 480), lower := (rows 35 70 292 25 25 32 64 128 256), losses := [] }

theorem u9188 : Upper (D 8) (R 8) [34,68,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9189 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 292 25 49 232 200 200 456), lower := (rows 35 70 292 25 49 32 64 128 256), losses := [] }

theorem u9189 : Upper (D 8) (R 8) [34,68,288,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9190 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 292 25 56 225 193 193 449), lower := (rows 35 70 292 25 56 32 64 128 256), losses := [] }

theorem u9190 : Upper (D 8) (R 8) [34,68,288,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9191 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 292 25 81 168 232 168 424), lower := (rows 35 70 292 25 81 32 64 128 256), losses := [] }

theorem u9191 : Upper (D 8) (R 8) [34,68,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9192 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 25 88 161 225 161 417), lower := (rows 35 70 292 25 88 32 64 128 256), losses := [] }

theorem u9192 : Upper (D 8) (R 8) [34,68,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9193 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 25 112 169 201 137 393), lower := (rows 35 70 292 25 112 32 64 128 256), losses := [] }

theorem u9193 : Upper (D 8) (R 8) [34,68,288,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9194 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 292 25 145 232 232 232 488), lower := (rows 35 70 292 25 145 32 64 128 256), losses := [] }

theorem u9194 : Upper (D 8) (R 8) [34,68,288,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9195 : Route 9 := (fun mask => (mask,id))

def c9195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9195 : Upper (D 8) (R 8) [34,68,288,17,136] 13 := by
  apply FastRouting.sound _ _ [34,68,288,17,136] 13 (by decide) (choices 1) [1,64,128] r9195 c9195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2282
  · exact u2283
  · exact u2284

def r9196 : Route 9 := (fun mask => (mask,id))

def c9196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9196 : Upper (D 8) (R 8) [34,68,288,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,288,17,160] 13 (by decide) (choices 1) [1,8,64,128] r9196 c9196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2285
  · exact u2286
  · exact u2287
  · exact u2288

def b9197 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 25 208 169 233 169 425), lower := (rows 35 70 292 25 208 32 64 128 256), losses := [] }

theorem u9197 : Upper (D 8) (R 8) [34,68,288,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9198 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 292 41 88 177 209 145 401), lower := (rows 35 70 292 41 88 32 64 128 256), losses := [] }

theorem u9198 : Upper (D 8) (R 8) [34,68,288,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9199 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 292 41 145 248 216 216 472), lower := (rows 35 70 292 41 145 32 64 128 256), losses := [] }

theorem u9199 : Upper (D 8) (R 8) [34,68,288,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9200 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 292 41 152 241 209 209 465), lower := (rows 35 70 292 41 152 32 64 128 256), losses := [] }

theorem u9200 : Upper (D 8) (R 8) [34,68,288,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9201 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 292 41 208 185 217 153 409), lower := (rows 35 70 292 41 208 32 64 128 256), losses := [] }

theorem u9201 : Upper (D 8) (R 8) [34,68,288,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9202 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 56 81 169 201 137 393), lower := (rows 35 70 292 56 81 32 64 128 256), losses := [] }

theorem u9202 : Upper (D 8) (R 8) [34,68,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9203 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 56 88 161 193 129 385), lower := (rows 35 70 292 56 88 32 64 128 256), losses := [] }

theorem u9203 : Upper (D 8) (R 8) [34,68,288,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9204 : Route 9 := (fun mask => (mask,id))

def c9204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9204 : Upper (D 8) (R 8) [34,68,288,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,288,48,129] 13 (by decide) (choices 1) [1,8,64,128] r9204 c9204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2289
  · exact u2290
  · exact u2291
  · exact u2292

def r9205 : Route 9 := (fun mask => (mask,id))

def c9205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9205 : Upper (D 8) (R 8) [34,68,288,48,136] 13 := by
  apply FastRouting.sound _ _ [34,68,288,48,136] 13 (by decide) (choices 1) [1,64,128] r9205 c9205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2293
  · exact u2294
  · exact u2295

def r9206 : Route 9 := (fun mask => (mask,id))

def c9206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9206 : Upper (D 8) (R 8) [34,68,288,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,288,48,192] 13 (by decide) (choices 1) [1,8,128] r9206 c9206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2296
  · exact u2297
  · exact u2298

def b9207 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 73 145 184 248 184 440), lower := (rows 35 70 292 73 145 32 64 128 256), losses := [] }

theorem u9207 : Upper (D 8) (R 8) [34,68,288,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9208 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 73 152 177 241 177 433), lower := (rows 35 70 292 73 152 32 64 128 256), losses := [] }

theorem u9208 : Upper (D 8) (R 8) [34,68,288,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9209 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 73 176 185 217 153 409), lower := (rows 35 70 292 73 176 32 64 128 256), losses := [] }

theorem u9209 : Upper (D 8) (R 8) [34,68,288,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9210 : Route 9 := (fun mask => (mask,id))

def c9210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9210 : Upper (D 8) (R 8) [34,68,288,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,288,80,129] 13 (by decide) (choices 1) [1,8,128] r9210 c9210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2299
  · exact u2300
  · exact u2301

def b9211 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 88 152 161 225 161 417), lower := (rows 35 70 292 88 152 32 64 128 256), losses := [] }

theorem u9211 : Upper (D 8) (R 8) [34,68,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9212 : Route 9 := (fun mask => (mask,id))

def c9212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9212 : Upper (D 8) (R 8) [34,68,288,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,288,80,160] 13 (by decide) (choices 1) [1,8,128] r9212 c9212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2302
  · exact u2303
  · exact u2304

def r9213 : Route 9 := (fun mask => (mask,id))

def c9213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9213 : Upper (D 8) (R 8) [34,68,288,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,288,96,129] 13 (by decide) (choices 1) [1,8,16,128] r9213 c9213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2305
  · exact u2306
  · exact u2307
  · exact u2308

def r9214 : Route 9 := (fun mask => (mask,id))

def c9214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9214 : Upper (D 8) (R 8) [34,68,288,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,288,96,136] 13 (by decide) (choices 1) [1,16,128] r9214 c9214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2309
  · exact u2310
  · exact u2311

def b9215 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 292 137 145 120 120 248 376), lower := (rows 35 70 292 137 145 32 64 128 256), losses := [] }

theorem u9215 : Upper (D 8) (R 8) [34,68,288,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9216 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 292 137 152 113 113 241 369), lower := (rows 35 70 292 137 152 32 64 128 256), losses := [] }

theorem u9216 : Upper (D 8) (R 8) [34,68,288,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9217 : Route 9 := (fun mask => (mask,id))

def c9217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9217 : Upper (D 8) (R 8) [34,68,288,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,288,129,160] 13 (by decide) (choices 1) [1,8,16,64] r9217 c9217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2312
  · exact u2313
  · exact u2314
  · exact u2315

def r9218 : Route 9 := (fun mask => (mask,id))

def c9218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9218 : Upper (D 8) (R 8) [34,68,288,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,288,129,192] 13 (by decide) (choices 1) [1,8,16] r9218 c9218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2316
  · exact u2317
  · exact u2318

def b9219 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 292 152 152 97 97 225 353), lower := (rows 35 70 292 152 152 32 64 128 256), losses := [] }

theorem u9219 : Upper (D 8) (R 8) [34,68,288,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9220 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 152 176 105 73 201 329), lower := (rows 35 70 292 152 176 32 64 128 256), losses := [] }

theorem u9220 : Upper (D 8) (R 8) [34,68,288,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9221 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 152 208 41 105 169 297), lower := (rows 35 70 292 152 208 32 64 128 256), losses := [] }

theorem u9221 : Upper (D 8) (R 8) [34,68,288,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9222 : Route 9 := (fun mask => (mask,id))

def c9222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9222 : Upper (D 8) (R 8) [34,68,288,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,288,160,192] 13 (by decide) (choices 1) [1,8,16] r9222 c9222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2319
  · exact u2320
  · exact u2321

def b9223 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 388 25 25 224 224 224 480), lower := (rows 35 70 388 25 25 32 64 128 256), losses := [] }

theorem u9223 : Upper (D 8) (R 8) [34,68,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9224 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 25 49 232 232 232 488), lower := (rows 35 70 388 25 49 32 64 128 256), losses := [] }

theorem u9224 : Upper (D 8) (R 8) [34,68,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9225 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 25 56 225 225 225 481), lower := (rows 35 70 388 25 56 32 64 128 256), losses := [] }

theorem u9225 : Upper (D 8) (R 8) [34,68,384,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9226 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 388 25 81 168 232 168 424), lower := (rows 35 70 388 25 81 32 64 128 256), losses := [] }

theorem u9226 : Upper (D 8) (R 8) [34,68,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9227 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 25 88 161 225 161 417), lower := (rows 35 70 388 25 88 32 64 128 256), losses := [] }

theorem u9227 : Upper (D 8) (R 8) [34,68,384,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9228 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 25 112 169 233 169 425), lower := (rows 35 70 388 25 112 32 64 128 256), losses := [] }

theorem u9228 : Upper (D 8) (R 8) [34,68,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9229 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 388 25 145 104 104 232 360), lower := (rows 35 70 388 25 145 32 64 128 256), losses := [] }

theorem u9229 : Upper (D 8) (R 8) [34,68,384,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9230 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 25 152 97 97 225 353), lower := (rows 35 70 388 25 152 32 64 128 256), losses := [] }

theorem u9230 : Upper (D 8) (R 8) [34,68,384,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9231 : Route 9 := (fun mask => (mask,id))

def c9231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9231 : Upper (D 8) (R 8) [34,68,384,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,160] 13 (by decide) (choices 1) [1,8,64] r9231 c9231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2322
  · exact u2323
  · exact u2324

def b9232 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 25 208 41 105 169 297), lower := (rows 35 70 388 25 208 32 64 128 256), losses := [] }

theorem u9232 : Upper (D 8) (R 8) [34,68,384,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9233 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 41 56 241 209 209 465), lower := (rows 35 70 388 41 56 32 64 128 256), losses := [] }

theorem u9233 : Upper (D 8) (R 8) [34,68,384,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9234 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 41 88 177 241 177 433), lower := (rows 35 70 388 41 88 32 64 128 256), losses := [] }

theorem u9234 : Upper (D 8) (R 8) [34,68,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9235 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 41 112 185 217 153 409), lower := (rows 35 70 388 41 112 32 64 128 256), losses := [] }

theorem u9235 : Upper (D 8) (R 8) [34,68,384,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9236 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 41 152 113 113 241 369), lower := (rows 35 70 388 41 152 32 64 128 256), losses := [] }

theorem u9236 : Upper (D 8) (R 8) [34,68,384,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9237 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 41 176 121 89 217 345), lower := (rows 35 70 388 41 176 32 64 128 256), losses := [] }

theorem u9237 : Upper (D 8) (R 8) [34,68,384,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9238 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 41 208 57 121 185 313), lower := (rows 35 70 388 41 208 32 64 128 256), losses := [] }

theorem u9238 : Upper (D 8) (R 8) [34,68,384,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9239 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 388 56 56 225 193 193 449), lower := (rows 35 70 388 56 56 32 64 128 256), losses := [] }

theorem u9239 : Upper (D 8) (R 8) [34,68,384,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9239
end Delivery.IrregularNine14.P08
