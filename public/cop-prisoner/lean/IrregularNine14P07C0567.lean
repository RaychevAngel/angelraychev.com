import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0304
import IrregularNine14P07C0305
import IrregularNine14P07C0306
import IrregularNine14P07C0307

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34020 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 152 276 233 201 201 457), lower := (rows 35 67 38 152 276 32 64 128 256), losses := [] }

theorem u34020 : Upper (D 7) (R 7) [34,65,34,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34021 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 152 280 229 197 197 453), lower := (rows 35 67 38 152 280 32 64 128 256), losses := [] }

theorem u34021 : Upper (D 7) (R 7) [34,65,34,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34022 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 152 336 173 205 141 397), lower := (rows 35 67 38 152 336 32 64 128 256), losses := [] }

theorem u34022 : Upper (D 7) (R 7) [34,65,34,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34023 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 200 273 188 220 156 412), lower := (rows 35 67 38 200 273 32 64 128 256), losses := [] }

theorem u34023 : Upper (D 7) (R 7) [34,65,34,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34024 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 200 276 185 217 153 409), lower := (rows 35 67 38 200 276 32 64 128 256), losses := [] }

theorem u34024 : Upper (D 7) (R 7) [34,65,34,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34025 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 200 280 181 213 149 405), lower := (rows 35 67 38 200 280 32 64 128 256), losses := [] }

theorem u34025 : Upper (D 7) (R 7) [34,65,34,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34026 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 38 200 400 61 93 157 285), lower := (rows 35 67 38 200 400 32 64 128 256), losses := [] }

theorem u34026 : Upper (D 7) (R 7) [34,65,34,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34027 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 67 44 76 145 434 466 402 402), lower := (rows 35 67 44 76 145 32 64 128 256), losses := [] }

theorem u34027 : Upper (D 7) (R 7) [34,65,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34028 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 67 44 76 273 178 210 146 402), lower := (rows 35 67 44 76 273 32 64 128 256), losses := [] }

theorem u34028 : Upper (D 7) (R 7) [34,65,40,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34029 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 67 44 76 400 179 211 147 403), lower := (rows 35 67 44 76 400 32 64 128 256), losses := [] }

theorem u34029 : Upper (D 7) (R 7) [34,65,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34030 : Route 9 := (fun mask => (mask,id))

def c34030 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34030 : Upper (D 7) (R 7) [34,65,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,129] 13 (by decide) (choices 1) [2,4,128,256] r34030 c34030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18270
  · exact u18271
  · exact u18272
  · exact u18273

def r34031 : Route 9 := (fun mask => (mask,id))

def c34031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34031 : Upper (D 7) (R 7) [34,65,40,80,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,130] 13 (by decide) (choices 1) [1,4,128,256] r34031 c34031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18274
  · exact u18275
  · exact u18276
  · exact u18277

def r34032 : Route 9 := (fun mask => (mask,id))

def c34032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34032 : Upper (D 7) (R 7) [34,65,40,80,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,132] 13 (by decide) (choices 1) [1,2,128,256] r34032 c34032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18278
  · exact u18279
  · exact u18280
  · exact u18281

def r34033 : Route 9 := (fun mask => (mask,id))

def c34033 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34033 : Upper (D 7) (R 7) [34,65,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,257] 13 (by decide) (choices 1) [2,4,128] r34033 c34033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18282
  · exact u18283
  · exact u18284

def r34034 : Route 9 := (fun mask => (mask,id))

def c34034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34034 : Upper (D 7) (R 7) [34,65,40,80,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,258] 13 (by decide) (choices 1) [1,4,128] r34034 c34034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18285
  · exact u18286
  · exact u18287

def r34035 : Route 9 := (fun mask => (mask,id))

def c34035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34035 : Upper (D 7) (R 7) [34,65,40,80,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,260] 13 (by decide) (choices 1) [1,2,128] r34035 c34035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18288
  · exact u18289
  · exact u18290

def r34036 : Route 9 := (fun mask => (mask,id))

def c34036 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34036 : Upper (D 7) (R 7) [34,65,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,384] 13 (by decide) (choices 1) [1,2,4,128] r34036 c34036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18291
  · exact u18292
  · exact u18293
  · exact u18294

def r34037 : Route 9 := (fun mask => (mask,id))

def c34037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34037 : Upper (D 7) (R 7) [34,65,40,129,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,130] 13 (by decide) (choices 1) [4,16,64,256] r34037 c34037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18295
  · exact u18296
  · exact u18297
  · exact u18298

def r34038 : Route 9 := (fun mask => (mask,id))

def c34038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34038 : Upper (D 7) (R 7) [34,65,40,129,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,132] 13 (by decide) (choices 1) [2,16,64,256] r34038 c34038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18299
  · exact u18300
  · exact u18301
  · exact u18302

def r34039 : Route 9 := (fun mask => (mask,id))

def c34039 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34039 : Upper (D 7) (R 7) [34,65,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,192] 13 (by decide) (choices 1) [2,4,16,256] r34039 c34039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18303
  · exact u18304
  · exact u18305
  · exact u18306

def r34040 : Route 9 := (fun mask => (mask,id))

def c34040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34040 : Upper (D 7) (R 7) [34,65,40,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,258] 13 (by decide) (choices 1) [4,16,64,128] r34040 c34040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18307
  · exact u18308
  · exact u18309
  · exact u18310

def r34041 : Route 9 := (fun mask => (mask,id))

def c34041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34041 : Upper (D 7) (R 7) [34,65,40,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,260] 13 (by decide) (choices 1) [2,16,64,128] r34041 c34041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18311
  · exact u18312
  · exact u18313
  · exact u18314

def r34042 : Route 9 := (fun mask => (mask,id))

def c34042 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34042 : Upper (D 7) (R 7) [34,65,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,320] 13 (by decide) (choices 1) [2,4,16,128] r34042 c34042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18315
  · exact u18316
  · exact u18317
  · exact u18318

def r34043 : Route 9 := (fun mask => (mask,id))

def c34043 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34043 : Upper (D 7) (R 7) [34,65,40,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,384] 13 (by decide) (choices 1) [2,4,16,64] r34043 c34043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18319
  · exact u18320
  · exact u18321
  · exact u18322

def r34044 : Route 9 := (fun mask => (mask,id))

def c34044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34044 : Upper (D 7) (R 7) [34,65,40,130,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,129] 13 (by decide) (choices 1) [4,16,64,256] r34044 c34044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18323
  · exact u18324
  · exact u18325
  · exact u18326

def r34045 : Route 9 := (fun mask => (mask,id))

def c34045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34045 : Upper (D 7) (R 7) [34,65,40,130,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,132] 13 (by decide) (choices 1) [1,16,64,256] r34045 c34045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18327
  · exact u18328
  · exact u18329
  · exact u18330

def r34046 : Route 9 := (fun mask => (mask,id))

def c34046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34046 : Upper (D 7) (R 7) [34,65,40,130,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,192] 13 (by decide) (choices 1) [1,4,16,256] r34046 c34046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18331
  · exact u18332
  · exact u18333
  · exact u18334

def r34047 : Route 9 := (fun mask => (mask,id))

def c34047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34047 : Upper (D 7) (R 7) [34,65,40,130,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,257] 13 (by decide) (choices 1) [4,16,64,128] r34047 c34047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18335
  · exact u18336
  · exact u18337
  · exact u18338

def r34048 : Route 9 := (fun mask => (mask,id))

def c34048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34048 : Upper (D 7) (R 7) [34,65,40,130,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,260] 13 (by decide) (choices 1) [1,16,64,128] r34048 c34048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18339
  · exact u18340
  · exact u18341
  · exact u18342

def r34049 : Route 9 := (fun mask => (mask,id))

def c34049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34049 : Upper (D 7) (R 7) [34,65,40,130,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,320] 13 (by decide) (choices 1) [1,4,16,128] r34049 c34049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18343
  · exact u18344
  · exact u18345
  · exact u18346

def r34050 : Route 9 := (fun mask => (mask,id))

def c34050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34050 : Upper (D 7) (R 7) [34,65,40,130,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,384] 13 (by decide) (choices 1) [1,4,16,64] r34050 c34050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18347
  · exact u18348
  · exact u18349
  · exact u18350

def b34051 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 67 44 140 145 370 338 466 338), lower := (rows 35 67 44 140 145 32 64 128 256), losses := [] }

theorem u34051 : Upper (D 7) (R 7) [34,65,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34052 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 67 44 140 146 369 337 465 337), lower := (rows 35 67 44 140 146 32 64 128 256), losses := [] }

theorem u34052 : Upper (D 7) (R 7) [34,65,40,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34053 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 67 44 140 208 307 339 403 275), lower := (rows 35 67 44 140 208 32 64 128 256), losses := [] }

theorem u34053 : Upper (D 7) (R 7) [34,65,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34054 : Route 9 := (fun mask => (mask,id))

def c34054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34054 : Upper (D 7) (R 7) [34,65,40,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,257] 13 (by decide) (choices 1) [2,16,64,128] r34054 c34054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18351
  · exact u18352
  · exact u18353
  · exact u18354

def r34055 : Route 9 := (fun mask => (mask,id))

def c34055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34055 : Upper (D 7) (R 7) [34,65,40,132,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,258] 13 (by decide) (choices 1) [1,16,64,128] r34055 c34055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18355
  · exact u18356
  · exact u18357
  · exact u18358

def r34056 : Route 9 := (fun mask => (mask,id))

def c34056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34056 : Upper (D 7) (R 7) [34,65,40,132,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,320] 13 (by decide) (choices 1) [1,2,16,128] r34056 c34056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18359
  · exact u18360
  · exact u18361
  · exact u18362

def b34057 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 67 44 140 400 115 83 211 339), lower := (rows 35 67 44 140 400 32 64 128 256), losses := [] }

theorem u34057 : Upper (D 7) (R 7) [34,65,40,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34058 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 44 152 145 358 326 454 326), lower := (rows 35 67 44 152 145 32 64 128 256), losses := [] }

theorem u34058 : Upper (D 7) (R 7) [34,65,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34059 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 44 152 146 357 325 453 325), lower := (rows 35 67 44 152 146 32 64 128 256), losses := [] }

theorem u34059 : Upper (D 7) (R 7) [34,65,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34060 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 44 152 148 355 323 451 323), lower := (rows 35 67 44 152 148 32 64 128 256), losses := [] }

theorem u34060 : Upper (D 7) (R 7) [34,65,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34061 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 44 152 208 295 327 391 263), lower := (rows 35 67 44 152 208 32 64 128 256), losses := [] }

theorem u34061 : Upper (D 7) (R 7) [34,65,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34062 : Route 9 := (fun mask => (mask,id))

def c34062 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34062 : Upper (D 7) (R 7) [34,65,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,257] 13 (by decide) (choices 1) [2,4,64,128] r34062 c34062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18363
  · exact u18364
  · exact u18365
  · exact u18366

def r34063 : Route 9 := (fun mask => (mask,id))

def c34063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34063 : Upper (D 7) (R 7) [34,65,40,144,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,258] 13 (by decide) (choices 1) [1,4,64,128] r34063 c34063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18367
  · exact u18368
  · exact u18369
  · exact u18370

def r34064 : Route 9 := (fun mask => (mask,id))

def c34064 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34064 : Upper (D 7) (R 7) [34,65,40,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,260] 13 (by decide) (choices 1) [1,2,64,128] r34064 c34064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18371
  · exact u18372
  · exact u18373
  · exact u18374

def r34065 : Route 9 := (fun mask => (mask,id))

def c34065 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34065 : Upper (D 7) (R 7) [34,65,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,320] 13 (by decide) (choices 1) [1,2,4,128] r34065 c34065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18375
  · exact u18376
  · exact u18377
  · exact u18378

def b34066 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 67 44 152 400 103 71 199 327), lower := (rows 35 67 44 152 400 32 64 128 256), losses := [] }

theorem u34066 : Upper (D 7) (R 7) [34,65,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34067 : Route 9 := (fun mask => (mask,id))

def c34067 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34067 : Upper (D 7) (R 7) [34,65,40,192,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,129] 13 (by decide) (choices 1) [2,4,16,256] r34067 c34067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18379
  · exact u18380
  · exact u18381
  · exact u18382

def r34068 : Route 9 := (fun mask => (mask,id))

def c34068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34068 : Upper (D 7) (R 7) [34,65,40,192,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,130] 13 (by decide) (choices 1) [1,4,16,256] r34068 c34068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18383
  · exact u18384
  · exact u18385
  · exact u18386

def r34069 : Route 9 := (fun mask => (mask,id))

def c34069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34069 : Upper (D 7) (R 7) [34,65,40,192,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,132] 13 (by decide) (choices 1) [1,2,16,256] r34069 c34069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18387
  · exact u18388
  · exact u18389
  · exact u18390

def r34070 : Route 9 := (fun mask => (mask,id))

def c34070 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34070 : Upper (D 7) (R 7) [34,65,40,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,257] 13 (by decide) (choices 1) [2,4,16,128] r34070 c34070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18391
  · exact u18392
  · exact u18393
  · exact u18394

def r34071 : Route 9 := (fun mask => (mask,id))

def c34071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34071 : Upper (D 7) (R 7) [34,65,40,192,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,258] 13 (by decide) (choices 1) [1,4,16,128] r34071 c34071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18395
  · exact u18396
  · exact u18397
  · exact u18398

def r34072 : Route 9 := (fun mask => (mask,id))

def c34072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34072 : Upper (D 7) (R 7) [34,65,40,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260] 13 (by decide) (choices 1) [1,2,16,128] r34072 c34072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18399
  · exact u18400
  · exact u18401
  · exact u18402

def r34073 : Route 9 := (fun mask => (mask,id))

def c34073 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34073 : Upper (D 7) (R 7) [34,65,40,192,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,384] 13 (by decide) (choices 1) [1,2,4,16] r34073 c34073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18403
  · exact u18404
  · exact u18405
  · exact u18406

def r34074 : Route 9 := (fun mask => (mask,id))

def c34074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34074 : Upper (D 7) (R 7) [34,65,40,257,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,130] 13 (by decide) (choices 1) [4,16,64,128] r34074 c34074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18407
  · exact u18408
  · exact u18409
  · exact u18410

def r34075 : Route 9 := (fun mask => (mask,id))

def c34075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34075 : Upper (D 7) (R 7) [34,65,40,257,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,132] 13 (by decide) (choices 1) [2,16,64,128] r34075 c34075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18411
  · exact u18412
  · exact u18413
  · exact u18414

def r34076 : Route 9 := (fun mask => (mask,id))

def c34076 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34076 : Upper (D 7) (R 7) [34,65,40,257,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,192] 13 (by decide) (choices 1) [2,4,16,128] r34076 c34076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18415
  · exact u18416
  · exact u18417
  · exact u18418

def r34077 : Route 9 := (fun mask => (mask,id))

def c34077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34077 : Upper (D 7) (R 7) [34,65,40,258,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,258,129] 13 (by decide) (choices 1) [4,16,64,128] r34077 c34077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18419
  · exact u18420
  · exact u18421
  · exact u18422

def r34078 : Route 9 := (fun mask => (mask,id))

def c34078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34078 : Upper (D 7) (R 7) [34,65,40,258,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,258,132] 13 (by decide) (choices 1) [1,16,64,128] r34078 c34078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18423
  · exact u18424
  · exact u18425
  · exact u18426

def r34079 : Route 9 := (fun mask => (mask,id))

def c34079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34079 : Upper (D 7) (R 7) [34,65,40,258,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,258,192] 13 (by decide) (choices 1) [1,4,16,128] r34079 c34079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18427
  · exact u18428
  · exact u18429
  · exact u18430

#print axioms u34079
end Delivery.IrregularNine14.P07
