import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0047
import IrregularNine14P08C0048

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10260 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 14 133 296 145 112 112 240 368), lower := (rows 67 14 133 296 145 32 64 128 256), losses := [] }

theorem u10260 : Upper (D 8) (R 8) [66,12,129,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10261 : Route 9 := (fun mask => (mask,id))

def c10261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10261 : Upper (D 8) (R 8) [66,12,129,288,160] 13 := by
  apply FastRouting.sound _ _ [66,12,129,288,160] 13 (by decide) (choices 1) [1,16,64] r10261 c10261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2857
  · exact u2858
  · exact u2859

def r10262 : Route 9 := (fun mask => (mask,id))

def c10262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10262 : Upper (D 8) (R 8) [66,12,129,288,192] 13 := by
  apply FastRouting.sound _ _ [66,12,129,288,192] 13 (by decide) (choices 1) [1,16] r10262 c10262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2860
  · exact u2861

def b10263 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 148 265 49 224 224 224 480), lower := (rows 67 14 148 265 49 32 64 128 256), losses := [] }

theorem u10263 : Upper (D 8) (R 8) [66,12,144,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10264 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 148 265 81 160 224 160 416), lower := (rows 67 14 148 265 81 32 64 128 256), losses := [] }

theorem u10264 : Upper (D 8) (R 8) [66,12,144,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10265 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 148 265 112 161 225 161 417), lower := (rows 67 14 148 265 112 32 64 128 256), losses := [] }

theorem u10265 : Upper (D 8) (R 8) [66,12,144,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10266 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 148 265 145 96 96 224 352), lower := (rows 67 14 148 265 145 32 64 128 256), losses := [] }

theorem u10266 : Upper (D 8) (R 8) [66,12,144,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10267 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 148 265 176 97 97 225 353), lower := (rows 67 14 148 265 176 32 64 128 256), losses := [] }

theorem u10267 : Upper (D 8) (R 8) [66,12,144,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10268 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 148 265 208 33 97 161 289), lower := (rows 67 14 148 265 208 32 64 128 256), losses := [] }

theorem u10268 : Upper (D 8) (R 8) [66,12,144,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10269 : Route 9 := (fun mask => (mask,id))

def c10269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10269 : Upper (D 8) (R 8) [66,12,144,288,33] 13 := by
  apply FastRouting.sound _ _ [66,12,144,288,33] 13 (by decide) (choices 1) [1,64,128] r10269 c10269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2862
  · exact u2863
  · exact u2864

def b10270 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 148 296 81 161 225 161 417), lower := (rows 67 14 148 296 81 32 64 128 256), losses := [] }

theorem u10270 : Upper (D 8) (R 8) [66,12,144,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10271 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 148 296 112 161 225 161 417), lower := (rows 67 14 148 296 112 32 64 128 256), losses := [] }

theorem u10271 : Upper (D 8) (R 8) [66,12,144,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10272 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 148 296 145 97 97 225 353), lower := (rows 67 14 148 296 145 32 64 128 256), losses := [] }

theorem u10272 : Upper (D 8) (R 8) [66,12,144,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10273 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 148 296 176 97 97 225 353), lower := (rows 67 14 148 296 176 32 64 128 256), losses := [] }

theorem u10273 : Upper (D 8) (R 8) [66,12,144,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10274 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 148 296 208 33 97 161 289), lower := (rows 67 14 148 296 208 32 64 128 256), losses := [] }

theorem u10274 : Upper (D 8) (R 8) [66,12,144,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10275 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 164 265 49 240 240 240 496), lower := (rows 67 14 164 265 49 32 64 128 256), losses := [] }

theorem u10275 : Upper (D 8) (R 8) [66,12,160,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10276 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 164 265 81 176 240 176 432), lower := (rows 67 14 164 265 81 32 64 128 256), losses := [] }

theorem u10276 : Upper (D 8) (R 8) [66,12,160,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10277 : Route 9 := (fun mask => (mask,id))

def c10277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10277 : Upper (D 8) (R 8) [66,12,160,257,96] 13 := by
  apply FastRouting.sound _ _ [66,12,160,257,96] 13 (by decide) (choices 1) [1,16,128] r10277 c10277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2865
  · exact u2866
  · exact u2867

def b10278 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 164 265 145 112 112 240 368), lower := (rows 67 14 164 265 145 32 64 128 256), losses := [] }

theorem u10278 : Upper (D 8) (R 8) [66,12,160,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10279 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 164 265 176 113 113 241 369), lower := (rows 67 14 164 265 176 32 64 128 256), losses := [] }

theorem u10279 : Upper (D 8) (R 8) [66,12,160,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10280 : Route 9 := (fun mask => (mask,id))

def c10280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10280 : Upper (D 8) (R 8) [66,12,160,257,192] 13 := by
  apply FastRouting.sound _ _ [66,12,160,257,192] 13 (by decide) (choices 1) [1,16] r10280 c10280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2868
  · exact u2869

def r10281 : Route 9 := (fun mask => (mask,id))

def c10281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10281 : Upper (D 8) (R 8) [66,12,160,272,33] 13 := by
  apply FastRouting.sound _ _ [66,12,160,272,33] 13 (by decide) (choices 1) [1,64,128] r10281 c10281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2870
  · exact u2871
  · exact u2872

def b10282 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 164 280 81 161 225 161 417), lower := (rows 67 14 164 280 81 32 64 128 256), losses := [] }

theorem u10282 : Upper (D 8) (R 8) [66,12,160,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10283 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 164 280 112 161 225 161 417), lower := (rows 67 14 164 280 112 32 64 128 256), losses := [] }

theorem u10283 : Upper (D 8) (R 8) [66,12,160,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10284 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 164 280 145 97 97 225 353), lower := (rows 67 14 164 280 145 32 64 128 256), losses := [] }

theorem u10284 : Upper (D 8) (R 8) [66,12,160,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10285 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 164 280 176 97 97 225 353), lower := (rows 67 14 164 280 176 32 64 128 256), losses := [] }

theorem u10285 : Upper (D 8) (R 8) [66,12,160,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10286 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 164 280 208 33 97 161 289), lower := (rows 67 14 164 280 208 32 64 128 256), losses := [] }

theorem u10286 : Upper (D 8) (R 8) [66,12,160,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10287 : Route 9 := (fun mask => (mask,id))

def c10287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10287 : Upper (D 8) (R 8) [66,12,160,288,33] 13 := by
  apply FastRouting.sound _ _ [66,12,160,288,33] 13 (by decide) (choices 1) [1,16,64,128] r10287 c10287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2873
  · exact u2874
  · exact u2875
  · exact u2876

def b10288 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 164 296 81 177 241 177 433), lower := (rows 67 14 164 296 81 32 64 128 256), losses := [] }

theorem u10288 : Upper (D 8) (R 8) [66,12,160,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10289 : Route 9 := (fun mask => (mask,id))

def c10289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10289 : Upper (D 8) (R 8) [66,12,160,288,96] 13 := by
  apply FastRouting.sound _ _ [66,12,160,288,96] 13 (by decide) (choices 1) [1,16,128] r10289 c10289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2877
  · exact u2878
  · exact u2879

def b10290 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 67 14 164 296 145 113 113 241 369), lower := (rows 67 14 164 296 145 32 64 128 256), losses := [] }

theorem u10290 : Upper (D 8) (R 8) [66,12,160,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10291 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 164 296 176 113 81 209 337), lower := (rows 67 14 164 296 176 32 64 128 256), losses := [] }

theorem u10291 : Upper (D 8) (R 8) [66,12,160,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10292 : Route 9 := (fun mask => (mask,id))

def c10292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10292 : Upper (D 8) (R 8) [66,12,160,288,192] 13 := by
  apply FastRouting.sound _ _ [66,12,160,288,192] 13 (by decide) (choices 1) [1,16] r10292 c10292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2880
  · exact u2881

def b10293 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 28 176 480 480 480 480), lower := (rows 67 35 13 28 176 32 64 128 256), losses := [] }

theorem u10293 : Upper (D 8) (R 8) [66,33,9,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10294 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 28 208 416 480 416 416), lower := (rows 67 35 13 28 208 32 64 128 256), losses := [] }

theorem u10294 : Upper (D 8) (R 8) [66,33,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10295 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 28 304 224 224 224 480), lower := (rows 67 35 13 28 304 32 64 128 256), losses := [] }

theorem u10295 : Upper (D 8) (R 8) [66,33,9,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10296 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 28 336 160 224 160 416), lower := (rows 67 35 13 28 336 32 64 128 256), losses := [] }

theorem u10296 : Upper (D 8) (R 8) [66,33,9,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10297 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 28 400 224 224 224 480), lower := (rows 67 35 13 28 400 32 64 128 256), losses := [] }

theorem u10297 : Upper (D 8) (R 8) [66,33,9,20,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10298 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 13 44 176 496 464 464 464), lower := (rows 67 35 13 44 176 32 64 128 256), losses := [] }

theorem u10298 : Upper (D 8) (R 8) [66,33,9,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10299 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 13 44 208 432 496 432 432), lower := (rows 67 35 13 44 208 32 64 128 256), losses := [] }

theorem u10299 : Upper (D 8) (R 8) [66,33,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10300 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 13 44 304 240 208 208 464), lower := (rows 67 35 13 44 304 32 64 128 256), losses := [] }

theorem u10300 : Upper (D 8) (R 8) [66,33,9,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10301 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 13 44 336 176 240 176 432), lower := (rows 67 35 13 44 336 32 64 128 256), losses := [] }

theorem u10301 : Upper (D 8) (R 8) [66,33,9,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10302 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 13 44 400 240 240 240 496), lower := (rows 67 35 13 44 400 32 64 128 256), losses := [] }

theorem u10302 : Upper (D 8) (R 8) [66,33,9,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10303 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 56 84 416 480 416 416), lower := (rows 67 35 13 56 84 32 64 128 256), losses := [] }

theorem u10303 : Upper (D 8) (R 8) [66,33,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10304 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 56 148 480 480 480 480), lower := (rows 67 35 13 56 148 32 64 128 256), losses := [] }

theorem u10304 : Upper (D 8) (R 8) [66,33,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10305 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 56 208 420 484 420 420), lower := (rows 67 35 13 56 208 32 64 128 256), losses := [] }

theorem u10305 : Upper (D 8) (R 8) [66,33,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10306 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 56 276 224 224 224 480), lower := (rows 67 35 13 56 276 32 64 128 256), losses := [] }

theorem u10306 : Upper (D 8) (R 8) [66,33,9,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10307 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 56 336 164 228 164 420), lower := (rows 67 35 13 56 336 32 64 128 256), losses := [] }

theorem u10307 : Upper (D 8) (R 8) [66,33,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10308 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 56 400 228 228 228 484), lower := (rows 67 35 13 56 400 32 64 128 256), losses := [] }

theorem u10308 : Upper (D 8) (R 8) [66,33,9,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10309 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 35 13 76 176 432 496 432 432), lower := (rows 67 35 13 76 176 32 64 128 256), losses := [] }

theorem u10309 : Upper (D 8) (R 8) [66,33,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10310 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 35 13 76 304 176 240 176 432), lower := (rows 67 35 13 76 304 32 64 128 256), losses := [] }

theorem u10310 : Upper (D 8) (R 8) [66,33,9,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10311 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 35 13 76 400 176 240 176 432), lower := (rows 67 35 13 76 400 32 64 128 256), losses := [] }

theorem u10311 : Upper (D 8) (R 8) [66,33,9,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10312 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 88 52 416 480 416 416), lower := (rows 67 35 13 88 52 32 64 128 256), losses := [] }

theorem u10312 : Upper (D 8) (R 8) [66,33,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10313 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 88 148 416 480 416 416), lower := (rows 67 35 13 88 148 32 64 128 256), losses := [] }

theorem u10313 : Upper (D 8) (R 8) [66,33,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10314 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 88 176 420 484 420 420), lower := (rows 67 35 13 88 176 32 64 128 256), losses := [] }

theorem u10314 : Upper (D 8) (R 8) [66,33,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10315 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 88 276 160 224 160 416), lower := (rows 67 35 13 88 276 32 64 128 256), losses := [] }

theorem u10315 : Upper (D 8) (R 8) [66,33,9,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10316 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 88 304 164 228 164 420), lower := (rows 67 35 13 88 304 32 64 128 256), losses := [] }

theorem u10316 : Upper (D 8) (R 8) [66,33,9,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10317 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 88 400 164 228 164 420), lower := (rows 67 35 13 88 400 32 64 128 256), losses := [] }

theorem u10317 : Upper (D 8) (R 8) [66,33,9,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10318 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 140 176 368 368 496 368), lower := (rows 67 35 13 140 176 32 64 128 256), losses := [] }

theorem u10318 : Upper (D 8) (R 8) [66,33,9,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10319 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 140 208 304 368 432 304), lower := (rows 67 35 13 140 208 32 64 128 256), losses := [] }

theorem u10319 : Upper (D 8) (R 8) [66,33,9,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10319
end Delivery.IrregularNine14.P08
