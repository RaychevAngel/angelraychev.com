import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0017
import IrregularNine14P08C0018

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7320 : Route 9 := (fun mask => (mask,id))

def c7320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7320 : Upper (D 8) (R 8) [6,33,72,384,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,96] 13 (by decide) (choices 1) [1,16,128] r7320 c7320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1051
  · exact u1052
  · exact u1053

def b7321 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 392 145 112 112 240 368), lower := (rows 7 35 76 392 145 32 64 128 256), losses := [] }

theorem u7321 : Upper (D 8) (R 8) [6,33,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7322 : Route 9 := (fun mask => (mask,id))

def c7322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7322 : Upper (D 8) (R 8) [6,33,72,384,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,160] 13 (by decide) (choices 1) [1,16,64] r7322 c7322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1054
  · exact u1055
  · exact u1056

def r7323 : Route 9 := (fun mask => (mask,id))

def c7323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7323 : Upper (D 8) (R 8) [6,33,72,384,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,192] 13 (by decide) (choices 1) [1,16] r7323 c7323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1057
  · exact u1058

def b7324 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 25 56 480 480 480 480), lower := (rows 7 35 196 25 56 32 64 128 256), losses := [] }

theorem u7324 : Upper (D 8) (R 8) [6,33,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7325 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 25 88 416 480 416 416), lower := (rows 7 35 196 25 88 32 64 128 256), losses := [] }

theorem u7325 : Upper (D 8) (R 8) [6,33,192,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7326 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 25 112 424 488 424 424), lower := (rows 7 35 196 25 112 32 64 128 256), losses := [] }

theorem u7326 : Upper (D 8) (R 8) [6,33,192,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7327 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 25 280 224 224 224 480), lower := (rows 7 35 196 25 280 32 64 128 256), losses := [] }

theorem u7327 : Upper (D 8) (R 8) [6,33,192,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7328 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 25 304 232 232 232 488), lower := (rows 7 35 196 25 304 32 64 128 256), losses := [] }

theorem u7328 : Upper (D 8) (R 8) [6,33,192,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7329 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 25 336 168 232 168 424), lower := (rows 7 35 196 25 336 32 64 128 256), losses := [] }

theorem u7329 : Upper (D 8) (R 8) [6,33,192,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7330 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 56 496 464 464 464), lower := (rows 7 35 196 41 56 32 64 128 256), losses := [] }

theorem u7330 : Upper (D 8) (R 8) [6,33,192,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7331 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 88 432 496 432 432), lower := (rows 7 35 196 41 88 32 64 128 256), losses := [] }

theorem u7331 : Upper (D 8) (R 8) [6,33,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7332 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 112 440 472 408 408), lower := (rows 7 35 196 41 112 32 64 128 256), losses := [] }

theorem u7332 : Upper (D 8) (R 8) [6,33,192,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7333 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 280 240 240 240 496), lower := (rows 7 35 196 41 280 32 64 128 256), losses := [] }

theorem u7333 : Upper (D 8) (R 8) [6,33,192,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7334 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 304 248 216 216 472), lower := (rows 7 35 196 41 304 32 64 128 256), losses := [] }

theorem u7334 : Upper (D 8) (R 8) [6,33,192,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7335 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 336 184 248 184 440), lower := (rows 7 35 196 41 336 32 64 128 256), losses := [] }

theorem u7335 : Upper (D 8) (R 8) [6,33,192,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7336 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 56 56 481 449 449 449), lower := (rows 7 35 196 56 56 32 64 128 256), losses := [] }

theorem u7336 : Upper (D 8) (R 8) [6,33,192,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7337 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 56 81 424 488 424 424), lower := (rows 7 35 196 56 81 32 64 128 256), losses := [] }

theorem u7337 : Upper (D 8) (R 8) [6,33,192,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7338 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 56 88 417 481 417 417), lower := (rows 7 35 196 56 88 32 64 128 256), losses := [] }

theorem u7338 : Upper (D 8) (R 8) [6,33,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7339 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 56 112 425 457 393 393), lower := (rows 7 35 196 56 112 32 64 128 256), losses := [] }

theorem u7339 : Upper (D 8) (R 8) [6,33,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7340 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 196 56 208 297 361 425 297), lower := (rows 7 35 196 56 208 32 64 128 256), losses := [] }

theorem u7340 : Upper (D 8) (R 8) [6,33,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7341 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 56 273 232 232 232 488), lower := (rows 7 35 196 56 273 32 64 128 256), losses := [] }

theorem u7341 : Upper (D 8) (R 8) [6,33,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7342 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7342 : Upper (D 8) (R 8) [6,33,192,48,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,264] 13 (by decide) (choices 1) [1,64] r7342 c7342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1059
  · exact u1060

def b7343 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 56 304 233 201 201 457), lower := (rows 7 35 196 56 304 32 64 128 256), losses := [] }

theorem u7343 : Upper (D 8) (R 8) [6,33,192,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7344 : Route 9 := (fun mask => (mask,id))

def c7344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7344 : Upper (D 8) (R 8) [6,33,192,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,320] 13 (by decide) (choices 1) [1,8,128] r7344 c7344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1061
  · exact u1062
  · exact u1063

def b7345 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 73 152 304 368 432 304), lower := (rows 7 35 196 73 152 32 64 128 256), losses := [] }

theorem u7345 : Upper (D 8) (R 8) [6,33,192,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7346 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 73 176 312 376 440 312), lower := (rows 7 35 196 73 176 32 64 128 256), losses := [] }

theorem u7346 : Upper (D 8) (R 8) [6,33,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7347 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 73 280 176 240 176 432), lower := (rows 7 35 196 73 280 32 64 128 256), losses := [] }

theorem u7347 : Upper (D 8) (R 8) [6,33,192,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7348 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 73 304 184 248 184 440), lower := (rows 7 35 196 73 304 32 64 128 256), losses := [] }

theorem u7348 : Upper (D 8) (R 8) [6,33,192,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7349 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 73 400 56 120 184 312), lower := (rows 7 35 196 73 400 32 64 128 256), losses := [] }

theorem u7349 : Upper (D 8) (R 8) [6,33,192,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7350 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 88 152 289 353 417 289), lower := (rows 7 35 196 88 152 32 64 128 256), losses := [] }

theorem u7350 : Upper (D 8) (R 8) [6,33,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7351 : Route 9 := (fun mask => (mask,id))

def c7351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7351 : Upper (D 8) (R 8) [6,33,192,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,160] 13 (by decide) (choices 1) [1,8,256] r7351 c7351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1064
  · exact u1065
  · exact u1066

def b7352 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 88 273 168 232 168 424), lower := (rows 7 35 196 88 273 32 64 128 256), losses := [] }

theorem u7352 : Upper (D 8) (R 8) [6,33,192,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7353 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 88 280 161 225 161 417), lower := (rows 7 35 196 88 280 32 64 128 256), losses := [] }

theorem u7353 : Upper (D 8) (R 8) [6,33,192,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7354 : Route 9 := (fun mask => (mask,id))

def c7354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7354 : Upper (D 8) (R 8) [6,33,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,288] 13 (by decide) (choices 1) [1,8,128] r7354 c7354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1067
  · exact u1068
  · exact u1069

def r7355 : Route 9 := (fun mask => (mask,id))

def c7355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7355 : Upper (D 8) (R 8) [6,33,192,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384] 13 (by decide) (choices 1) [1,8] r7355 c7355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1070
  · exact u1071

theorem m7356_16 : Upper (D 8) (R 8) [6,33,192,96,160,16] 13 :=
  permutation_upper _ _ _ [6,33,192,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1073

def r7356 : Route 9 := (fun mask => (mask,id))

def c7356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7356 : Upper (D 8) (R 8) [6,33,192,96,160] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,160] 13 (by decide) (choices 1) [1,8,16,256] r7356 c7356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1072
  · exact u1073
  · exact m7356_16
  · exact u1074

def b7357 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 104 273 184 248 184 440), lower := (rows 7 35 196 104 273 32 64 128 256), losses := [] }

theorem u7357 : Upper (D 8) (R 8) [6,33,192,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7358 : Route 9 := (fun mask => (mask,id))

def c7358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7358 : Upper (D 8) (R 8) [6,33,192,96,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264] 13 (by decide) (choices 1) [1,16,128] r7358 c7358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1075
  · exact u1076
  · exact u1077

def r7359 : Route 9 := (fun mask => (mask,id))

def c7359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7359 : Upper (D 8) (R 8) [6,33,192,96,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,288] 13 (by decide) (choices 1) [1,8,16,128] r7359 c7359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1078
  · exact u1079
  · exact u1080
  · exact u1081

def r7360 : Route 9 := (fun mask => (mask,id))

def c7360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7360 : Upper (D 8) (R 8) [6,33,192,96,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,384] 13 (by decide) (choices 1) [1,8,16] r7360 c7360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1082
  · exact u1083
  · exact u1084

def b7361 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 200 280 49 113 177 305), lower := (rows 7 35 196 200 280 32 64 128 256), losses := [] }

theorem u7361 : Upper (D 8) (R 8) [6,33,192,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7362 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 200 304 57 121 185 313), lower := (rows 7 35 196 200 304 32 64 128 256), losses := [] }

theorem u7362 : Upper (D 8) (R 8) [6,33,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7363 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 268 56 49 224 192 192 448), lower := (rows 7 35 268 56 49 32 64 128 256), losses := [] }

theorem u7363 : Upper (D 8) (R 8) [6,33,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7364 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 268 56 81 224 224 224 480), lower := (rows 7 35 268 56 81 32 64 128 256), losses := [] }

theorem u7364 : Upper (D 8) (R 8) [6,33,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7365 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 268 56 112 225 193 193 449), lower := (rows 7 35 268 56 112 32 64 128 256), losses := [] }

theorem u7365 : Upper (D 8) (R 8) [6,33,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7366 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7366 : Upper (D 8) (R 8) [6,33,264,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,48,192] 13 (by decide) (choices 1) [1,64] r7366 c7366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1085
  · exact u1086

def b7367 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 88 49 224 224 224 480), lower := (rows 7 35 268 88 49 32 64 128 256), losses := [] }

theorem u7367 : Upper (D 8) (R 8) [6,33,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7368 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 81 160 224 160 416), lower := (rows 7 35 268 88 81 32 64 128 256), losses := [] }

theorem u7368 : Upper (D 8) (R 8) [6,33,264,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7369 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 112 161 225 161 417), lower := (rows 7 35 268 88 112 32 64 128 256), losses := [] }

theorem u7369 : Upper (D 8) (R 8) [6,33,264,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7370 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 268 88 145 224 224 224 480), lower := (rows 7 35 268 88 145 32 64 128 256), losses := [] }

theorem u7370 : Upper (D 8) (R 8) [6,33,264,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7371 : Route 9 := (fun mask => (mask,id))

def c7371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7371 : Upper (D 8) (R 8) [6,33,264,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80,160] 13 (by decide) (choices 1) [1,64,128] r7371 c7371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1087
  · exact u1088
  · exact u1089

def b7372 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 208 161 225 161 417), lower := (rows 7 35 268 88 208 32 64 128 256), losses := [] }

theorem u7372 : Upper (D 8) (R 8) [6,33,264,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7373 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 104 49 240 208 208 464), lower := (rows 7 35 268 104 49 32 64 128 256), losses := [] }

theorem u7373 : Upper (D 8) (R 8) [6,33,264,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7374 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 268 104 81 176 240 176 432), lower := (rows 7 35 268 104 81 32 64 128 256), losses := [] }

theorem u7374 : Upper (D 8) (R 8) [6,33,264,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7375 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 268 104 112 177 209 145 401), lower := (rows 7 35 268 104 112 32 64 128 256), losses := [] }

theorem u7375 : Upper (D 8) (R 8) [6,33,264,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7376 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 268 104 145 240 240 240 496), lower := (rows 7 35 268 104 145 32 64 128 256), losses := [] }

theorem u7376 : Upper (D 8) (R 8) [6,33,264,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7377 : Route 9 := (fun mask => (mask,id))

def c7377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7377 : Upper (D 8) (R 8) [6,33,264,96,160] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,160] 13 (by decide) (choices 1) [1,16,64,128] r7377 c7377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1090
  · exact u1091
  · exact u1092
  · exact u1093

def r7378 : Route 9 := (fun mask => (mask,id))

def c7378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7378 : Upper (D 8) (R 8) [6,33,264,96,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,192] 13 (by decide) (choices 1) [1,16,128] r7378 c7378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1094
  · exact u1095
  · exact u1096

def b7379 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 200 49 240 240 240 496), lower := (rows 7 35 268 200 49 32 64 128 256), losses := [] }

theorem u7379 : Upper (D 8) (R 8) [6,33,264,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7379
end Delivery.IrregularNine14.P08
