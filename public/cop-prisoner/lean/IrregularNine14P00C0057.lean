import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0038
import IrregularNine14P00C0039
import IrregularNine14P00C0040

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3420 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 489 497 481 481 481 481), lower := (rows 15 50 84 8 16 32 64 128 256), losses := [] }

theorem u3420 : Upper (D 0) (R 0) [14,48,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3420
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3421_17 : Upper (D 0) (R 0) [14,48,192,17] 13 :=
  permutation_upper _ _ _ [14,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2290

theorem m3421_48 : Upper (D 0) (R 0) [14,48,192,48] 13 :=
  permutation_upper _ _ _ [14,48,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2300

theorem m3421_65 : Upper (D 0) (R 0) [14,48,192,65] 13 :=
  permutation_upper _ _ _ [14,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2290

theorem m3421_80 : Upper (D 0) (R 0) [14,48,192,80] 13 :=
  permutation_upper _ _ _ [14,48,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2303

theorem m3421_192 : Upper (D 0) (R 0) [14,48,192,192] 13 :=
  permutation_upper _ _ _ [14,48,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2300

theorem m3421_320 : Upper (D 0) (R 0) [14,48,192,320] 13 :=
  permutation_upper _ _ _ [14,48,192,272] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2308

def r3421 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3421 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3421 : Upper (D 0) (R 0) [14,48,192] 13 := by
  apply FastRouting.sound _ _ [14,48,192] 13 (by decide) (choices 2) [17,48,65,80,192,257,272,320] r3421 c3421
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3421_17
  · exact m3421_48
  · exact m3421_65
  · exact m3421_80
  · exact m3421_192
  · exact u2307
  · exact u2308
  · exact m3421_320

theorem m3422_17 : Upper (D 0) (R 0) [14,48,257,17] 13 :=
  permutation_upper _ _ _ [14,17,48,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2291

theorem m3422_48 : Upper (D 0) (R 0) [14,48,257,48] 13 :=
  permutation_upper _ _ _ [14,48,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2301

theorem m3422_65 : Upper (D 0) (R 0) [14,48,257,65] 13 :=
  permutation_upper _ _ _ [14,17,96,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2296

theorem m3422_80 : Upper (D 0) (R 0) [14,48,257,80] 13 :=
  permutation_upper _ _ _ [14,48,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2304

theorem m3422_192 : Upper (D 0) (R 0) [14,48,257,192] 13 :=
  permutation_upper _ _ _ [14,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2307

def r3422 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3422 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3422 : Upper (D 0) (R 0) [14,48,257] 13 := by
  apply FastRouting.sound _ _ [14,48,257] 13 (by decide) (choices 2) [17,48,65,80,192] r3422 c3422
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m3422_17
  · exact m3422_48
  · exact m3422_65
  · exact m3422_80
  · exact m3422_192

def b3423 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 276 233 241 225 225 225 481), lower := (rows 15 50 276 8 16 32 64 128 256), losses := [] }

theorem u3423 : Upper (D 0) (R 0) [14,48,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3423
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3424_17 : Upper (D 0) (R 0) [14,48,320,17] 13 :=
  permutation_upper _ _ _ [14,17,48,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2293

theorem m3424_48 : Upper (D 0) (R 0) [14,48,320,48] 13 :=
  permutation_upper _ _ _ [14,48,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2302

theorem m3424_65 : Upper (D 0) (R 0) [14,48,320,65] 13 :=
  permutation_upper _ _ _ [14,17,96,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2297

theorem m3424_80 : Upper (D 0) (R 0) [14,48,320,80] 13 :=
  permutation_upper _ _ _ [14,48,80,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2305

theorem m3424_129 : Upper (D 0) (R 0) [14,48,320,129] 13 :=
  permutation_upper _ _ _ [14,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 7 | 5 => 4 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 4 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2299

theorem m3424_144 : Upper (D 0) (R 0) [14,48,320,144] 13 :=
  permutation_upper _ _ _ [14,48,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2306

theorem m3424_192 : Upper (D 0) (R 0) [14,48,320,192] 13 :=
  permutation_upper _ _ _ [14,48,192,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2308

def r3424 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c3424 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3424 : Upper (D 0) (R 0) [14,48,320] 13 := by
  apply FastRouting.sound _ _ [14,48,320] 13 (by decide) (choices 2) [17,48,65,80,129,144,192] r3424 c3424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3424_17
  · exact m3424_48
  · exact m3424_65
  · exact m3424_80
  · exact m3424_129
  · exact m3424_144
  · exact m3424_192

def b3425 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 23 11 21 488 496 480 480 480 480), lower := (rows 23 11 21 8 16 32 64 128 256), losses := [] }

theorem u3425 : Upper (D 0) (R 0) [22,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3425
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3426 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 23 11 37 504 496 496 496 496 496), lower := (rows 23 11 37 8 16 32 64 128 256), losses := [] }

theorem u3426 : Upper (D 0) (R 0) [22,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3426
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3427 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 52 489 497 481 481 481 481), lower := (rows 23 11 52 8 16 32 64 128 256), losses := [] }

theorem u3427 : Upper (D 0) (R 0) [22,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3427
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3428 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3428 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3428 : Upper (D 0) (R 0) [22,9,96] 13 := by
  apply FastRouting.sound _ _ [22,9,96] 13 (by decide) (choices 2) [17,33,48,96,129,144,160,257,272,288,384] r3428 c3428
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2309
  · exact u2310
  · exact u2311
  · exact u2312
  · exact u2313
  · exact u2314
  · exact u2315
  · exact u2316
  · exact u2317
  · exact u2318
  · exact u2319

def b3429 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 23 11 261 248 240 240 240 240 496), lower := (rows 23 11 261 8 16 32 64 128 256), losses := [] }

theorem u3429 : Upper (D 0) (R 0) [22,9,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3429
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3430 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 276 233 241 225 225 225 481), lower := (rows 23 11 276 8 16 32 64 128 256), losses := [] }

theorem u3430 : Upper (D 0) (R 0) [22,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3430
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3431 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3431 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3431 : Upper (D 0) (R 0) [22,9,288] 13 := by
  apply FastRouting.sound _ _ [22,9,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3431 c3431
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2320
  · exact u2321
  · exact u2322
  · exact u2323
  · exact u2324
  · exact u2325
  · exact u2326

def b3432 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 23 19 37 488 504 488 488 488 488), lower := (rows 23 19 37 8 16 32 64 128 256), losses := [] }

theorem u3432 : Upper (D 0) (R 0) [22,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3432
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3433 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 23 19 44 489 497 481 481 481 481), lower := (rows 23 19 44 8 16 32 64 128 256), losses := [] }

theorem u3433 : Upper (D 0) (R 0) [22,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3433
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3434 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 23 19 100 489 505 489 489 489 489), lower := (rows 23 19 100 8 16 32 64 128 256), losses := [] }

theorem u3434 : Upper (D 0) (R 0) [22,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3434
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3435 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 23 19 261 232 248 232 232 232 488), lower := (rows 23 19 261 8 16 32 64 128 256), losses := [] }

theorem u3435 : Upper (D 0) (R 0) [22,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3435
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3436 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 23 19 268 233 241 225 225 225 481), lower := (rows 23 19 268 8 16 32 64 128 256), losses := [] }

theorem u3436 : Upper (D 0) (R 0) [22,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3436
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3437 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 23 19 292 233 249 233 233 233 489), lower := (rows 23 19 292 8 16 32 64 128 256), losses := [] }

theorem u3437 : Upper (D 0) (R 0) [22,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3437
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3438 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 26 37 489 497 481 481 481 481), lower := (rows 23 26 37 8 16 32 64 128 256), losses := [] }

theorem u3438 : Upper (D 0) (R 0) [22,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3438
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3439 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 26 100 489 497 481 481 481 481), lower := (rows 23 26 100 8 16 32 64 128 256), losses := [] }

theorem u3439 : Upper (D 0) (R 0) [22,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3439
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3440 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 26 261 233 241 225 225 225 481), lower := (rows 23 26 261 8 16 32 64 128 256), losses := [] }

theorem u3440 : Upper (D 0) (R 0) [22,24,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3440
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3441 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 26 292 233 241 225 225 225 481), lower := (rows 23 26 292 8 16 32 64 128 256), losses := [] }

theorem u3441 : Upper (D 0) (R 0) [22,24,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3441
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3442 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 35 37 472 472 504 472 472 472), lower := (rows 23 35 37 8 16 32 64 128 256), losses := [] }

theorem u3442 : Upper (D 0) (R 0) [22,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3442
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3443 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 44 473 465 497 465 465 465), lower := (rows 23 35 44 8 16 32 64 128 256), losses := [] }

theorem u3443 : Upper (D 0) (R 0) [22,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3443
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3444 : PairBound 9 := { available := 457, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 23 35 52 457 473 489 457 457 457), lower := (rows 23 35 52 8 16 32 64 128 256), losses := [] }

theorem u3444 : Upper (D 0) (R 0) [22,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3444
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3445 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 23 35 69 504 504 504 504 504 504), lower := (rows 23 35 69 8 16 32 64 128 256), losses := [] }

theorem u3445 : Upper (D 0) (R 0) [22,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3445
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3446 : Route 9 := (fun mask => (mask,id))

def c3446 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3446 : Upper (D 0) (R 0) [22,33,72] 13 := by
  apply FastRouting.sound _ _ [22,33,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r3446 c3446
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2327
  · exact u2328
  · exact u2329
  · exact u2330
  · exact u2331
  · exact u2332
  · exact u2333
  · exact u2334
  · exact u2335
  · exact u2336
  · exact u2337
  · exact u2338
  · exact u2339
  · exact u2340
  · exact u2341

def b3447 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 84 489 505 489 489 489 489), lower := (rows 23 35 84 8 16 32 64 128 256), losses := [] }

theorem u3447 : Upper (D 0) (R 0) [22,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3447
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3448 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 100 473 473 505 473 473 473), lower := (rows 23 35 100 8 16 32 64 128 256), losses := [] }

theorem u3448 : Upper (D 0) (R 0) [22,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3448
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3449 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3449 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3449 : Upper (D 0) (R 0) [22,33,192] 13 := by
  apply FastRouting.sound _ _ [22,33,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r3449 c3449
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2342
  · exact u2343
  · exact u2344
  · exact u2345
  · exact u2346
  · exact u2347
  · exact u2348
  · exact u2349
  · exact u2350
  · exact u2351
  · exact u2352

def b3450 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 23 35 261 248 248 248 248 248 504), lower := (rows 23 35 261 8 16 32 64 128 256), losses := [] }

theorem u3450 : Upper (D 0) (R 0) [22,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3450
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3451 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3451 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3451 : Upper (D 0) (R 0) [22,33,264] 13 := by
  apply FastRouting.sound _ _ [22,33,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3451 c3451
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2353
  · exact u2354
  · exact u2355
  · exact u2356
  · exact u2357
  · exact u2358
  · exact u2359

def b3452 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 276 233 249 233 233 233 489), lower := (rows 23 35 276 8 16 32 64 128 256), losses := [] }

theorem u3452 : Upper (D 0) (R 0) [22,33,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3452
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3453 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 292 217 217 249 217 217 473), lower := (rows 23 35 292 8 16 32 64 128 256), losses := [] }

theorem u3453 : Upper (D 0) (R 0) [22,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3453
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3454 : Route 9 := (fun mask => (mask,id))

def c3454 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3454 : Upper (D 0) (R 0) [22,33,320] 13 := by
  apply FastRouting.sound _ _ [22,33,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r3454 c3454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2360
  · exact u2361
  · exact u2362
  · exact u2363
  · exact u2364
  · exact u2365
  · exact u2366
  · exact u2367
  · exact u2368
  · exact u2369

def b3455 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 52 457 465 481 449 449 449), lower := (rows 23 42 52 8 16 32 64 128 256), losses := [] }

theorem u3455 : Upper (D 0) (R 0) [22,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3455
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3456 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 84 489 497 481 481 481 481), lower := (rows 23 42 84 8 16 32 64 128 256), losses := [] }

theorem u3456 : Upper (D 0) (R 0) [22,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3456
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3457 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 100 473 465 497 465 465 465), lower := (rows 23 42 100 8 16 32 64 128 256), losses := [] }

theorem u3457 : Upper (D 0) (R 0) [22,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3457
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3458 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3458 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3458 : Upper (D 0) (R 0) [22,40,192] 13 := by
  apply FastRouting.sound _ _ [22,40,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r3458 c3458
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2370
  · exact u2371
  · exact u2372
  · exact u2373
  · exact u2374
  · exact u2375
  · exact u2376
  · exact u2377
  · exact u2378
  · exact u2379
  · exact u2380

def r3459 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3459 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3459 : Upper (D 0) (R 0) [22,40,257] 13 := by
  apply FastRouting.sound _ _ [22,40,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3459 c3459
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2381
  · exact u2382
  · exact u2383
  · exact u2384
  · exact u2385
  · exact u2386
  · exact u2387

def b3460 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 276 233 241 225 225 225 481), lower := (rows 23 42 276 8 16 32 64 128 256), losses := [] }

theorem u3460 : Upper (D 0) (R 0) [22,40,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3460
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3461 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 292 217 209 241 209 209 465), lower := (rows 23 42 292 8 16 32 64 128 256), losses := [] }

theorem u3461 : Upper (D 0) (R 0) [22,40,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3461
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3462 : Route 9 := (fun mask => (mask,id))

def c3462 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3462 : Upper (D 0) (R 0) [22,40,320] 13 := by
  apply FastRouting.sound _ _ [22,40,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r3462 c3462
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2388
  · exact u2389
  · exact u2390
  · exact u2391
  · exact u2392
  · exact u2393
  · exact u2394
  · exact u2395
  · exact u2396
  · exact u2397

def b3463 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 23 50 100 457 473 489 457 457 457), lower := (rows 23 50 100 8 16 32 64 128 256), losses := [] }

theorem u3463 : Upper (D 0) (R 0) [22,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3463
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3464 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 23 50 196 489 505 489 489 489 489), lower := (rows 23 50 196 8 16 32 64 128 256), losses := [] }

theorem u3464 : Upper (D 0) (R 0) [22,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3464
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3465 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 23 50 261 233 249 233 233 233 489), lower := (rows 23 50 261 8 16 32 64 128 256), losses := [] }

theorem u3465 : Upper (D 0) (R 0) [22,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3465
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3466 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 23 50 268 233 241 225 225 225 481), lower := (rows 23 50 268 8 16 32 64 128 256), losses := [] }

theorem u3466 : Upper (D 0) (R 0) [22,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3466
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3467 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 23 50 292 201 217 233 201 201 457), lower := (rows 23 50 292 8 16 32 64 128 256), losses := [] }

theorem u3467 : Upper (D 0) (R 0) [22,48,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3467
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3468 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 23 50 324 233 249 233 233 233 489), lower := (rows 23 50 324 8 16 32 64 128 256), losses := [] }

theorem u3468 : Upper (D 0) (R 0) [22,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3468
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3469 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 23 98 100 409 409 441 473 409 409), lower := (rows 23 98 100 8 16 32 64 128 256), losses := [] }

theorem u3469 : Upper (D 0) (R 0) [22,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3469
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3470 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 164 473 473 505 473 473 473), lower := (rows 23 98 164 8 16 32 64 128 256), losses := [] }

theorem u3470 : Upper (D 0) (R 0) [22,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3470
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3471 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3471 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3471 : Upper (D 0) (R 0) [22,96,257] 13 := by
  apply FastRouting.sound _ _ [22,96,257] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r3471 c3471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2398
  · exact u2399
  · exact u2400
  · exact u2401
  · exact u2402
  · exact u2403
  · exact u2404

def r3472 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3472 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3472 : Upper (D 0) (R 0) [22,96,264] 13 := by
  apply FastRouting.sound _ _ [22,96,264] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r3472 c3472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2405
  · exact u2406
  · exact u2407
  · exact u2408
  · exact u2409
  · exact u2410
  · exact u2411

def b3473 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 276 233 249 233 233 233 489), lower := (rows 23 98 276 8 16 32 64 128 256), losses := [] }

theorem u3473 : Upper (D 0) (R 0) [22,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3473
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3474 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 292 217 217 249 217 217 473), lower := (rows 23 98 292 8 16 32 64 128 256), losses := [] }

theorem u3474 : Upper (D 0) (R 0) [22,96,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3474
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3475 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3475 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3475 : Upper (D 0) (R 0) [22,96,384] 13 := by
  apply FastRouting.sound _ _ [22,96,384] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r3475 c3475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2412
  · exact u2413
  · exact u2414
  · exact u2415
  · exact u2416
  · exact u2417
  · exact u2418

def b3476 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 51 7 13 504 496 496 496 496 496), lower := (rows 51 7 13 8 16 32 64 128 256), losses := [] }

theorem u3476 : Upper (D 0) (R 0) [50,5,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3476
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3477 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 21 488 504 488 488 488 488), lower := (rows 51 7 21 8 16 32 64 128 256), losses := [] }

theorem u3477 : Upper (D 0) (R 0) [50,5,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3477
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3478 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 7 28 489 497 481 481 481 481), lower := (rows 51 7 28 8 16 32 64 128 256), losses := [] }

theorem u3478 : Upper (D 0) (R 0) [50,5,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3478
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3479 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 51 7 52 457 473 489 457 457 457), lower := (rows 51 7 52 8 16 32 64 128 256), losses := [] }

theorem u3479 : Upper (D 0) (R 0) [50,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3479
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u3479
end Delivery.IrregularNine14.P00
