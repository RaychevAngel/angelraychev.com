import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0038
import IrregularNine14P03C0039
import IrregularNine14P03C0040
import IrregularNine14P03C0041

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5820 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 292 56 209 225 193 193 449), lower := (rows 7 11 292 56 16 32 64 128 256), losses := [] }

theorem u5820 : Upper (D 3) (R 3) [6,9,288,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5820
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5821 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 73 241 241 241 241 497), lower := (rows 7 11 292 73 16 32 64 128 256), losses := [] }

theorem u5821 : Upper (D 3) (R 3) [6,9,288,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5821
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5822 : Route 9 := (fun mask => (mask,id))

def c5822 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5822 : Upper (D 3) (R 3) [6,9,288,80] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5822 c5822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2284
  · exact u2285
  · exact u2286
  · exact u2287
  · exact u2288
  · exact u2289

def b5823 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 11 292 104 209 241 209 209 465), lower := (rows 7 11 292 104 16 32 64 128 256), losses := [] }

theorem u5823 : Upper (D 3) (R 3) [6,9,288,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5823
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5824 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5824 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5824 : Upper (D 3) (R 3) [6,9,288,192] 13 := by
  apply FastRouting.sound _ _ [6,9,288,192] 13 (by decide) (choices 2) [33,65,96,192] r5824 c5824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2290
  · exact u2291
  · exact u2292
  · exact u2293

def b5825 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 37 41 465 481 449 449 449), lower := (rows 7 26 37 41 16 32 64 128 256), losses := [] }

theorem u5825 : Upper (D 3) (R 3) [6,24,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5825
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5826_33 : Upper (D 3) (R 3) [6,24,33,65,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2294

def r5826 : Route 9 := (fun mask => (mask,id))

def c5826 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5826 : Upper (D 3) (R 3) [6,24,33,65] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5826 c5826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5826_33
  · exact u2298
  · exact u2299
  · exact u2300
  · exact u2301
  · exact u2302
  · exact u2303
  · exact u2304
  · exact u2305
  · exact u2306

def b5827 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 26 37 104 465 481 449 449 449), lower := (rows 7 26 37 104 16 32 64 128 256), losses := [] }

theorem u5827 : Upper (D 3) (R 3) [6,24,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5827
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5828_33 : Upper (D 3) (R 3) [6,24,33,192,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2295

theorem m5828_65 : Upper (D 3) (R 3) [6,24,33,192,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2302

theorem m5828_96 : Upper (D 3) (R 3) [6,24,33,192,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2307

def r5828 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5828 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5828 : Upper (D 3) (R 3) [6,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r5828 c5828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5828_33
  · exact m5828_65
  · exact m5828_96
  · exact u2311
  · exact u2312
  · exact u2313
  · exact u2314

theorem m5829_33 : Upper (D 3) (R 3) [6,24,33,257,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2296

theorem m5829_65 : Upper (D 3) (R 3) [6,24,33,257,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2303

theorem m5829_96 : Upper (D 3) (R 3) [6,24,33,257,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2308

theorem m5829_192 : Upper (D 3) (R 3) [6,24,33,257,192] 13 :=
  permutation_upper _ _ _ [6,24,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2312

def r5829 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5829 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5829 : Upper (D 3) (R 3) [6,24,33,257] 13 := by
  apply FastRouting.sound _ _ [6,24,33,257] 13 (by decide) (choices 2) [33,65,96,192] r5829 c5829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5829_33
  · exact m5829_65
  · exact m5829_96
  · exact m5829_192

def b5830 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 26 37 296 209 225 193 193 449), lower := (rows 7 26 37 296 16 32 64 128 256), losses := [] }

theorem u5830 : Upper (D 3) (R 3) [6,24,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5830
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5831_33 : Upper (D 3) (R 3) [6,24,33,320,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2297

theorem m5831_65 : Upper (D 3) (R 3) [6,24,33,320,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2305

theorem m5831_96 : Upper (D 3) (R 3) [6,24,33,320,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2309

theorem m5831_129 : Upper (D 3) (R 3) [6,24,33,320,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2306

theorem m5831_160 : Upper (D 3) (R 3) [6,24,33,320,160] 13 :=
  permutation_upper _ _ _ [6,24,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2310

theorem m5831_192 : Upper (D 3) (R 3) [6,24,33,320,192] 13 :=
  permutation_upper _ _ _ [6,24,33,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2314

def r5831 : Route 9 := (fun mask => (mask,id))

def c5831 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5831 : Upper (D 3) (R 3) [6,24,33,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5831 c5831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5831_33
  · exact m5831_65
  · exact m5831_96
  · exact m5831_129
  · exact m5831_160
  · exact m5831_192

def b5832 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 100 41 465 481 449 449 449), lower := (rows 7 26 100 41 16 32 64 128 256), losses := [] }

theorem u5832 : Upper (D 3) (R 3) [6,24,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5832
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5833 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 401 417 449 385 385), lower := (rows 7 26 100 104 16 32 64 128 256), losses := [] }

theorem u5833 : Upper (D 3) (R 3) [6,24,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5833
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5834_33 : Upper (D 3) (R 3) [6,24,96,129,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2315

theorem m5834_96 : Upper (D 3) (R 3) [6,24,96,129,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2318

def r5834 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5834 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5834 : Upper (D 3) (R 3) [6,24,96,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r5834 c5834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5834_33
  · exact m5834_96
  · exact u2321
  · exact u2322
  · exact u2323
  · exact u2324
  · exact u2325

def b5835 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 26 100 168 465 481 449 449 449), lower := (rows 7 26 100 168 16 32 64 128 256), losses := [] }

theorem u5835 : Upper (D 3) (R 3) [6,24,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5835
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5836_33 : Upper (D 3) (R 3) [6,24,96,257,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2316

theorem m5836_96 : Upper (D 3) (R 3) [6,24,96,257,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2319

theorem m5836_129 : Upper (D 3) (R 3) [6,24,96,257,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2323

theorem m5836_160 : Upper (D 3) (R 3) [6,24,96,257,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2326

def r5836 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5836 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5836 : Upper (D 3) (R 3) [6,24,96,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,257] 13 (by decide) (choices 2) [33,96,129,160] r5836 c5836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5836_33
  · exact m5836_96
  · exact m5836_129
  · exact m5836_160

def b5837 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 26 100 296 209 225 193 193 449), lower := (rows 7 26 100 296 16 32 64 128 256), losses := [] }

theorem u5837 : Upper (D 3) (R 3) [6,24,96,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5837
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5838_33 : Upper (D 3) (R 3) [6,24,96,384,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2317

theorem m5838_96 : Upper (D 3) (R 3) [6,24,96,384,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2320

theorem m5838_129 : Upper (D 3) (R 3) [6,24,96,384,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2325

theorem m5838_160 : Upper (D 3) (R 3) [6,24,96,384,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2327

def r5838 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5838 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5838 : Upper (D 3) (R 3) [6,24,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,384] 13 (by decide) (choices 2) [33,96,129,160] r5838 c5838
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5838_33
  · exact m5838_96
  · exact m5838_129
  · exact m5838_160

def r5839 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5839 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5839 : Upper (D 3) (R 3) [6,24,257,33] 13 := by
  apply FastRouting.sound _ _ [6,24,257,33] 13 (by decide) (choices 2) [33,65,96,192] r5839 c5839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2328
  · exact u2329
  · exact u2330
  · exact u2331

theorem m5840_33 : Upper (D 3) (R 3) [6,24,257,96,33] 13 :=
  permutation_upper _ _ _ [6,24,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2330

theorem m5840_129 : Upper (D 3) (R 3) [6,24,257,96,129] 13 :=
  permutation_upper _ _ _ [6,24,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2331

def r5840 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5840 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5840 : Upper (D 3) (R 3) [6,24,257,96] 13 := by
  apply FastRouting.sound _ _ [6,24,257,96] 13 (by decide) (choices 2) [33,96,129,160] r5840 c5840
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5840_33
  · exact u2332
  · exact m5840_129
  · exact u2333

def b5841 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 292 41 209 225 193 193 449), lower := (rows 7 26 292 41 16 32 64 128 256), losses := [] }

theorem u5841 : Upper (D 3) (R 3) [6,24,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5841
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5842_33 : Upper (D 3) (R 3) [6,24,288,65,33] 13 :=
  permutation_upper _ _ _ [6,24,288,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2334

def r5842 : Route 9 := (fun mask => (mask,id))

def c5842 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5842 : Upper (D 3) (R 3) [6,24,288,65] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5842 c5842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5842_33
  · exact u2336
  · exact u2337
  · exact u2338
  · exact u2339
  · exact u2340

def b5843 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 26 292 104 209 225 193 193 449), lower := (rows 7 26 292 104 16 32 64 128 256), losses := [] }

theorem u5843 : Upper (D 3) (R 3) [6,24,288,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5843
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5844_33 : Upper (D 3) (R 3) [6,24,288,192,33] 13 :=
  permutation_upper _ _ _ [6,24,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2335

theorem m5844_65 : Upper (D 3) (R 3) [6,24,288,192,65] 13 :=
  permutation_upper _ _ _ [6,24,288,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2340

theorem m5844_96 : Upper (D 3) (R 3) [6,24,288,192,96] 13 :=
  permutation_upper _ _ _ [6,24,288,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2341

def r5844 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5844 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5844 : Upper (D 3) (R 3) [6,24,288,192] 13 := by
  apply FastRouting.sound _ _ [6,24,288,192] 13 (by decide) (choices 2) [33,65,96,192] r5844 c5844
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m5844_33
  · exact m5844_65
  · exact m5844_96
  · exact u2342

def b5845 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 25 504 488 488 488 488), lower := (rows 7 35 69 25 16 32 64 128 256), losses := [] }

theorem u5845 : Upper (D 3) (R 3) [6,33,65,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5845
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5846 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 69 41 472 504 472 472 472), lower := (rows 7 35 69 41 16 32 64 128 256), losses := [] }

theorem u5846 : Upper (D 3) (R 3) [6,33,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5846
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5847_9 : Upper (D 3) (R 3) [6,33,65,48,9] 13 :=
  permutation_upper _ _ _ [6,33,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2343

theorem m5847_65 : Upper (D 3) (R 3) [6,33,65,48,65] 13 :=
  permutation_upper _ _ _ [6,33,65,33,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2349

def r5847 : Route 9 := (fun mask => (mask,id))

def c5847 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u5847 : Upper (D 3) (R 3) [6,33,65,48] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r5847 c5847
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5847_9
  · exact m5847_65
  · exact u2355
  · exact u2356
  · exact u2357
  · exact u2358
  · exact u2359
  · exact u2360
  · exact u2361
  · exact u2362

def b5848 : PairBound 9 := { available := 409, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 104 409 441 473 409 409), lower := (rows 7 35 69 104 16 32 64 128 256), losses := [] }

theorem u5848 : Upper (D 3) (R 3) [6,33,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5848
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5849 : PairBound 9 := { available := 504, camps := [{ cop := 3, region := 368, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 137 504 504 504 504 504), lower := (rows 7 35 69 137 16 32 64 128 256), losses := [] }

theorem u5849 : Upper (D 3) (R 3) [6,33,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5849
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5850_9 : Upper (D 3) (R 3) [6,33,65,144,9] 13 :=
  permutation_upper _ _ _ [6,33,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2344

theorem m5850_33 : Upper (D 3) (R 3) [6,33,65,144,33] 13 :=
  permutation_upper _ _ _ [6,33,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2350

theorem m5850_40 : Upper (D 3) (R 3) [6,33,65,144,40] 13 :=
  permutation_upper _ _ _ [6,33,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2357

theorem m5850_65 : Upper (D 3) (R 3) [6,33,65,144,65] 13 :=
  permutation_upper _ _ _ [6,33,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2350

theorem m5850_72 : Upper (D 3) (R 3) [6,33,65,144,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2357

theorem m5850_96 : Upper (D 3) (R 3) [6,33,65,144,96] 13 :=
  permutation_upper _ _ _ [6,33,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2363

theorem m5850_129 : Upper (D 3) (R 3) [6,33,65,144,129] 13 :=
  permutation_upper _ _ _ [6,33,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2366

theorem m5850_192 : Upper (D 3) (R 3) [6,33,65,144,192] 13 :=
  permutation_upper _ _ _ [6,33,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2372

theorem m5850_320 : Upper (D 3) (R 3) [6,33,65,144,320] 13 :=
  permutation_upper _ _ _ [6,33,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2375

def r5850 : Route 9 := (fun mask => (mask,id))

def c5850 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u5850 : Upper (D 3) (R 3) [6,33,65,144] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r5850 c5850
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5850_9
  · exact m5850_33
  · exact m5850_40
  · exact m5850_65
  · exact m5850_72
  · exact m5850_96
  · exact m5850_129
  · exact u2371
  · exact u2372
  · exact m5850_192
  · exact u2373
  · exact u2374
  · exact u2375
  · exact m5850_320
  · exact u2376

theorem m5851_9 : Upper (D 3) (R 3) [6,33,65,160,9] 13 :=
  permutation_upper _ _ _ [6,33,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2345

theorem m5851_65 : Upper (D 3) (R 3) [6,33,65,160,65] 13 :=
  permutation_upper _ _ _ [6,33,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2351

theorem m5851_72 : Upper (D 3) (R 3) [6,33,65,160,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2358

theorem m5851_129 : Upper (D 3) (R 3) [6,33,65,160,129] 13 :=
  permutation_upper _ _ _ [6,33,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2367

theorem m5851_136 : Upper (D 3) (R 3) [6,33,65,160,136] 13 :=
  permutation_upper _ _ _ [6,33,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2372

def r5851 : Route 9 := (fun mask => (mask,id))

def c5851 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u5851 : Upper (D 3) (R 3) [6,33,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r5851 c5851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5851_9
  · exact m5851_65
  · exact m5851_72
  · exact m5851_129
  · exact m5851_136
  · exact u2377
  · exact u2378
  · exact u2379
  · exact u2380
  · exact u2381

def b5852 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 69 265 248 248 248 248 504), lower := (rows 7 35 69 265 16 32 64 128 256), losses := [] }

theorem u5852 : Upper (D 3) (R 3) [6,33,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5852
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5853_9 : Upper (D 3) (R 3) [6,33,65,272,9] 13 :=
  permutation_upper _ _ _ [6,33,65,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2346

theorem m5853_33 : Upper (D 3) (R 3) [6,33,65,272,33] 13 :=
  permutation_upper _ _ _ [6,33,65,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2352

theorem m5853_40 : Upper (D 3) (R 3) [6,33,65,272,40] 13 :=
  permutation_upper _ _ _ [6,33,65,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2360

theorem m5853_65 : Upper (D 3) (R 3) [6,33,65,272,65] 13 :=
  permutation_upper _ _ _ [6,33,65,33,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2352

theorem m5853_72 : Upper (D 3) (R 3) [6,33,65,272,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2360

theorem m5853_96 : Upper (D 3) (R 3) [6,33,65,272,96] 13 :=
  permutation_upper _ _ _ [6,33,65,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2364

theorem m5853_129 : Upper (D 3) (R 3) [6,33,65,272,129] 13 :=
  permutation_upper _ _ _ [6,33,65,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2368

theorem m5853_136 : Upper (D 3) (R 3) [6,33,65,272,136] 13 :=
  permutation_upper _ _ _ [6,33,65,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2374

theorem m5853_160 : Upper (D 3) (R 3) [6,33,65,272,160] 13 :=
  permutation_upper _ _ _ [6,33,65,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2379

theorem m5853_192 : Upper (D 3) (R 3) [6,33,65,272,192] 13 :=
  permutation_upper _ _ _ [6,33,65,160,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2379

def r5853 : Route 9 := (fun mask => (mask,id))

def c5853 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5853 : Upper (D 3) (R 3) [6,33,65,272] 13 := by
  apply FastRouting.sound _ _ [6,33,65,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r5853 c5853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5853_9
  · exact m5853_33
  · exact m5853_40
  · exact m5853_65
  · exact m5853_72
  · exact m5853_96
  · exact m5853_129
  · exact m5853_136
  · exact m5853_160
  · exact m5853_192

theorem m5854_9 : Upper (D 3) (R 3) [6,33,65,288,9] 13 :=
  permutation_upper _ _ _ [6,33,65,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2347

theorem m5854_65 : Upper (D 3) (R 3) [6,33,65,288,65] 13 :=
  permutation_upper _ _ _ [6,33,65,33,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2353

theorem m5854_72 : Upper (D 3) (R 3) [6,33,65,288,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2361

theorem m5854_129 : Upper (D 3) (R 3) [6,33,65,288,129] 13 :=
  permutation_upper _ _ _ [6,33,65,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2369

theorem m5854_136 : Upper (D 3) (R 3) [6,33,65,288,136] 13 :=
  permutation_upper _ _ _ [6,33,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2375

theorem m5854_192 : Upper (D 3) (R 3) [6,33,65,288,192] 13 :=
  permutation_upper _ _ _ [6,33,65,160,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2380

def r5854 : Route 9 := (fun mask => (mask,id))

def c5854 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5854 : Upper (D 3) (R 3) [6,33,65,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,288] 13 (by decide) (choices 2) [9,65,72,129,136,192] r5854 c5854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5854_9
  · exact m5854_65
  · exact m5854_72
  · exact m5854_129
  · exact m5854_136
  · exact m5854_192

theorem m5855_9 : Upper (D 3) (R 3) [6,33,65,384,9] 13 :=
  permutation_upper _ _ _ [6,33,65,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2348

theorem m5855_33 : Upper (D 3) (R 3) [6,33,65,384,33] 13 :=
  permutation_upper _ _ _ [6,33,65,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2354

theorem m5855_40 : Upper (D 3) (R 3) [6,33,65,384,40] 13 :=
  permutation_upper _ _ _ [6,33,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2362

theorem m5855_65 : Upper (D 3) (R 3) [6,33,65,384,65] 13 :=
  permutation_upper _ _ _ [6,33,65,33,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2354

theorem m5855_72 : Upper (D 3) (R 3) [6,33,65,384,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2362

theorem m5855_96 : Upper (D 3) (R 3) [6,33,65,384,96] 13 :=
  permutation_upper _ _ _ [6,33,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2365

theorem m5855_129 : Upper (D 3) (R 3) [6,33,65,384,129] 13 :=
  permutation_upper _ _ _ [6,33,65,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2370

theorem m5855_136 : Upper (D 3) (R 3) [6,33,65,384,136] 13 :=
  permutation_upper _ _ _ [6,33,65,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2376

theorem m5855_160 : Upper (D 3) (R 3) [6,33,65,384,160] 13 :=
  permutation_upper _ _ _ [6,33,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2381

theorem m5855_192 : Upper (D 3) (R 3) [6,33,65,384,192] 13 :=
  permutation_upper _ _ _ [6,33,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2381

def r5855 : Route 9 := (fun mask => (mask,id))

def c5855 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5855 : Upper (D 3) (R 3) [6,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r5855 c5855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5855_9
  · exact m5855_33
  · exact m5855_40
  · exact m5855_65
  · exact m5855_72
  · exact m5855_96
  · exact m5855_129
  · exact m5855_136
  · exact m5855_160
  · exact m5855_192

def r5856 : Route 9 := (fun mask => (mask,id))

def c5856 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5856 : Upper (D 3) (R 3) [6,33,72,17] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5856 c5856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2382
  · exact u2383
  · exact u2384
  · exact u2385
  · exact u2386
  · exact u2387
  · exact u2388
  · exact u2389
  · exact u2390
  · exact u2391

def b5857 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 41 465 497 465 465 465), lower := (rows 7 35 76 41 16 32 64 128 256), losses := [] }

theorem u5857 : Upper (D 3) (R 3) [6,33,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5857
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5858 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 35 76 56 465 481 449 449 449), lower := (rows 7 35 76 56 16 32 64 128 256), losses := [] }

theorem u5858 : Upper (D 3) (R 3) [6,33,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5858
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5859 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 73 433 433 497 433 433), lower := (rows 7 35 76 73 16 32 64 128 256), losses := [] }

theorem u5859 : Upper (D 3) (R 3) [6,33,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5859
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5860 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 88 433 417 481 417 417), lower := (rows 7 35 76 88 16 32 64 128 256), losses := [] }

theorem u5860 : Upper (D 3) (R 3) [6,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5860
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5861 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 104 401 433 465 401 401), lower := (rows 7 35 76 104 16 32 64 128 256), losses := [] }

theorem u5861 : Upper (D 3) (R 3) [6,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5861
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5862 : Route 9 := (fun mask => (mask,id))

def c5862 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5862 : Upper (D 3) (R 3) [6,33,72,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5862 c5862
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2392
  · exact u2393
  · exact u2394
  · exact u2395
  · exact u2396
  · exact u2397
  · exact u2398
  · exact u2399
  · exact u2400
  · exact u2401

def r5863 : Route 9 := (fun mask => (mask,id))

def c5863 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u5863 : Upper (D 3) (R 3) [6,33,72,144] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r5863 c5863
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2402
  · exact u2403
  · exact u2404
  · exact u2405
  · exact u2406
  · exact u2407
  · exact u2408
  · exact u2409
  · exact u2410
  · exact u2411

def b5864 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 35 76 168 465 497 465 465 465), lower := (rows 7 35 76 168 16 32 64 128 256), losses := [] }

theorem u5864 : Upper (D 3) (R 3) [6,33,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5864
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5865 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 200 433 433 497 433 433), lower := (rows 7 35 76 200 16 32 64 128 256), losses := [] }

theorem u5865 : Upper (D 3) (R 3) [6,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5865
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5866 : Route 9 := (fun mask => (mask,id))

def c5866 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5866 : Upper (D 3) (R 3) [6,33,72,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5866 c5866
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2412
  · exact u2413
  · exact u2414
  · exact u2415
  · exact u2416
  · exact u2417

def r5867 : Route 9 := (fun mask => (mask,id))

def c5867 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5867 : Upper (D 3) (R 3) [6,33,72,272] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5867 c5867
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2418
  · exact u2419
  · exact u2420
  · exact u2421
  · exact u2422
  · exact u2423

def b5868 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 35 76 296 209 241 209 209 465), lower := (rows 7 35 76 296 16 32 64 128 256), losses := [] }

theorem u5868 : Upper (D 3) (R 3) [6,33,72,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5868
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5869 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 328 177 177 241 177 433), lower := (rows 7 35 76 328 16 32 64 128 256), losses := [] }

theorem u5869 : Upper (D 3) (R 3) [6,33,72,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5869
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5870 : Route 9 := (fun mask => (mask,id))

def c5870 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5870 : Upper (D 3) (R 3) [6,33,72,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r5870 c5870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2424
  · exact u2425
  · exact u2426
  · exact u2427
  · exact u2428
  · exact u2429

def r5871 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5871 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u5871 : Upper (D 3) (R 3) [6,33,192,17] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r5871 c5871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2430
  · exact u2431
  · exact u2432
  · exact u2433
  · exact u2434
  · exact u2435
  · exact u2436
  · exact u2437
  · exact u2438
  · exact u2439
  · exact u2440

def b5872 : PairBound 9 := { available := 473, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 473 505 473 473 473), lower := (rows 7 35 196 41 16 32 64 128 256), losses := [] }

theorem u5872 : Upper (D 3) (R 3) [6,33,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5872
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5873_9 : Upper (D 3) (R 3) [6,33,192,48,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2432

def r5873 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5873 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u5873 : Upper (D 3) (R 3) [6,33,192,48] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48] 13 (by decide) (choices 2) [9,65,72,192,257,264,320] r5873 c5873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5873_9
  · exact u2445
  · exact u2446
  · exact u2447
  · exact u2448
  · exact u2449
  · exact u2450

def b5874 : PairBound 9 := { available := 441, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 73 441 441 505 441 441), lower := (rows 7 35 196 73 16 32 64 128 256), losses := [] }

theorem u5874 : Upper (D 3) (R 3) [6,33,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5874
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5875_9 : Upper (D 3) (R 3) [6,33,192,80,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2434

theorem m5875_33 : Upper (D 3) (R 3) [6,33,192,80,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2441

theorem m5875_40 : Upper (D 3) (R 3) [6,33,192,80,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2446

theorem m5875_129 : Upper (D 3) (R 3) [6,33,192,80,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2451

def r5875 : Route 9 := (fun mask => (mask,id))

def c5875 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u5875 : Upper (D 3) (R 3) [6,33,192,80] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r5875 c5875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5875_9
  · exact m5875_33
  · exact m5875_40
  · exact m5875_129
  · exact u2457
  · exact u2458
  · exact u2459
  · exact u2460
  · exact u2461
  · exact u2462

theorem m5876_9 : Upper (D 3) (R 3) [6,33,192,96,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2435

theorem m5876_129 : Upper (D 3) (R 3) [6,33,192,96,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2452

theorem m5876_136 : Upper (D 3) (R 3) [6,33,192,96,136] 13 :=
  permutation_upper _ _ _ [6,33,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2458

def r5876 : Route 9 := (fun mask => (mask,id))

def c5876 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u5876 : Upper (D 3) (R 3) [6,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r5876 c5876
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5876_9
  · exact m5876_129
  · exact m5876_136
  · exact u2463
  · exact u2464
  · exact u2465

def b5877 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 200 313 313 377 441 313), lower := (rows 7 35 196 200 16 32 64 128 256), losses := [] }

theorem u5877 : Upper (D 3) (R 3) [6,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5877
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5878_9 : Upper (D 3) (R 3) [6,33,192,257,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2437

theorem m5878_33 : Upper (D 3) (R 3) [6,33,192,257,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2442

theorem m5878_40 : Upper (D 3) (R 3) [6,33,192,257,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2448

theorem m5878_65 : Upper (D 3) (R 3) [6,33,192,257,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2453

theorem m5878_72 : Upper (D 3) (R 3) [6,33,192,257,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2459

theorem m5878_96 : Upper (D 3) (R 3) [6,33,192,257,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2463

theorem m5878_192 : Upper (D 3) (R 3) [6,33,192,257,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2466

def r5878 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5878 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5878 : Upper (D 3) (R 3) [6,33,192,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r5878 c5878
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5878_9
  · exact m5878_33
  · exact m5878_40
  · exact m5878_65
  · exact m5878_72
  · exact m5878_96
  · exact m5878_192

theorem m5879_9 : Upper (D 3) (R 3) [6,33,192,272,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2438

theorem m5879_33 : Upper (D 3) (R 3) [6,33,192,272,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2443

theorem m5879_40 : Upper (D 3) (R 3) [6,33,192,272,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2449

theorem m5879_65 : Upper (D 3) (R 3) [6,33,192,272,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2454

theorem m5879_72 : Upper (D 3) (R 3) [6,33,192,272,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2460

theorem m5879_96 : Upper (D 3) (R 3) [6,33,192,272,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2464

theorem m5879_192 : Upper (D 3) (R 3) [6,33,192,272,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2467

def r5879 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5879 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u5879 : Upper (D 3) (R 3) [6,33,192,272] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r5879 c5879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5879_9
  · exact m5879_33
  · exact m5879_40
  · exact m5879_65
  · exact m5879_72
  · exact m5879_96
  · exact m5879_192

#print axioms u5879
end Delivery.IrregularNine14.P03
