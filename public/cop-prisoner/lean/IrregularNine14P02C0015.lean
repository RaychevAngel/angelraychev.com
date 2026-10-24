import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0005
import IrregularNine14P02C0006

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 84 268 144 297 361 425 297), lower := (rows 51 194 84 268 144 32 64 128 256), losses := [] }

theorem u900 : Upper (D 2) (R 2) [50,192,80,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b900
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r901 : Route 9 := (fun mask => (mask,id))

def c901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u901 : Upper (D 2) (R 2) [50,192,80,260,256] 13 := by
  apply FastRouting.sound _ _ [50,192,80,260,256] 13 (by decide) (choices 1) [1,8,128] r901 c901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u340
  · exact u341
  · exact u342

def b902 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 426, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 296 17 428 460 396 396), lower := (rows 51 194 84 296 17 32 64 128 256), losses := [] }

theorem u902 : Upper (D 2) (R 2) [50,192,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b902
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b903 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 84 296 20 425 457 393 393), lower := (rows 51 194 84 296 20 32 64 128 256), losses := [] }

theorem u903 : Upper (D 2) (R 2) [50,192,80,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b903
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 296 24 421 453 389 389), lower := (rows 51 194 84 296 24 32 64 128 256), losses := [] }

theorem u904 : Upper (D 2) (R 2) [50,192,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b904
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b905 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 84 296 144 301 333 397 269), lower := (rows 51 194 84 296 144 32 64 128 256), losses := [] }

theorem u905 : Upper (D 2) (R 2) [50,192,80,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b905
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r906 : Route 9 := (fun mask => (mask,id))

def c906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u906 : Upper (D 2) (R 2) [50,192,80,288,256] 13 := by
  apply FastRouting.sound _ _ [50,192,80,288,256] 13 (by decide) (choices 1) [1,4,8,128] r906 c906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u343
  · exact u344
  · exact u345
  · exact u346

def b907 : PairBound 9 := { available := 300, camps := [{ cop := 2, region := 426, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 392 17 300 364 428 300), lower := (rows 51 194 84 392 17 32 64 128 256), losses := [] }

theorem u907 : Upper (D 2) (R 2) [50,192,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b907
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 84 392 20 297 361 425 297), lower := (rows 51 194 84 392 20 32 64 128 256), losses := [] }

theorem u908 : Upper (D 2) (R 2) [50,192,80,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b908
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 324, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 392 24 293 357 421 293), lower := (rows 51 194 84 392 24 32 64 128 256), losses := [] }

theorem u909 : Upper (D 2) (R 2) [50,192,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b909
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 84 392 48 301 333 397 269), lower := (rows 51 194 84 392 48 32 64 128 256), losses := [] }

theorem u910 : Upper (D 2) (R 2) [50,192,80,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b910
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r911 : Route 9 := (fun mask => (mask,id))

def c911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u911 : Upper (D 2) (R 2) [50,192,80,384,256] 13 := by
  apply FastRouting.sound _ _ [50,192,80,384,256] 13 (by decide) (choices 1) [1,4,8] r911 c911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u347
  · exact u348
  · exact u349

def b912 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 194 261 280 20 232 232 232 488), lower := (rows 51 194 261 280 20 32 64 128 256), losses := [] }

theorem u912 : Upper (D 2) (R 2) [50,192,257,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b912
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 194 261 280 24 228 228 228 484), lower := (rows 51 194 261 280 24 32 64 128 256), losses := [] }

theorem u913 : Upper (D 2) (R 2) [50,192,257,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b913
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 261 280 48 236 204 204 460), lower := (rows 51 194 261 280 48 32 64 128 256), losses := [] }

theorem u914 : Upper (D 2) (R 2) [50,192,257,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b914
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 194 261 280 80 172 236 172 428), lower := (rows 51 194 261 280 80 32 64 128 256), losses := [] }

theorem u915 : Upper (D 2) (R 2) [50,192,257,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b915
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r916 : Route 9 := (fun mask => (mask,id))

def c916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u916 : Upper (D 2) (R 2) [50,192,257,320,4] 13 := by
  apply FastRouting.sound _ _ [50,192,257,320,4] 13 (by decide) (choices 1) [8,16,128] r916 c916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u350
  · exact u351
  · exact u352

def b917 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 261 328 24 180 244 180 436), lower := (rows 51 194 261 328 24 32 64 128 256), losses := [] }

theorem u917 : Upper (D 2) (R 2) [50,192,257,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b917
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 261 328 48 188 220 156 412), lower := (rows 51 194 261 328 48 32 64 128 256), losses := [] }

theorem u918 : Upper (D 2) (R 2) [50,192,257,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b918
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 261 328 144 60 124 188 316), lower := (rows 51 194 261 328 144 32 64 128 256), losses := [] }

theorem u919 : Upper (D 2) (R 2) [50,192,257,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b919
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b920 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 276 296 17 236 204 204 460), lower := (rows 51 194 276 296 17 32 64 128 256), losses := [] }

theorem u920 : Upper (D 2) (R 2) [50,192,272,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b920
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b921 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 276 296 20 233 201 201 457), lower := (rows 51 194 276 296 20 32 64 128 256), losses := [] }

theorem u921 : Upper (D 2) (R 2) [50,192,272,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b921
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 276 296 24 229 197 197 453), lower := (rows 51 194 276 296 24 32 64 128 256), losses := [] }

theorem u922 : Upper (D 2) (R 2) [50,192,272,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b922
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b923 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 194 276 296 80 173 205 141 397), lower := (rows 51 194 276 296 80 32 64 128 256), losses := [] }

theorem u923 : Upper (D 2) (R 2) [50,192,272,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b923
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b924 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 276 328 17 172 236 172 428), lower := (rows 51 194 276 328 17 32 64 128 256), losses := [] }

theorem u924 : Upper (D 2) (R 2) [50,192,272,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b924
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 276 328 20 169 233 169 425), lower := (rows 51 194 276 328 20 32 64 128 256), losses := [] }

theorem u925 : Upper (D 2) (R 2) [50,192,272,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b925
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 276 328 24 165 229 165 421), lower := (rows 51 194 276 328 24 32 64 128 256), losses := [] }

theorem u926 : Upper (D 2) (R 2) [50,192,272,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b926
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 276 328 48 173 205 141 397), lower := (rows 51 194 276 328 48 32 64 128 256), losses := [] }

theorem u927 : Upper (D 2) (R 2) [50,192,272,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b927
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b928 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 276 328 144 45 109 173 301), lower := (rows 51 194 276 328 144 32 64 128 256), losses := [] }

theorem u928 : Upper (D 2) (R 2) [50,192,272,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b928
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m929_8 : Upper (D 2) (R 2) [50,192,320,384,1,8] 13 :=
  permutation_upper _ _ _ [50,192,320,384,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u353

def r929 : Route 9 := (fun mask => (mask,id))

def c929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u929 : Upper (D 2) (R 2) [50,192,320,384,1] 13 := by
  apply FastRouting.sound _ _ [50,192,320,384,1] 13 (by decide) (choices 1) [4,8,16] r929 c929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u353
  · exact m929_8
  · exact u354

def b930 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 324 392 20 57 121 185 313), lower := (rows 51 194 324 392 20 32 64 128 256), losses := [] }

theorem u930 : Upper (D 2) (R 2) [50,192,320,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b930
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b931 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 324 392 48 61 93 157 285), lower := (rows 51 194 324 392 48 32 64 128 256), losses := [] }

theorem u931 : Upper (D 2) (R 2) [50,192,320,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b931
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b932 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 14 152 48 480 448 448 448), lower := (rows 113 7 14 152 48 32 64 128 256), losses := [] }

theorem u932 : Upper (D 2) (R 2) [112,5,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b932
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b933 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 7 14 152 144 352 352 480 352), lower := (rows 113 7 14 152 144 32 64 128 256), losses := [] }

theorem u933 : Upper (D 2) (R 2) [112,5,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b933
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r934 : Route 9 := (fun mask => (mask,id))

def c934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u934 : Upper (D 2) (R 2) [112,5,10,144,256] 13 := by
  apply FastRouting.sound _ _ [112,5,10,144,256] 13 (by decide) (choices 1) [64,128,256] r934 c934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u355
  · exact u356
  · exact u357

def b935 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 14 392 48 496 464 464 464), lower := (rows 113 7 14 392 48 32 64 128 256), losses := [] }

theorem u935 : Upper (D 2) (R 2) [112,5,10,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b935
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m936_16 : Upper (D 2) (R 2) [112,5,10,384,128,16] 13 :=
  permutation_upper _ _ _ [112,5,10,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u358

theorem m936_64 : Upper (D 2) (R 2) [112,5,10,384,128,64] 13 :=
  permutation_upper _ _ _ [112,5,10,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u359

def r936 : Route 9 := (fun mask => (mask,id))

def c936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u936 : Upper (D 2) (R 2) [112,5,10,384,128] 13 := by
  apply FastRouting.sound _ _ [112,5,10,384,128] 13 (by decide) (choices 1) [16,64,256] r936 c936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m936_16
  · exact m936_64
  · exact u360

def b937 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 28 138 48 480 448 448 448), lower := (rows 113 7 28 138 48 32 64 128 256), losses := [] }

theorem u937 : Upper (D 2) (R 2) [112,5,24,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b937
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 113 7 28 138 144 352 352 480 352), lower := (rows 113 7 28 138 144 32 64 128 256), losses := [] }

theorem u938 : Upper (D 2) (R 2) [112,5,24,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b938
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r939 : Route 9 := (fun mask => (mask,id))

def c939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u939 : Upper (D 2) (R 2) [112,5,24,130,256] 13 := by
  apply FastRouting.sound _ _ [112,5,24,130,256] 13 (by decide) (choices 1) [64,128,256] r939 c939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u361
  · exact u362
  · exact u363

def b940 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 168 18 480 448 448 448), lower := (rows 113 7 28 168 18 32 64 128 256), losses := [] }

theorem u940 : Upper (D 2) (R 2) [112,5,24,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b940
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 28 168 80 418 450 386 386), lower := (rows 113 7 28 168 80 32 64 128 256), losses := [] }

theorem u941 : Upper (D 2) (R 2) [112,5,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b941
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 113 7 28 168 144 354 322 450 322), lower := (rows 113 7 28 168 144 32 64 128 256), losses := [] }

theorem u942 : Upper (D 2) (R 2) [112,5,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b942
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r943 : Route 9 := (fun mask => (mask,id))

def c943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u943 : Upper (D 2) (R 2) [112,5,24,160,256] 13 := by
  apply FastRouting.sound _ _ [112,5,24,160,256] 13 (by decide) (choices 1) [2,64,128,256] r943 c943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u364
  · exact u365
  · exact u366
  · exact u367

def b944 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 392 18 480 480 480 480), lower := (rows 113 7 28 392 18 32 64 128 256), losses := [] }

theorem u944 : Upper (D 2) (R 2) [112,5,24,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b944
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 28 392 48 482 450 450 450), lower := (rows 113 7 28 392 48 32 64 128 256), losses := [] }

theorem u945 : Upper (D 2) (R 2) [112,5,24,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b945
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 113 7 28 392 144 354 354 482 354), lower := (rows 113 7 28 392 144 32 64 128 256), losses := [] }

theorem u946 : Upper (D 2) (R 2) [112,5,24,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b946
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 134 152 24 352 352 480 352), lower := (rows 113 7 134 152 24 32 64 128 256), losses := [] }

theorem u947 : Upper (D 2) (R 2) [112,5,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b947
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 134 152 48 360 328 456 328), lower := (rows 113 7 134 152 48 32 64 128 256), losses := [] }

theorem u948 : Upper (D 2) (R 2) [112,5,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b948
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r949 : Route 9 := (fun mask => (mask,id))

def c949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u949 : Upper (D 2) (R 2) [112,5,130,144,256] 13 := by
  apply FastRouting.sound _ _ [112,5,130,144,256] 13 (by decide) (choices 1) [8,64,256] r949 c949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u368
  · exact u369
  · exact u370

def b950 : PairBound 9 := { available := 480, camps := [{ cop := 8, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 134 280 24 480 480 480 480), lower := (rows 113 7 134 280 24 32 64 128 256), losses := [] }

theorem u950 : Upper (D 2) (R 2) [112,5,130,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b950
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 134 280 48 488 456 456 456), lower := (rows 113 7 134 280 48 32 64 128 256), losses := [] }

theorem u951 : Upper (D 2) (R 2) [112,5,130,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b951
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 113 7 134 280 144 360 360 488 360), lower := (rows 113 7 134 280 144 32 64 128 256), losses := [] }

theorem u952 : Upper (D 2) (R 2) [112,5,130,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b952
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 113 7 134 280 272 232 232 232 488), lower := (rows 113 7 134 280 272 32 64 128 256), losses := [] }

theorem u953 : Upper (D 2) (R 2) [112,5,130,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b953
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 134 392 24 368 368 496 368), lower := (rows 113 7 134 392 24 32 64 128 256), losses := [] }

theorem u954 : Upper (D 2) (R 2) [112,5,130,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b954
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 134 392 48 376 344 472 344), lower := (rows 113 7 134 392 48 32 64 128 256), losses := [] }

theorem u955 : Upper (D 2) (R 2) [112,5,130,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b955
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m956_8 : Upper (D 2) (R 2) [112,5,130,384,256,8] 13 :=
  permutation_upper _ _ _ [112,5,130,384,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u371

theorem m956_16 : Upper (D 2) (R 2) [112,5,130,384,256,16] 13 :=
  permutation_upper _ _ _ [112,5,130,384,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u372

theorem m956_64 : Upper (D 2) (R 2) [112,5,130,384,256,64] 13 :=
  permutation_upper _ _ _ [112,5,130,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u373

def r956 : Route 9 := (fun mask => (mask,id))

def c956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u956 : Upper (D 2) (R 2) [112,5,130,384,256] 13 := by
  apply FastRouting.sound _ _ [112,5,130,384,256] 13 (by decide) (choices 1) [8,16,64] r956 c956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m956_8
  · exact m956_16
  · exact m956_64

def b957 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 140 26 48 480 448 448 448), lower := (rows 113 7 140 26 48 32 64 128 256), losses := [] }

theorem u957 : Upper (D 2) (R 2) [112,5,136,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b957
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 484, targets := 16 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(2,4)], upper := (rows 113 7 140 26 144 352 352 480 352), lower := (rows 113 7 140 26 144 32 64 128 256), losses := [] }

theorem u958 : Upper (D 2) (R 2) [112,5,136,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b958
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r959 : Route 9 := (fun mask => (mask,id))

def c959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u959 : Upper (D 2) (R 2) [112,5,136,18,256] 13 := by
  apply FastRouting.sound _ _ [112,5,136,18,256] 13 (by decide) (choices 1) [64,128,256] r959 c959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u374
  · exact u375
  · exact u376

#print axioms u959
end Delivery.IrregularNine14.P02
