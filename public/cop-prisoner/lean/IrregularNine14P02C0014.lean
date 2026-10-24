import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0005

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 51 194 28 296 80 421 453 389 389), lower := (rows 51 194 28 296 80 32 64 128 256), losses := [] }

theorem u840 : Upper (D 2) (R 2) [50,192,24,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b840
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 28 296 272 229 197 197 453), lower := (rows 51 194 28 296 272 32 64 128 256), losses := [] }

theorem u841 : Upper (D 2) (R 2) [50,192,24,288,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b841
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 28 328 17 420 484 420 420), lower := (rows 51 194 28 328 17 32 64 128 256), losses := [] }

theorem u842 : Upper (D 2) (R 2) [50,192,24,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b842
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 28 328 20 417 481 417 417), lower := (rows 51 194 28 328 20 32 64 128 256), losses := [] }

theorem u843 : Upper (D 2) (R 2) [50,192,24,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b843
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 28 328 48 421 453 389 389), lower := (rows 51 194 28 328 48 32 64 128 256), losses := [] }

theorem u844 : Upper (D 2) (R 2) [50,192,24,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b844
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 28 328 144 293 357 421 293), lower := (rows 51 194 28 328 144 32 64 128 256), losses := [] }

theorem u845 : Upper (D 2) (R 2) [50,192,24,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b845
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b846 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 20, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 28 328 272 165 229 165 421), lower := (rows 51 194 28 328 272 32 64 128 256), losses := [] }

theorem u846 : Upper (D 2) (R 2) [50,192,24,320,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b846
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b847 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 324, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 69 140 24 304 368 432 304), lower := (rows 51 194 69 140 24 32 64 128 256), losses := [] }

theorem u847 : Upper (D 2) (R 2) [50,192,65,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b847
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 69 140 48 312 344 408 280), lower := (rows 51 194 69 140 48 32 64 128 256), losses := [] }

theorem u848 : Upper (D 2) (R 2) [50,192,65,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b848
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m849_8 : Upper (D 2) (R 2) [50,192,65,132,256,8] 13 :=
  permutation_upper _ _ _ [50,192,65,132,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u310

theorem m849_16 : Upper (D 2) (R 2) [50,192,65,132,256,16] 13 :=
  permutation_upper _ _ _ [50,192,65,132,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u311

def r849 : Route 9 := (fun mask => (mask,id))

def c849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u849 : Upper (D 2) (R 2) [50,192,65,132,256] 13 := by
  apply FastRouting.sound _ _ [50,192,65,132,256] 13 (by decide) (choices 1) [8,16,256] r849 c849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m849_8
  · exact m849_16
  · exact u312

def b850 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 152 20 296 360 424 296), lower := (rows 51 194 69 152 20 32 64 128 256), losses := [] }

theorem u850 : Upper (D 2) (R 2) [50,192,65,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b850
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 194 69 152 24 292 356 420 292), lower := (rows 51 194 69 152 24 32 64 128 256), losses := [] }

theorem u851 : Upper (D 2) (R 2) [50,192,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b851
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 69 152 48 300 332 396 268), lower := (rows 51 194 69 152 48 32 64 128 256), losses := [] }

theorem u852 : Upper (D 2) (R 2) [50,192,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b852
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r853 : Route 9 := (fun mask => (mask,id))

def c853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u853 : Upper (D 2) (R 2) [50,192,65,144,256] 13 := by
  apply FastRouting.sound _ _ [50,192,65,144,256] 13 (by decide) (choices 1) [4,8,256] r853 c853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u313
  · exact u314
  · exact u315

def b854 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 268 24 432 496 432 432), lower := (rows 51 194 69 268 24 32 64 128 256), losses := [] }

theorem u854 : Upper (D 2) (R 2) [50,192,65,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b854
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 69 268 48 440 472 408 408), lower := (rows 51 194 69 268 48 32 64 128 256), losses := [] }

theorem u855 : Upper (D 2) (R 2) [50,192,65,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b855
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 69 268 144 312 376 440 312), lower := (rows 51 194 69 268 144 32 64 128 256), losses := [] }

theorem u856 : Upper (D 2) (R 2) [50,192,65,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b856
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m857_8 : Upper (D 2) (R 2) [50,192,65,260,256,8] 13 :=
  permutation_upper _ _ _ [50,192,65,260,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u316

theorem m857_16 : Upper (D 2) (R 2) [50,192,65,260,256,16] 13 :=
  permutation_upper _ _ _ [50,192,65,260,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u317

theorem m857_128 : Upper (D 2) (R 2) [50,192,65,260,256,128] 13 :=
  permutation_upper _ _ _ [50,192,65,260,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u318

def r857 : Route 9 := (fun mask => (mask,id))

def c857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u857 : Upper (D 2) (R 2) [50,192,65,260,256] 13 := by
  apply FastRouting.sound _ _ [50,192,65,260,256] 13 (by decide) (choices 1) [8,16,128] r857 c857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m857_8
  · exact m857_16
  · exact m857_128

def b858 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 280 20 424 488 424 424), lower := (rows 51 194 69 280 20 32 64 128 256), losses := [] }

theorem u858 : Upper (D 2) (R 2) [50,192,65,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b858
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 420, camps := [{ cop := 8, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 194 69 280 24 420 484 420 420), lower := (rows 51 194 69 280 24 32 64 128 256), losses := [] }

theorem u859 : Upper (D 2) (R 2) [50,192,65,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b859
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b860 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 69 280 48 428 460 396 396), lower := (rows 51 194 69 280 48 32 64 128 256), losses := [] }

theorem u860 : Upper (D 2) (R 2) [50,192,65,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b860
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b861 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 69 280 144 300 364 428 300), lower := (rows 51 194 69 280 144 32 64 128 256), losses := [] }

theorem u861 : Upper (D 2) (R 2) [50,192,65,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b861
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 172, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 194 69 280 272 172 236 172 428), lower := (rows 51 194 69 280 272 32 64 128 256), losses := [] }

theorem u862 : Upper (D 2) (R 2) [50,192,65,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b862
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 69 392 20 312 376 440 312), lower := (rows 51 194 69 392 20 32 64 128 256), losses := [] }

theorem u863 : Upper (D 2) (R 2) [50,192,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b863
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b864 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 324, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 69 392 24 308 372 436 308), lower := (rows 51 194 69 392 24 32 64 128 256), losses := [] }

theorem u864 : Upper (D 2) (R 2) [50,192,65,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b864
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b865 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 69 392 48 316 348 412 284), lower := (rows 51 194 69 392 48 32 64 128 256), losses := [] }

theorem u865 : Upper (D 2) (R 2) [50,192,65,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b865
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m866_4 : Upper (D 2) (R 2) [50,192,65,384,256,4] 13 :=
  permutation_upper _ _ _ [50,192,65,384,4,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u319

theorem m866_8 : Upper (D 2) (R 2) [50,192,65,384,256,8] 13 :=
  permutation_upper _ _ _ [50,192,65,384,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u320

theorem m866_16 : Upper (D 2) (R 2) [50,192,65,384,256,16] 13 :=
  permutation_upper _ _ _ [50,192,65,384,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u321

def r866 : Route 9 := (fun mask => (mask,id))

def c866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u866 : Upper (D 2) (R 2) [50,192,65,384,256] 13 := by
  apply FastRouting.sound _ _ [50,192,65,384,256] 13 (by decide) (choices 1) [4,8,16] r866 c866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m866_4
  · exact m866_8
  · exact m866_16

def b867 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 358, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 152 17 292 356 420 292), lower := (rows 51 194 76 152 17 32 64 128 256), losses := [] }

theorem u867 : Upper (D 2) (R 2) [50,192,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b867
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b868 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 76 152 20 289 353 417 289), lower := (rows 51 194 76 152 20 32 64 128 256), losses := [] }

theorem u868 : Upper (D 2) (R 2) [50,192,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b868
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 76 152 48 293 325 389 261), lower := (rows 51 194 76 152 48 32 64 128 256), losses := [] }

theorem u869 : Upper (D 2) (R 2) [50,192,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b869
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r870 : Route 9 := (fun mask => (mask,id))

def c870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u870 : Upper (D 2) (R 2) [50,192,72,144,256] 13 := by
  apply FastRouting.sound _ _ [50,192,72,144,256] 13 (by decide) (choices 1) [1,4,256] r870 c870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u322
  · exact u323
  · exact u324

def b871 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 76 265 20 432 496 432 432), lower := (rows 51 194 76 265 20 32 64 128 256), losses := [] }

theorem u871 : Upper (D 2) (R 2) [50,192,72,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b871
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 76 265 48 436 468 404 404), lower := (rows 51 194 76 265 48 32 64 128 256), losses := [] }

theorem u872 : Upper (D 2) (R 2) [50,192,72,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b872
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 76 265 144 308 372 436 308), lower := (rows 51 194 76 265 144 32 64 128 256), losses := [] }

theorem u873 : Upper (D 2) (R 2) [50,192,72,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b873
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m874_4 : Upper (D 2) (R 2) [50,192,72,257,256,4] 13 :=
  permutation_upper _ _ _ [50,192,72,257,4,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u325

theorem m874_16 : Upper (D 2) (R 2) [50,192,72,257,256,16] 13 :=
  permutation_upper _ _ _ [50,192,72,257,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u326

theorem m874_128 : Upper (D 2) (R 2) [50,192,72,257,256,128] 13 :=
  permutation_upper _ _ _ [50,192,72,257,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u327

def r874 : Route 9 := (fun mask => (mask,id))

def c874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u874 : Upper (D 2) (R 2) [50,192,72,257,256] 13 := by
  apply FastRouting.sound _ _ [50,192,72,257,256] 13 (by decide) (choices 1) [4,16,128] r874 c874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m874_4
  · exact m874_16
  · exact m874_128

def b875 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 51 194 76 268 17 432 496 432 432), lower := (rows 51 194 76 268 17 32 64 128 256), losses := [] }

theorem u875 : Upper (D 2) (R 2) [50,192,72,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b875
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 76 268 48 433 465 401 401), lower := (rows 51 194 76 268 48 32 64 128 256), losses := [] }

theorem u876 : Upper (D 2) (R 2) [50,192,72,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b876
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 76 268 144 305 369 433 305), lower := (rows 51 194 76 268 144 32 64 128 256), losses := [] }

theorem u877 : Upper (D 2) (R 2) [50,192,72,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b877
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b878 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 194 76 268 272 177 241 177 433), lower := (rows 51 194 76 268 272 32 64 128 256), losses := [] }

theorem u878 : Upper (D 2) (R 2) [50,192,72,260,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b878
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b879 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 230, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 280 17 420 484 420 420), lower := (rows 51 194 76 280 17 32 64 128 256), losses := [] }

theorem u879 : Upper (D 2) (R 2) [50,192,72,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b879
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b880 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 280 20 417 481 417 417), lower := (rows 51 194 76 280 20 32 64 128 256), losses := [] }

theorem u880 : Upper (D 2) (R 2) [50,192,72,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b880
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b881 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 76 280 48 421 453 389 389), lower := (rows 51 194 76 280 48 32 64 128 256), losses := [] }

theorem u881 : Upper (D 2) (R 2) [50,192,72,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b881
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b882 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 76 280 144 293 357 421 293), lower := (rows 51 194 76 280 144 32 64 128 256), losses := [] }

theorem u882 : Upper (D 2) (R 2) [50,192,72,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b882
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b883 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 51 194 76 280 272 165 229 165 421), lower := (rows 51 194 76 280 272 32 64 128 256), losses := [] }

theorem u883 : Upper (D 2) (R 2) [50,192,72,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b883
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r884 : Route 9 := (fun mask => (mask,id))

def c884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u884 : Upper (D 2) (R 2) [50,192,72,384,1] 13 := by
  apply FastRouting.sound _ _ [50,192,72,384,1] 13 (by decide) (choices 1) [4,16,256] r884 c884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u328
  · exact u329
  · exact u330

def b885 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 194 76 392 20 305 369 433 305), lower := (rows 51 194 76 392 20 32 64 128 256), losses := [] }

theorem u885 : Upper (D 2) (R 2) [50,192,72,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b885
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 76 392 48 309 341 405 277), lower := (rows 51 194 76 392 48 32 64 128 256), losses := [] }

theorem u886 : Upper (D 2) (R 2) [50,192,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b886
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m887_1 : Upper (D 2) (R 2) [50,192,72,384,256,1] 13 :=
  permutation_upper _ _ _ [50,192,72,384,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u330

theorem m887_4 : Upper (D 2) (R 2) [50,192,72,384,256,4] 13 :=
  permutation_upper _ _ _ [50,192,72,384,4,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u331

theorem m887_16 : Upper (D 2) (R 2) [50,192,72,384,256,16] 13 :=
  permutation_upper _ _ _ [50,192,72,384,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u332

def r887 : Route 9 := (fun mask => (mask,id))

def c887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u887 : Upper (D 2) (R 2) [50,192,72,384,256] 13 := by
  apply FastRouting.sound _ _ [50,192,72,384,256] 13 (by decide) (choices 1) [1,4,16] r887 c887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m887_1
  · exact m887_4
  · exact m887_16

def b888 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 426, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 168 17 300 332 396 268), lower := (rows 51 194 84 168 17 32 64 128 256), losses := [] }

theorem u888 : Upper (D 2) (R 2) [50,192,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b888
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b889 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 84 168 20 297 329 393 265), lower := (rows 51 194 84 168 20 32 64 128 256), losses := [] }

theorem u889 : Upper (D 2) (R 2) [50,192,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b889
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b890 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 84 168 24 293 325 389 261), lower := (rows 51 194 84 168 24 32 64 128 256), losses := [] }

theorem u890 : Upper (D 2) (R 2) [50,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b890
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m891_1 : Upper (D 2) (R 2) [50,192,80,160,256,1] 13 :=
  permutation_upper _ _ _ [50,192,80,160,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u333

theorem m891_4 : Upper (D 2) (R 2) [50,192,80,160,256,4] 13 :=
  permutation_upper _ _ _ [50,192,80,160,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u335

theorem m891_8 : Upper (D 2) (R 2) [50,192,80,160,256,8] 13 :=
  permutation_upper _ _ _ [50,192,80,160,4,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u334

def r891 : Route 9 := (fun mask => (mask,id))

def c891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u891 : Upper (D 2) (R 2) [50,192,80,160,256] 13 := by
  apply FastRouting.sound _ _ [50,192,80,160,256] 13 (by decide) (choices 1) [1,4,8,256] r891 c891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m891_1
  · exact m891_4
  · exact m891_8
  · exact u336

def b892 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 84 265 20 424 488 424 424), lower := (rows 51 194 84 265 20 32 64 128 256), losses := [] }

theorem u892 : Upper (D 2) (R 2) [50,192,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b892
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b893 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 265 24 420 484 420 420), lower := (rows 51 194 84 265 24 32 64 128 256), losses := [] }

theorem u893 : Upper (D 2) (R 2) [50,192,80,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b893
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b894 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 84 265 48 428 460 396 396), lower := (rows 51 194 84 265 48 32 64 128 256), losses := [] }

theorem u894 : Upper (D 2) (R 2) [50,192,80,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b894
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b895 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 51 194 84 265 144 300 364 428 300), lower := (rows 51 194 84 265 144 32 64 128 256), losses := [] }

theorem u895 : Upper (D 2) (R 2) [50,192,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b895
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r896 : Route 9 := (fun mask => (mask,id))

def c896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u896 : Upper (D 2) (R 2) [50,192,80,257,256] 13 := by
  apply FastRouting.sound _ _ [50,192,80,257,256] 13 (by decide) (choices 1) [4,8,128] r896 c896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u337
  · exact u338
  · exact u339

def b897 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 426, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 268 17 424 488 424 424), lower := (rows 51 194 84 268 17 32 64 128 256), losses := [] }

theorem u897 : Upper (D 2) (R 2) [50,192,80,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b897
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b898 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 84 268 24 417 481 417 417), lower := (rows 51 194 84 268 24 32 64 128 256), losses := [] }

theorem u898 : Upper (D 2) (R 2) [50,192,80,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b898
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b899 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 51 194 84 268 48 425 457 393 393), lower := (rows 51 194 84 268 48 32 64 128 256), losses := [] }

theorem u899 : Upper (D 2) (R 2) [50,192,80,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b899
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u899
end Delivery.IrregularNine14.P02
