import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0017

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3840 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 137 144 354 354 482 354), lower := (rows 113 14 22 137 144 32 64 128 256), losses := [] }

theorem u3840 : Upper (D 1) (R 1) [112,12,18,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3840
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3841 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 14 22 137 272 226 226 226 482), lower := (rows 113 14 22 137 272 32 64 128 256), losses := [] }

theorem u3841 : Upper (D 1) (R 1) [112,12,18,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3841
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3842 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 113 14 22 168 17 482 450 450 450), lower := (rows 113 14 22 168 17 32 64 128 256), losses := [] }

theorem u3842 : Upper (D 1) (R 1) [112,12,18,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3842
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3843 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 168 18 481 449 449 449), lower := (rows 113 14 22 168 18 32 64 128 256), losses := [] }

theorem u3843 : Upper (D 1) (R 1) [112,12,18,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3843
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3844 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 22 168 80 419 451 387 387), lower := (rows 113 14 22 168 80 32 64 128 256), losses := [] }

theorem u3844 : Upper (D 1) (R 1) [112,12,18,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3844
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3845 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 168 144 355 323 451 323), lower := (rows 113 14 22 168 144 32 64 128 256), losses := [] }

theorem u3845 : Upper (D 1) (R 1) [112,12,18,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3845
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3846 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 14 22 168 272 227 195 195 451), lower := (rows 113 14 22 168 272 32 64 128 256), losses := [] }

theorem u3846 : Upper (D 1) (R 1) [112,12,18,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3846
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3847 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 265 18 224 224 224 480), lower := (rows 113 14 22 265 18 32 64 128 256), losses := [] }

theorem u3847 : Upper (D 1) (R 1) [112,12,18,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3847
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3848 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 265 48 226 194 194 450), lower := (rows 113 14 22 265 48 32 64 128 256), losses := [] }

theorem u3848 : Upper (D 1) (R 1) [112,12,18,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3848
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3849 : Route 9 := (fun mask => (mask,id))

def c3849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3849 : Upper (D 1) (R 1) [112,12,18,257,128] 13 := by
  apply FastRouting.sound _ _ [112,12,18,257,128] 13 (by decide) (choices 1) [2,64,128] r3849 c3849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1024
  · exact u1025
  · exact u1026

def b3850 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 14 22 296 17 226 194 194 450), lower := (rows 113 14 22 296 17 32 64 128 256), losses := [] }

theorem u3850 : Upper (D 1) (R 1) [112,12,18,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3850
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3851 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 296 18 225 193 193 449), lower := (rows 113 14 22 296 18 32 64 128 256), losses := [] }

theorem u3851 : Upper (D 1) (R 1) [112,12,18,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3851
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3852 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 22 296 80 163 195 131 387), lower := (rows 113 14 22 296 80 32 64 128 256), losses := [] }

theorem u3852 : Upper (D 1) (R 1) [112,12,18,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3852
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3853 : Route 9 := (fun mask => (mask,id))

def c3853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3853 : Upper (D 1) (R 1) [112,12,18,288,128] 13 := by
  apply FastRouting.sound _ _ [112,12,18,288,128] 13 (by decide) (choices 1) [1,2,64,128] r3853 c3853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1027
  · exact u1028
  · exact u1029
  · exact u1030

def b3854 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 14 22 392 17 226 226 226 482), lower := (rows 113 14 22 392 17 32 64 128 256), losses := [] }

theorem u3854 : Upper (D 1) (R 1) [112,12,18,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3854
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3855 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 392 18 225 225 225 481), lower := (rows 113 14 22 392 18 32 64 128 256), losses := [] }

theorem u3855 : Upper (D 1) (R 1) [112,12,18,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3855
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3856 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 392 48 227 195 195 451), lower := (rows 113 14 22 392 48 32 64 128 256), losses := [] }

theorem u3856 : Upper (D 1) (R 1) [112,12,18,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3856
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3857 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 392 144 99 99 227 355), lower := (rows 113 14 22 392 144 32 64 128 256), losses := [] }

theorem u3857 : Upper (D 1) (R 1) [112,12,18,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3857
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3858 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 133 266 18 240 240 240 496), lower := (rows 113 14 133 266 18 32 64 128 256), losses := [] }

theorem u3858 : Upper (D 1) (R 1) [112,12,129,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3858
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3859 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 266 48 242 210 210 466), lower := (rows 113 14 133 266 48 32 64 128 256), losses := [] }

theorem u3859 : Upper (D 1) (R 1) [112,12,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3859
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3860_2 : Upper (D 1) (R 1) [112,12,129,258,128,2] 13 :=
  permutation_upper _ _ _ [112,12,129,258,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1031

theorem m3860_16 : Upper (D 1) (R 1) [112,12,129,258,128,16] 13 :=
  permutation_upper _ _ _ [112,12,129,258,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1032

theorem m3860_64 : Upper (D 1) (R 1) [112,12,129,258,128,64] 13 :=
  permutation_upper _ _ _ [112,12,129,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1033

def r3860 : Route 9 := (fun mask => (mask,id))

def c3860 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3860 : Upper (D 1) (R 1) [112,12,129,258,128] 13 := by
  apply FastRouting.sound _ _ [112,12,129,258,128] 13 (by decide) (choices 1) [2,16,64] r3860 c3860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3860_2
  · exact m3860_16
  · exact m3860_64

def b3861 : PairBound 9 := { available := 226, camps := [], pairs := [(2,4)], upper := (rows 113 14 133 280 18 226 226 226 482), lower := (rows 113 14 133 280 18 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 8 0 50 82 146 274), good := (rows 485 494 133 488 482 32 64 128 256) }] }

theorem u3861 : Upper (D 1) (R 1) [112,12,129,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3861
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3862 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 280 48 226 194 194 450), lower := (rows 113 14 133 280 48 32 64 128 256), losses := [] }

theorem u3862 : Upper (D 1) (R 1) [112,12,129,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3862
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3863 : Route 9 := (fun mask => (mask,id))

def c3863 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3863 : Upper (D 1) (R 1) [112,12,129,272,128] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272,128] 13 (by decide) (choices 1) [2,64] r3863 c3863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1034
  · exact u1035

def b3864 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 134 265 18 240 240 240 496), lower := (rows 113 14 134 265 18 32 64 128 256), losses := [] }

theorem u3864 : Upper (D 1) (R 1) [112,12,130,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3864
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3865 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 134 265 48 242 210 210 466), lower := (rows 113 14 134 265 48 32 64 128 256), losses := [] }

theorem u3865 : Upper (D 1) (R 1) [112,12,130,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3865
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3866_2 : Upper (D 1) (R 1) [112,12,130,257,128,2] 13 :=
  permutation_upper _ _ _ [112,12,130,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1036

theorem m3866_16 : Upper (D 1) (R 1) [112,12,130,257,128,16] 13 :=
  permutation_upper _ _ _ [112,12,130,257,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1037

theorem m3866_64 : Upper (D 1) (R 1) [112,12,130,257,128,64] 13 :=
  permutation_upper _ _ _ [112,12,130,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1038

def r3866 : Route 9 := (fun mask => (mask,id))

def c3866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3866 : Upper (D 1) (R 1) [112,12,130,257,128] 13 := by
  apply FastRouting.sound _ _ [112,12,130,257,128] 13 (by decide) (choices 1) [2,16,64] r3866 c3866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3866_2
  · exact m3866_16
  · exact m3866_64

def b3867 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 14 134 280 17 226 226 226 482), lower := (rows 113 14 134 280 17 32 64 128 256), losses := [] }

theorem u3867 : Upper (D 1) (R 1) [112,12,130,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3867
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3868 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 134 280 18 225 225 225 481), lower := (rows 113 14 134 280 18 32 64 128 256), losses := [] }

theorem u3868 : Upper (D 1) (R 1) [112,12,130,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3868
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3869 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 134 280 48 227 195 195 451), lower := (rows 113 14 134 280 48 32 64 128 256), losses := [] }

theorem u3869 : Upper (D 1) (R 1) [112,12,130,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3869
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3870 : Route 9 := (fun mask => (mask,id))

def c3870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3870 : Upper (D 1) (R 1) [112,12,130,272,128] 13 := by
  apply FastRouting.sound _ _ [112,12,130,272,128] 13 (by decide) (choices 1) [1,2,64] r3870 c3870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1039
  · exact u1040
  · exact u1041

def b3871 : PairBound 9 := { available := 226, camps := [], pairs := [(3,4)], upper := (rows 113 14 148 265 18 226 226 226 482), lower := (rows 113 14 148 265 18 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 9 0 50 82 146 274), good := (rows 489 494 484 265 482 32 64 128 256) }] }

theorem u3871 : Upper (D 1) (R 1) [112,12,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3871
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3872 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 148 265 48 226 194 194 450), lower := (rows 113 14 148 265 48 32 64 128 256), losses := [] }

theorem u3872 : Upper (D 1) (R 1) [112,12,144,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3872
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3873 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 265 144 98 98 226 354), lower := (rows 113 14 148 265 144 32 64 128 256), losses := [] }

theorem u3873 : Upper (D 1) (R 1) [112,12,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3873
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3874 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 14 148 266 17 226 226 226 482), lower := (rows 113 14 148 266 17 32 64 128 256), losses := [] }

theorem u3874 : Upper (D 1) (R 1) [112,12,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3874
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3875 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 148 266 18 225 225 225 481), lower := (rows 113 14 148 266 18 32 64 128 256), losses := [] }

theorem u3875 : Upper (D 1) (R 1) [112,12,144,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3875
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3876 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 148 266 48 227 195 195 451), lower := (rows 113 14 148 266 48 32 64 128 256), losses := [] }

theorem u3876 : Upper (D 1) (R 1) [112,12,144,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3876
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3877 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 266 144 99 99 227 355), lower := (rows 113 14 148 266 144 32 64 128 256), losses := [] }

theorem u3877 : Upper (D 1) (R 1) [112,12,144,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3877
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3878 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 14 148 296 17 226 194 194 450), lower := (rows 113 14 148 296 17 32 64 128 256), losses := [] }

theorem u3878 : Upper (D 1) (R 1) [112,12,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3878
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3879 : Route 9 := (fun mask => (mask,id))

def c3879 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3879 : Upper (D 1) (R 1) [112,12,144,288,2] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288,2] 13 (by decide) (choices 1) [1,2,64,128] r3879 c3879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1042
  · exact u1043
  · exact u1044
  · exact u1045

def b3880 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 148 296 80 163 195 131 387), lower := (rows 113 14 148 296 80 32 64 128 256), losses := [] }

theorem u3880 : Upper (D 1) (R 1) [112,12,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3880
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3881 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 296 144 99 67 195 323), lower := (rows 113 14 148 296 144 32 64 128 256), losses := [] }

theorem u3881 : Upper (D 1) (R 1) [112,12,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3881
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3882 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 137 18 480 480 480 480), lower := (rows 113 22 14 137 18 32 64 128 256), losses := [] }

theorem u3882 : Upper (D 1) (R 1) [112,20,10,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3882
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3883 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 137 48 482 450 450 450), lower := (rows 113 22 14 137 48 32 64 128 256), losses := [] }

theorem u3883 : Upper (D 1) (R 1) [112,20,10,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3883
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3884 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 137 144 354 354 482 354), lower := (rows 113 22 14 137 144 32 64 128 256), losses := [] }

theorem u3884 : Upper (D 1) (R 1) [112,20,10,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3884
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3885 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 22 14 137 272 226 226 226 482), lower := (rows 113 22 14 137 272 32 64 128 256), losses := [] }

theorem u3885 : Upper (D 1) (R 1) [112,20,10,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3885
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3886 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 113 22 14 168 17 482 450 450 450), lower := (rows 113 22 14 168 17 32 64 128 256), losses := [] }

theorem u3886 : Upper (D 1) (R 1) [112,20,10,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3886
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3887 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 168 18 481 449 449 449), lower := (rows 113 22 14 168 18 32 64 128 256), losses := [] }

theorem u3887 : Upper (D 1) (R 1) [112,20,10,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3887
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3888 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 14 168 80 419 451 387 387), lower := (rows 113 22 14 168 80 32 64 128 256), losses := [] }

theorem u3888 : Upper (D 1) (R 1) [112,20,10,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3888
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3889 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 168 144 355 323 451 323), lower := (rows 113 22 14 168 144 32 64 128 256), losses := [] }

theorem u3889 : Upper (D 1) (R 1) [112,20,10,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3889
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3890 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 14 168 272 227 195 195 451), lower := (rows 113 22 14 168 272 32 64 128 256), losses := [] }

theorem u3890 : Upper (D 1) (R 1) [112,20,10,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3890
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3891 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 265 18 224 224 224 480), lower := (rows 113 22 14 265 18 32 64 128 256), losses := [] }

theorem u3891 : Upper (D 1) (R 1) [112,20,10,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3891
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3892 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 265 48 226 194 194 450), lower := (rows 113 22 14 265 48 32 64 128 256), losses := [] }

theorem u3892 : Upper (D 1) (R 1) [112,20,10,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3892
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3893 : Route 9 := (fun mask => (mask,id))

def c3893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3893 : Upper (D 1) (R 1) [112,20,10,257,128] 13 := by
  apply FastRouting.sound _ _ [112,20,10,257,128] 13 (by decide) (choices 1) [2,64,128] r3893 c3893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1046
  · exact u1047
  · exact u1048

def b3894 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 14 296 17 226 194 194 450), lower := (rows 113 22 14 296 17 32 64 128 256), losses := [] }

theorem u3894 : Upper (D 1) (R 1) [112,20,10,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3894
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3895 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 296 18 225 193 193 449), lower := (rows 113 22 14 296 18 32 64 128 256), losses := [] }

theorem u3895 : Upper (D 1) (R 1) [112,20,10,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3895
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3896 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 14 296 80 163 195 131 387), lower := (rows 113 22 14 296 80 32 64 128 256), losses := [] }

theorem u3896 : Upper (D 1) (R 1) [112,20,10,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3896
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3897 : Route 9 := (fun mask => (mask,id))

def c3897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3897 : Upper (D 1) (R 1) [112,20,10,288,128] 13 := by
  apply FastRouting.sound _ _ [112,20,10,288,128] 13 (by decide) (choices 1) [1,2,64,128] r3897 c3897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1049
  · exact u1050
  · exact u1051
  · exact u1052

def b3898 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 22 14 392 17 226 226 226 482), lower := (rows 113 22 14 392 17 32 64 128 256), losses := [] }

theorem u3898 : Upper (D 1) (R 1) [112,20,10,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3898
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3899 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 392 18 225 225 225 481), lower := (rows 113 22 14 392 18 32 64 128 256), losses := [] }

theorem u3899 : Upper (D 1) (R 1) [112,20,10,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3899
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3899
end Delivery.IrregularNine14.P01
