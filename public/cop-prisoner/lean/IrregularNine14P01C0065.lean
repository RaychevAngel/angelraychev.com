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

def b3900 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 392 48 227 195 195 451), lower := (rows 113 22 14 392 48 32 64 128 256), losses := [] }

theorem u3900 : Upper (D 1) (R 1) [112,20,10,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3900
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3901 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 392 144 99 99 227 355), lower := (rows 113 22 14 392 144 32 64 128 256), losses := [] }

theorem u3901 : Upper (D 1) (R 1) [112,20,10,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3902 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 113 22 44 138 17 482 450 450 450), lower := (rows 113 22 44 138 17 32 64 128 256), losses := [] }

theorem u3902 : Upper (D 1) (R 1) [112,20,40,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3902
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3903 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 138 18 481 449 449 449), lower := (rows 113 22 44 138 18 32 64 128 256), losses := [] }

theorem u3903 : Upper (D 1) (R 1) [112,20,40,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3904 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 138 80 419 451 387 387), lower := (rows 113 22 44 138 80 32 64 128 256), losses := [] }

theorem u3904 : Upper (D 1) (R 1) [112,20,40,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3904
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3905 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 44 138 144 355 323 451 323), lower := (rows 113 22 44 138 144 32 64 128 256), losses := [] }

theorem u3905 : Upper (D 1) (R 1) [112,20,40,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3905
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3906 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 44 138 272 227 195 195 451), lower := (rows 113 22 44 138 272 32 64 128 256), losses := [] }

theorem u3906 : Upper (D 1) (R 1) [112,20,40,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3906
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3907 : PairBound 9 := { available := 386, camps := [], pairs := [], upper := (rows 113 22 44 200 17 418 450 386 386), lower := (rows 113 22 44 200 17 32 64 128 256), losses := [] }

theorem u3907 : Upper (D 1) (R 1) [112,20,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3907
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3908 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 200 18 419 451 387 387), lower := (rows 113 22 44 200 18 32 64 128 256), losses := [] }

theorem u3908 : Upper (D 1) (R 1) [112,20,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3908
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3909 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 44 200 144 291 323 387 259), lower := (rows 113 22 44 200 144 32 64 128 256), losses := [] }

theorem u3909 : Upper (D 1) (R 1) [112,20,40,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3909
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3910 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 44 200 272 163 195 131 387), lower := (rows 113 22 44 200 272 32 64 128 256), losses := [] }

theorem u3910 : Upper (D 1) (R 1) [112,20,40,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3910
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3911 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 44 266 17 226 194 194 450), lower := (rows 113 22 44 266 17 32 64 128 256), losses := [] }

theorem u3911 : Upper (D 1) (R 1) [112,20,40,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3911
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3912 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 266 18 225 193 193 449), lower := (rows 113 22 44 266 18 32 64 128 256), losses := [] }

theorem u3912 : Upper (D 1) (R 1) [112,20,40,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3912
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3913 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 266 80 163 195 131 387), lower := (rows 113 22 44 266 80 32 64 128 256), losses := [] }

theorem u3913 : Upper (D 1) (R 1) [112,20,40,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3913
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3914 : Route 9 := (fun mask => (mask,id))

def c3914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3914 : Upper (D 1) (R 1) [112,20,40,258,128] 13 := by
  apply FastRouting.sound _ _ [112,20,40,258,128] 13 (by decide) (choices 1) [1,2,64,128] r3914 c3914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1053
  · exact u1054
  · exact u1055
  · exact u1056

def b3915 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 113 22 44 328 17 162 194 130 386), lower := (rows 113 22 44 328 17 32 64 128 256), losses := [] }

theorem u3915 : Upper (D 1) (R 1) [112,20,40,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3915
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3916 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 328 18 163 195 131 387), lower := (rows 113 22 44 328 18 32 64 128 256), losses := [] }

theorem u3916 : Upper (D 1) (R 1) [112,20,40,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3916
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3917 : Route 9 := (fun mask => (mask,id))

def c3917 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3917 : Upper (D 1) (R 1) [112,20,40,320,128] 13 := by
  apply FastRouting.sound _ _ [112,20,40,320,128] 13 (by decide) (choices 1) [1,2,128] r3917 c3917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1057
  · exact u1058
  · exact u1059

def b3918 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 44 392 17 226 194 194 450), lower := (rows 113 22 44 392 17 32 64 128 256), losses := [] }

theorem u3918 : Upper (D 1) (R 1) [112,20,40,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3918
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3919 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 392 18 227 195 195 451), lower := (rows 113 22 44 392 18 32 64 128 256), losses := [] }

theorem u3919 : Upper (D 1) (R 1) [112,20,40,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3919
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3920 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 392 80 163 195 131 387), lower := (rows 113 22 44 392 80 32 64 128 256), losses := [] }

theorem u3920 : Upper (D 1) (R 1) [112,20,40,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3920
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3921 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 44 392 144 99 67 195 323), lower := (rows 113 22 44 392 144 32 64 128 256), losses := [] }

theorem u3921 : Upper (D 1) (R 1) [112,20,40,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3921
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3922 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 137 18 360 360 488 360), lower := (rows 113 22 134 137 18 32 64 128 256), losses := [] }

theorem u3922 : Upper (D 1) (R 1) [112,20,130,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3922
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3923 : PairBound 9 := { available := 354, camps := [], pairs := [], upper := (rows 113 22 134 137 24 354 354 482 354), lower := (rows 113 22 134 137 24 32 64 128 256), losses := [] }

theorem u3923 : Upper (D 1) (R 1) [112,20,130,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3923
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3924 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 137 48 362 330 458 330), lower := (rows 113 22 134 137 48 32 64 128 256), losses := [] }

theorem u3924 : Upper (D 1) (R 1) [112,20,130,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3924
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3925 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 22 134 137 272 106 106 234 362), lower := (rows 113 22 134 137 272 32 64 128 256), losses := [] }

theorem u3925 : Upper (D 1) (R 1) [112,20,130,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3925
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3926 : PairBound 9 := { available := 330, camps := [], pairs := [], upper := (rows 113 22 134 168 17 362 330 458 330), lower := (rows 113 22 134 168 17 32 64 128 256), losses := [] }

theorem u3926 : Upper (D 1) (R 1) [112,20,130,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3926
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3927 : PairBound 9 := { available := 329, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 168 18 361 329 457 329), lower := (rows 113 22 134 168 18 32 64 128 256), losses := [] }

theorem u3927 : Upper (D 1) (R 1) [112,20,130,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3927
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3928 : PairBound 9 := { available := 323, camps := [], pairs := [], upper := (rows 113 22 134 168 24 355 323 451 323), lower := (rows 113 22 134 168 24 32 64 128 256), losses := [] }

theorem u3928 : Upper (D 1) (R 1) [112,20,130,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3928
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3929 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 134 168 80 299 331 395 267), lower := (rows 113 22 134 168 80 32 64 128 256), losses := [] }

theorem u3929 : Upper (D 1) (R 1) [112,20,130,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3929
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3930 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 22 134 168 272 107 75 203 331), lower := (rows 113 22 134 168 272 32 64 128 256), losses := [] }

theorem u3930 : Upper (D 1) (R 1) [112,20,130,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3930
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3931 : PairBound 9 := { available := 232, camps := [{ cop := 7, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 265 18 232 232 232 488), lower := (rows 113 22 134 265 18 32 64 128 256), losses := [] }

theorem u3931 : Upper (D 1) (R 1) [112,20,130,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3931
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3932 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 22 134 265 24 226 226 226 482), lower := (rows 113 22 134 265 24 32 64 128 256), losses := [] }

theorem u3932 : Upper (D 1) (R 1) [112,20,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3932
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3933 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 265 48 234 202 202 458), lower := (rows 113 22 134 265 48 32 64 128 256), losses := [] }

theorem u3933 : Upper (D 1) (R 1) [112,20,130,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3933
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3934 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 265 144 106 106 234 362), lower := (rows 113 22 134 265 144 32 64 128 256), losses := [] }

theorem u3934 : Upper (D 1) (R 1) [112,20,130,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3934
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3935 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 22 134 296 17 234 202 202 458), lower := (rows 113 22 134 296 17 32 64 128 256), losses := [] }

theorem u3935 : Upper (D 1) (R 1) [112,20,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3935
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3936 : PairBound 9 := { available := 201, camps := [{ cop := 7, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 296 18 233 201 201 457), lower := (rows 113 22 134 296 18 32 64 128 256), losses := [] }

theorem u3936 : Upper (D 1) (R 1) [112,20,130,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3936
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3937 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 134 296 24 227 195 195 451), lower := (rows 113 22 134 296 24 32 64 128 256), losses := [] }

theorem u3937 : Upper (D 1) (R 1) [112,20,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3937
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3938 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 134 296 80 171 203 139 395), lower := (rows 113 22 134 296 80 32 64 128 256), losses := [] }

theorem u3938 : Upper (D 1) (R 1) [112,20,130,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3938
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3939 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 296 144 107 75 203 331), lower := (rows 113 22 134 296 144 32 64 128 256), losses := [] }

theorem u3939 : Upper (D 1) (R 1) [112,20,130,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3939
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3940 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 22 134 392 17 106 106 234 362), lower := (rows 113 22 134 392 17 32 64 128 256), losses := [] }

theorem u3940 : Upper (D 1) (R 1) [112,20,130,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3940
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3941 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 392 18 105 105 233 361), lower := (rows 113 22 134 392 18 32 64 128 256), losses := [] }

theorem u3941 : Upper (D 1) (R 1) [112,20,130,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3941
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3942 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 22 134 392 24 99 99 227 355), lower := (rows 113 22 134 392 24 32 64 128 256), losses := [] }

theorem u3942 : Upper (D 1) (R 1) [112,20,130,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3942
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3943 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 392 48 107 75 203 331), lower := (rows 113 22 134 392 48 32 64 128 256), losses := [] }

theorem u3943 : Upper (D 1) (R 1) [112,20,130,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3943
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3944 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 113 22 140 42 17 482 450 450 450), lower := (rows 113 22 140 42 17 32 64 128 256), losses := [] }

theorem u3944 : Upper (D 1) (R 1) [112,20,136,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3944
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3945 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 42 18 481 449 449 449), lower := (rows 113 22 140 42 18 32 64 128 256), losses := [] }

theorem u3945 : Upper (D 1) (R 1) [112,20,136,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3945
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3946 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 140 42 80 419 451 387 387), lower := (rows 113 22 140 42 80 32 64 128 256), losses := [] }

theorem u3946 : Upper (D 1) (R 1) [112,20,136,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3946
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3947 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 140 42 144 355 323 451 323), lower := (rows 113 22 140 42 144 32 64 128 256), losses := [] }

theorem u3947 : Upper (D 1) (R 1) [112,20,136,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3947
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3948 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 140 42 272 227 195 195 451), lower := (rows 113 22 140 42 272 32 64 128 256), losses := [] }

theorem u3948 : Upper (D 1) (R 1) [112,20,136,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3948
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3949 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 265 18 226 226 226 482), lower := (rows 113 22 140 265 18 32 64 128 256), losses := [] }

theorem u3949 : Upper (D 1) (R 1) [112,20,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3949
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3950 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 265 48 226 194 194 450), lower := (rows 113 22 140 265 48 32 64 128 256), losses := [] }

theorem u3950 : Upper (D 1) (R 1) [112,20,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3950
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3951 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 140 265 144 98 98 226 354), lower := (rows 113 22 140 265 144 32 64 128 256), losses := [] }

theorem u3951 : Upper (D 1) (R 1) [112,20,136,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3951
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3952 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 22 140 266 17 226 226 226 482), lower := (rows 113 22 140 266 17 32 64 128 256), losses := [] }

theorem u3952 : Upper (D 1) (R 1) [112,20,136,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3953 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 266 18 225 225 225 481), lower := (rows 113 22 140 266 18 32 64 128 256), losses := [] }

theorem u3953 : Upper (D 1) (R 1) [112,20,136,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3953
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3954 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 266 48 227 195 195 451), lower := (rows 113 22 140 266 48 32 64 128 256), losses := [] }

theorem u3954 : Upper (D 1) (R 1) [112,20,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3954
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3955 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 140 266 144 99 99 227 355), lower := (rows 113 22 140 266 144 32 64 128 256), losses := [] }

theorem u3955 : Upper (D 1) (R 1) [112,20,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3955
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3956 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 140 296 17 226 194 194 450), lower := (rows 113 22 140 296 17 32 64 128 256), losses := [] }

theorem u3956 : Upper (D 1) (R 1) [112,20,136,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3956
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3957 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 296 18 227 195 195 451), lower := (rows 113 22 140 296 18 32 64 128 256), losses := [] }

theorem u3957 : Upper (D 1) (R 1) [112,20,136,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3957
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3958 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 140 296 80 163 195 131 387), lower := (rows 113 22 140 296 80 32 64 128 256), losses := [] }

theorem u3958 : Upper (D 1) (R 1) [112,20,136,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3959 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 140 296 144 99 67 195 323), lower := (rows 113 22 140 296 144 32 64 128 256), losses := [] }

theorem u3959 : Upper (D 1) (R 1) [112,20,136,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3959
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3959
end Delivery.IrregularNine14.P01
