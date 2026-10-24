import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0026

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3900 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 44 208 177 209 145 401), lower := (rows 35 322 13 44 208 32 64 128 256), losses := [] }

theorem u3900 : Upper (D 3) (R 3) [34,320,9,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3900
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3901 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 56 84 161 193 129 385), lower := (rows 35 322 13 56 84 32 64 128 256), losses := [] }

theorem u3901 : Upper (D 3) (R 3) [34,320,9,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3901
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3902 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 56 145 229 197 197 453), lower := (rows 35 322 13 56 145 32 64 128 256), losses := [] }

theorem u3902 : Upper (D 3) (R 3) [34,320,9,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3902
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3903 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 56 148 225 193 193 449), lower := (rows 35 322 13 56 148 32 64 128 256), losses := [] }

theorem u3903 : Upper (D 3) (R 3) [34,320,9,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3903
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3904 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 56 208 165 197 133 389), lower := (rows 35 322 13 56 208 32 64 128 256), losses := [] }

theorem u3904 : Upper (D 3) (R 3) [34,320,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3904
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3905 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 73 52 177 209 145 401), lower := (rows 35 322 13 73 52 32 64 128 256), losses := [] }

theorem u3905 : Upper (D 3) (R 3) [34,320,9,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3905
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3906 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 73 145 180 244 180 436), lower := (rows 35 322 13 73 145 32 64 128 256), losses := [] }

theorem u3906 : Upper (D 3) (R 3) [34,320,9,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3906
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3907 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 73 148 177 241 177 433), lower := (rows 35 322 13 73 148 32 64 128 256), losses := [] }

theorem u3907 : Upper (D 3) (R 3) [34,320,9,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3907
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3908 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 73 176 181 213 149 405), lower := (rows 35 322 13 73 176 32 64 128 256), losses := [] }

theorem u3908 : Upper (D 3) (R 3) [34,320,9,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3908
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3909 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 76 145 177 241 177 433), lower := (rows 35 322 13 76 145 32 64 128 256), losses := [] }

theorem u3909 : Upper (D 3) (R 3) [34,320,9,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3909
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3910 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 76 176 177 209 145 401), lower := (rows 35 322 13 76 176 32 64 128 256), losses := [] }

theorem u3910 : Upper (D 3) (R 3) [34,320,9,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3910
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3911 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 88 52 161 193 129 385), lower := (rows 35 322 13 88 52 32 64 128 256), losses := [] }

theorem u3911 : Upper (D 3) (R 3) [34,320,9,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3911
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3912 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 88 145 165 229 165 421), lower := (rows 35 322 13 88 145 32 64 128 256), losses := [] }

theorem u3912 : Upper (D 3) (R 3) [34,320,9,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3912
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3913 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 88 148 161 225 161 417), lower := (rows 35 322 13 88 148 32 64 128 256), losses := [] }

theorem u3913 : Upper (D 3) (R 3) [34,320,9,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3913
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3914 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 88 176 165 197 133 389), lower := (rows 35 322 13 88 176 32 64 128 256), losses := [] }

theorem u3914 : Upper (D 3) (R 3) [34,320,9,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3914
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3915 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 104 145 181 213 149 405), lower := (rows 35 322 13 104 145 32 64 128 256), losses := [] }

theorem u3915 : Upper (D 3) (R 3) [34,320,9,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3915
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3916 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 104 148 177 209 145 401), lower := (rows 35 322 13 104 148 32 64 128 256), losses := [] }

theorem u3916 : Upper (D 3) (R 3) [34,320,9,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3916
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3917 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 52 241 209 209 465), lower := (rows 35 322 13 137 52 32 64 128 256), losses := [] }

theorem u3917 : Upper (D 3) (R 3) [34,320,9,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3917
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3918 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 84 177 241 177 433), lower := (rows 35 322 13 137 84 32 64 128 256), losses := [] }

theorem u3918 : Upper (D 3) (R 3) [34,320,9,129,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3918
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3919 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 112 181 213 149 405), lower := (rows 35 322 13 137 112 32 64 128 256), losses := [] }

theorem u3919 : Upper (D 3) (R 3) [34,320,9,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3919
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3920 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 145 116 116 244 372), lower := (rows 35 322 13 137 145 32 64 128 256), losses := [] }

theorem u3920 : Upper (D 3) (R 3) [34,320,9,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3920
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3921 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 148 113 113 241 369), lower := (rows 35 322 13 137 148 32 64 128 256), losses := [] }

theorem u3921 : Upper (D 3) (R 3) [34,320,9,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3921
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3922 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 176 117 85 213 341), lower := (rows 35 322 13 137 176 32 64 128 256), losses := [] }

theorem u3922 : Upper (D 3) (R 3) [34,320,9,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3922
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3923 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 208 53 117 181 309), lower := (rows 35 322 13 137 208 32 64 128 256), losses := [] }

theorem u3923 : Upper (D 3) (R 3) [34,320,9,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3923
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3924 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 140 49 241 209 209 465), lower := (rows 35 322 13 140 49 32 64 128 256), losses := [] }

theorem u3924 : Upper (D 3) (R 3) [34,320,9,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3924
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3925 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 140 81 177 241 177 433), lower := (rows 35 322 13 140 81 32 64 128 256), losses := [] }

theorem u3925 : Upper (D 3) (R 3) [34,320,9,132,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3925
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3926 : Route 9 := (fun mask => (mask,id))

def c3926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3926 : Upper (D 3) (R 3) [34,320,9,132,96] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132,96] 13 (by decide) (choices 1) [1,16,128] r3926 c3926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1579
  · exact u1580
  · exact u1581

def b3927 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 140 145 113 113 241 369), lower := (rows 35 322 13 140 145 32 64 128 256), losses := [] }

theorem u3927 : Upper (D 3) (R 3) [34,320,9,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3927
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3928 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 140 176 113 81 209 337), lower := (rows 35 322 13 140 176 32 64 128 256), losses := [] }

theorem u3928 : Upper (D 3) (R 3) [34,320,9,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3928
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3929 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 140 208 49 113 177 305), lower := (rows 35 322 13 140 208 32 64 128 256), losses := [] }

theorem u3929 : Upper (D 3) (R 3) [34,320,9,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3929
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3930 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 152 49 229 197 197 453), lower := (rows 35 322 13 152 49 32 64 128 256), losses := [] }

theorem u3930 : Upper (D 3) (R 3) [34,320,9,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3930
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3931 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 152 52 225 193 193 449), lower := (rows 35 322 13 152 52 32 64 128 256), losses := [] }

theorem u3931 : Upper (D 3) (R 3) [34,320,9,144,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3931
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3932 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 152 81 165 229 165 421), lower := (rows 35 322 13 152 81 32 64 128 256), losses := [] }

theorem u3932 : Upper (D 3) (R 3) [34,320,9,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3932
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3933 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 152 84 161 225 161 417), lower := (rows 35 322 13 152 84 32 64 128 256), losses := [] }

theorem u3933 : Upper (D 3) (R 3) [34,320,9,144,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3933
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3934 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 152 112 165 197 133 389), lower := (rows 35 322 13 152 112 32 64 128 256), losses := [] }

theorem u3934 : Upper (D 3) (R 3) [34,320,9,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3934
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3935 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 152 145 101 101 229 357), lower := (rows 35 322 13 152 145 32 64 128 256), losses := [] }

theorem u3935 : Upper (D 3) (R 3) [34,320,9,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3935
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3936 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 152 148 97 97 225 353), lower := (rows 35 322 13 152 148 32 64 128 256), losses := [] }

theorem u3936 : Upper (D 3) (R 3) [34,320,9,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3936
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3937 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 152 176 101 69 197 325), lower := (rows 35 322 13 152 176 32 64 128 256), losses := [] }

theorem u3937 : Upper (D 3) (R 3) [34,320,9,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3937
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3938 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 152 208 37 101 165 293), lower := (rows 35 322 13 152 208 32 64 128 256), losses := [] }

theorem u3938 : Upper (D 3) (R 3) [34,320,9,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3938
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3939 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 168 84 177 209 145 401), lower := (rows 35 322 13 168 84 32 64 128 256), losses := [] }

theorem u3939 : Upper (D 3) (R 3) [34,320,9,160,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3939
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3940 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 168 145 117 85 213 341), lower := (rows 35 322 13 168 145 32 64 128 256), losses := [] }

theorem u3940 : Upper (D 3) (R 3) [34,320,9,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3940
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3941 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 168 148 113 81 209 337), lower := (rows 35 322 13 168 148 32 64 128 256), losses := [] }

theorem u3941 : Upper (D 3) (R 3) [34,320,9,160,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3941
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3942 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 168 208 53 85 149 277), lower := (rows 35 322 13 168 208 32 64 128 256), losses := [] }

theorem u3942 : Upper (D 3) (R 3) [34,320,9,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3942
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3943 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 200 52 177 209 145 401), lower := (rows 35 322 13 200 52 32 64 128 256), losses := [] }

theorem u3943 : Upper (D 3) (R 3) [34,320,9,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3943
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3944 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 200 145 53 117 181 309), lower := (rows 35 322 13 200 145 32 64 128 256), losses := [] }

theorem u3944 : Upper (D 3) (R 3) [34,320,9,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3944
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3945 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 200 148 49 113 177 305), lower := (rows 35 322 13 200 148 32 64 128 256), losses := [] }

theorem u3945 : Upper (D 3) (R 3) [34,320,9,192,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3945
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3946 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 200 176 53 85 149 277), lower := (rows 35 322 13 200 176 32 64 128 256), losses := [] }

theorem u3946 : Upper (D 3) (R 3) [34,320,9,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3946
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3947 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 28 41 145 229 197 197 453), lower := (rows 35 322 28 41 145 32 64 128 256), losses := [] }

theorem u3947 : Upper (D 3) (R 3) [34,320,24,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3947
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3948 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 28 41 148 225 193 193 449), lower := (rows 35 322 28 41 148 32 64 128 256), losses := [] }

theorem u3948 : Upper (D 3) (R 3) [34,320,24,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3948
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3949 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 28 41 208 165 197 133 389), lower := (rows 35 322 28 41 208 32 64 128 256), losses := [] }

theorem u3949 : Upper (D 3) (R 3) [34,320,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3949
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3950 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 28 44 145 225 193 193 449), lower := (rows 35 322 28 44 145 32 64 128 256), losses := [] }

theorem u3950 : Upper (D 3) (R 3) [34,320,24,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3950
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3951 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 28 44 208 161 193 129 385), lower := (rows 35 322 28 44 208 32 64 128 256), losses := [] }

theorem u3951 : Upper (D 3) (R 3) [34,320,24,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3951
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3952 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 73 145 165 229 165 421), lower := (rows 35 322 28 73 145 32 64 128 256), losses := [] }

theorem u3952 : Upper (D 3) (R 3) [34,320,24,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3952
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3953 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 73 148 161 225 161 417), lower := (rows 35 322 28 73 148 32 64 128 256), losses := [] }

theorem u3953 : Upper (D 3) (R 3) [34,320,24,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3953
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3954 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 73 176 165 197 133 389), lower := (rows 35 322 28 73 176 32 64 128 256), losses := [] }

theorem u3954 : Upper (D 3) (R 3) [34,320,24,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3954
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3955 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 28 76 145 161 225 161 417), lower := (rows 35 322 28 76 145 32 64 128 256), losses := [] }

theorem u3955 : Upper (D 3) (R 3) [34,320,24,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3955
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3956 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 28 76 176 161 193 129 385), lower := (rows 35 322 28 76 176 32 64 128 256), losses := [] }

theorem u3956 : Upper (D 3) (R 3) [34,320,24,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3956
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3957 : Route 9 := (fun mask => (mask,id))

def c3957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3957 : Upper (D 3) (R 3) [34,320,24,96,129] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,129] 13 (by decide) (choices 1) [1,4,128] r3957 c3957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1582
  · exact u1583
  · exact u1584

def b3958 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 28 104 148 161 193 129 385), lower := (rows 35 322 28 104 148 32 64 128 256), losses := [] }

theorem u3958 : Upper (D 3) (R 3) [34,320,24,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3958
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3959 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 28 137 145 101 101 229 357), lower := (rows 35 322 28 137 145 32 64 128 256), losses := [] }

theorem u3959 : Upper (D 3) (R 3) [34,320,24,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3959
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3959
end Delivery.IrregularNine14.P03
