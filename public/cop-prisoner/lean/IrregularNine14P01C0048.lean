import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0010

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2880 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 259 84 200 20 170 234 170 426), lower := (rows 51 259 84 200 20 32 64 128 256), losses := [] }

theorem u2880 : Upper (D 1) (R 1) [50,257,80,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2880
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2881 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 259 84 200 24 166 230 166 422), lower := (rows 51 259 84 200 24 32 64 128 256), losses := [] }

theorem u2881 : Upper (D 1) (R 1) [50,257,80,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2881
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2882 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 259 84 200 48 174 206 142 398), lower := (rows 51 259 84 200 48 32 64 128 256), losses := [] }

theorem u2882 : Upper (D 1) (R 1) [50,257,80,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2882
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2883 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 84 200 144 46 110 174 302), lower := (rows 51 259 84 200 144 32 64 128 256), losses := [] }

theorem u2883 : Upper (D 1) (R 1) [50,257,80,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2883
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2884 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 13 74 48 240 208 208 464), lower := (rows 51 262 13 74 48 32 64 128 256), losses := [] }

theorem u2884 : Upper (D 1) (R 1) [50,260,9,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2884
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2885 : PairBound 9 := { available := 176, camps := [], pairs := [(1,6)], upper := (rows 51 262 13 74 80 176 240 176 432), lower := (rows 51 262 13 74 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 49 0 145 273), good := (rows 435 262 431 10 432 32 0 128 256) }] }

theorem u2885 : Upper (D 1) (R 1) [50,260,9,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2885
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2886_16 : Upper (D 1) (R 1) [50,260,9,66,128,16] 13 :=
  permutation_upper _ _ _ [50,260,9,66,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u630

theorem m2886_64 : Upper (D 1) (R 1) [50,260,9,66,128,64] 13 :=
  permutation_upper _ _ _ [50,260,9,66,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u631

def r2886 : Route 9 := (fun mask => (mask,id))

def c2886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2886 : Upper (D 1) (R 1) [50,260,9,66,128] 13 := by
  apply FastRouting.sound _ _ [50,260,9,66,128] 13 (by decide) (choices 1) [16,64,128] r2886 c2886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2886_16
  · exact m2886_64
  · exact u632

def b2887 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 13 200 18 240 240 240 496), lower := (rows 51 262 13 200 18 32 64 128 256), losses := [] }

theorem u2887 : Upper (D 1) (R 1) [50,260,9,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2887
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2888 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 13 200 48 242 210 210 466), lower := (rows 51 262 13 200 48 32 64 128 256), losses := [] }

theorem u2888 : Upper (D 1) (R 1) [50,260,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2888
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2889 : PairBound 9 := { available := 178, camps := [], pairs := [(1,6)], upper := (rows 51 262 13 200 80 178 242 178 434), lower := (rows 51 262 13 200 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 33 0 129 257), good := (rows 435 262 431 136 16 32 0 128 256) }] }

theorem u2889 : Upper (D 1) (R 1) [50,260,9,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2889
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2890 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 69 88 18 168 232 168 424), lower := (rows 51 262 69 88 18 32 64 128 256), losses := [] }

theorem u2890 : Upper (D 1) (R 1) [50,260,65,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2890
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2891 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 262 69 88 24 162 226 162 418), lower := (rows 51 262 69 88 24 32 64 128 256), losses := [] }

theorem u2891 : Upper (D 1) (R 1) [50,260,65,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2891
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2892 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 88 48 170 202 138 394), lower := (rows 51 262 69 88 48 32 64 128 256), losses := [] }

theorem u2892 : Upper (D 1) (R 1) [50,260,65,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2892
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2893 : Route 9 := (fun mask => (mask,id))

def c2893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2893 : Upper (D 1) (R 1) [50,260,65,80,128] 13 := by
  apply FastRouting.sound _ _ [50,260,65,80,128] 13 (by decide) (choices 1) [2,8,128] r2893 c2893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u633
  · exact u634
  · exact u635

def b2894 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 262 69 138 24 240 240 240 496), lower := (rows 51 262 69 138 24 32 64 128 256), losses := [] }

theorem u2894 : Upper (D 1) (R 1) [50,260,65,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2894
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2895 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 138 48 248 216 216 472), lower := (rows 51 262 69 138 48 32 64 128 256), losses := [] }

theorem u2895 : Upper (D 1) (R 1) [50,260,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2895
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2896 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 69 138 80 184 248 184 440), lower := (rows 51 262 69 138 80 32 64 128 256), losses := [] }

theorem u2896 : Upper (D 1) (R 1) [50,260,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2896
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2897_8 : Upper (D 1) (R 1) [50,260,65,130,128,8] 13 :=
  permutation_upper _ _ _ [50,260,65,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u636

theorem m2897_16 : Upper (D 1) (R 1) [50,260,65,130,128,16] 13 :=
  permutation_upper _ _ _ [50,260,65,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u637

theorem m2897_64 : Upper (D 1) (R 1) [50,260,65,130,128,64] 13 :=
  permutation_upper _ _ _ [50,260,65,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u638

def r2897 : Route 9 := (fun mask => (mask,id))

def c2897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2897 : Upper (D 1) (R 1) [50,260,65,130,128] 13 := by
  apply FastRouting.sound _ _ [50,260,65,130,128] 13 (by decide) (choices 1) [8,16,64] r2897 c2897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2897_8
  · exact m2897_16
  · exact m2897_64

def b2898 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 69 152 18 232 232 232 488), lower := (rows 51 262 69 152 18 32 64 128 256), losses := [] }

theorem u2898 : Upper (D 1) (R 1) [50,260,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2898
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2899 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 262 69 152 24 226 226 226 482), lower := (rows 51 262 69 152 24 32 64 128 256), losses := [] }

theorem u2899 : Upper (D 1) (R 1) [50,260,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2899
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2900 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 152 48 234 202 202 458), lower := (rows 51 262 69 152 48 32 64 128 256), losses := [] }

theorem u2900 : Upper (D 1) (R 1) [50,260,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2900
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2901 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 69 152 80 170 234 170 426), lower := (rows 51 262 69 152 80 32 64 128 256), losses := [] }

theorem u2901 : Upper (D 1) (R 1) [50,260,65,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2902 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 262 69 152 144 106 106 234 362), lower := (rows 51 262 69 152 144 32 64 128 256), losses := [] }

theorem u2902 : Upper (D 1) (R 1) [50,260,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2902
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2903 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 69 200 18 184 248 184 440), lower := (rows 51 262 69 200 18 32 64 128 256), losses := [] }

theorem u2903 : Upper (D 1) (R 1) [50,260,65,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2904 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 262 69 200 24 178 242 178 434), lower := (rows 51 262 69 200 24 32 64 128 256), losses := [] }

theorem u2904 : Upper (D 1) (R 1) [50,260,65,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2904
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2905 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 200 48 186 218 154 410), lower := (rows 51 262 69 200 48 32 64 128 256), losses := [] }

theorem u2905 : Upper (D 1) (R 1) [50,260,65,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2905
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2906_2 : Upper (D 1) (R 1) [50,260,65,192,128,2] 13 :=
  permutation_upper _ _ _ [50,260,65,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u639

theorem m2906_8 : Upper (D 1) (R 1) [50,260,65,192,128,8] 13 :=
  permutation_upper _ _ _ [50,260,65,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u640

theorem m2906_16 : Upper (D 1) (R 1) [50,260,65,192,128,16] 13 :=
  permutation_upper _ _ _ [50,260,65,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u641

def r2906 : Route 9 := (fun mask => (mask,id))

def c2906 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2906 : Upper (D 1) (R 1) [50,260,65,192,128] 13 := by
  apply FastRouting.sound _ _ [50,260,65,192,128] 13 (by decide) (choices 1) [2,8,16] r2906 c2906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2906_2
  · exact m2906_8
  · exact m2906_16

def b2907 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 76 137 18 240 240 240 496), lower := (rows 51 262 76 137 18 32 64 128 256), losses := [] }

theorem u2907 : Upper (D 1) (R 1) [50,260,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2907
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2908 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 76 137 48 242 210 210 466), lower := (rows 51 262 76 137 48 32 64 128 256), losses := [] }

theorem u2908 : Upper (D 1) (R 1) [50,260,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2908
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2909 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 76 137 80 178 242 178 434), lower := (rows 51 262 76 137 80 32 64 128 256), losses := [] }

theorem u2909 : Upper (D 1) (R 1) [50,260,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2909
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2910 : PairBound 9 := { available := 114, camps := [], pairs := [(1,7)], upper := (rows 51 262 76 137 144 114 114 242 370), lower := (rows 51 262 76 137 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 33 65 0 257), good := (rows 371 262 78 367 16 32 64 0 256) }] }

theorem u2910 : Upper (D 1) (R 1) [50,260,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2910
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2911 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 262 76 138 17 240 240 240 496), lower := (rows 51 262 76 138 17 32 64 128 256), losses := [] }

theorem u2911 : Upper (D 1) (R 1) [50,260,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2911
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2912 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 76 138 48 241 209 209 465), lower := (rows 51 262 76 138 48 32 64 128 256), losses := [] }

theorem u2912 : Upper (D 1) (R 1) [50,260,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2912
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2913 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 76 138 80 177 241 177 433), lower := (rows 51 262 76 138 80 32 64 128 256), losses := [] }

theorem u2913 : Upper (D 1) (R 1) [50,260,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2913
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2914_1 : Upper (D 1) (R 1) [50,260,72,130,128,1] 13 :=
  permutation_upper _ _ _ [50,260,72,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u642

theorem m2914_16 : Upper (D 1) (R 1) [50,260,72,130,128,16] 13 :=
  permutation_upper _ _ _ [50,260,72,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u643

theorem m2914_64 : Upper (D 1) (R 1) [50,260,72,130,128,64] 13 :=
  permutation_upper _ _ _ [50,260,72,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u644

def r2914 : Route 9 := (fun mask => (mask,id))

def c2914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2914 : Upper (D 1) (R 1) [50,260,72,130,128] 13 := by
  apply FastRouting.sound _ _ [50,260,72,130,128] 13 (by decide) (choices 1) [1,16,64] r2914 c2914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2914_1
  · exact m2914_16
  · exact m2914_64

def b2915 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 262 76 152 17 226 226 226 482), lower := (rows 51 262 76 152 17 32 64 128 256), losses := [] }

theorem u2915 : Upper (D 1) (R 1) [50,260,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2915
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2916 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 76 152 18 225 225 225 481), lower := (rows 51 262 76 152 18 32 64 128 256), losses := [] }

theorem u2916 : Upper (D 1) (R 1) [50,260,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2916
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2917 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 76 152 48 227 195 195 451), lower := (rows 51 262 76 152 48 32 64 128 256), losses := [] }

theorem u2917 : Upper (D 1) (R 1) [50,260,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2917
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2918 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 76 152 80 163 227 163 419), lower := (rows 51 262 76 152 80 32 64 128 256), losses := [] }

theorem u2918 : Upper (D 1) (R 1) [50,260,72,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2918
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2919 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 262 76 152 144 99 99 227 355), lower := (rows 51 262 76 152 144 32 64 128 256), losses := [] }

theorem u2919 : Upper (D 1) (R 1) [50,260,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2919
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2920 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 196 73 18 184 248 184 440), lower := (rows 51 262 196 73 18 32 64 128 256), losses := [] }

theorem u2920 : Upper (D 1) (R 1) [50,260,192,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2920
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2921 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 262 196 73 24 178 242 178 434), lower := (rows 51 262 196 73 24 32 64 128 256), losses := [] }

theorem u2921 : Upper (D 1) (R 1) [50,260,192,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2921
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2922 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 196 73 48 186 218 154 410), lower := (rows 51 262 196 73 48 32 64 128 256), losses := [] }

theorem u2922 : Upper (D 1) (R 1) [50,260,192,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2922
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2923 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 51 262 196 73 144 58 122 186 314), lower := (rows 51 262 196 73 144 32 64 128 256), losses := [] }

theorem u2923 : Upper (D 1) (R 1) [50,260,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2923
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2924 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 262 196 88 17 170 234 170 426), lower := (rows 51 262 196 88 17 32 64 128 256), losses := [] }

theorem u2924 : Upper (D 1) (R 1) [50,260,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2924
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2925 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 196 88 18 169 233 169 425), lower := (rows 51 262 196 88 18 32 64 128 256), losses := [] }

theorem u2925 : Upper (D 1) (R 1) [50,260,192,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2925
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2926 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 51 262 196 88 24 163 227 163 419), lower := (rows 51 262 196 88 24 32 64 128 256), losses := [] }

theorem u2926 : Upper (D 1) (R 1) [50,260,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2926
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2927 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 196 88 48 171 203 139 395), lower := (rows 51 262 196 88 48 32 64 128 256), losses := [] }

theorem u2927 : Upper (D 1) (R 1) [50,260,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2927
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2928 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 196 88 144 43 107 171 299), lower := (rows 51 262 196 88 144 32 64 128 256), losses := [] }

theorem u2928 : Upper (D 1) (R 1) [50,260,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2928
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2929 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 322 13 138 20 240 240 240 496), lower := (rows 51 322 13 138 20 32 64 128 256), losses := [] }

theorem u2929 : Upper (D 1) (R 1) [50,320,9,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2929
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2930 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 13 138 48 244 212 212 468), lower := (rows 51 322 13 138 48 32 64 128 256), losses := [] }

theorem u2930 : Upper (D 1) (R 1) [50,320,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2930
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2931 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 13 138 80 180 244 180 436), lower := (rows 51 322 13 138 80 32 64 128 256), losses := [] }

theorem u2931 : Upper (D 1) (R 1) [50,320,9,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2931
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2932_4 : Upper (D 1) (R 1) [50,320,9,130,128,4] 13 :=
  permutation_upper _ _ _ [50,320,9,130,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u645

theorem m2932_16 : Upper (D 1) (R 1) [50,320,9,130,128,16] 13 :=
  permutation_upper _ _ _ [50,320,9,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u646

theorem m2932_64 : Upper (D 1) (R 1) [50,320,9,130,128,64] 13 :=
  permutation_upper _ _ _ [50,320,9,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u647

def r2932 : Route 9 := (fun mask => (mask,id))

def c2932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2932 : Upper (D 1) (R 1) [50,320,9,130,128] 13 := by
  apply FastRouting.sound _ _ [50,320,9,130,128] 13 (by decide) (choices 1) [4,16,64] r2932 c2932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2932_4
  · exact m2932_16
  · exact m2932_64

def b2933 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 13 140 18 240 240 240 496), lower := (rows 51 322 13 140 18 32 64 128 256), losses := [] }

theorem u2933 : Upper (D 1) (R 1) [50,320,9,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2933
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2934 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 13 140 48 242 210 210 466), lower := (rows 51 322 13 140 48 32 64 128 256), losses := [] }

theorem u2934 : Upper (D 1) (R 1) [50,320,9,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2934
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2935 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 13 140 80 178 242 178 434), lower := (rows 51 322 13 140 80 32 64 128 256), losses := [] }

theorem u2935 : Upper (D 1) (R 1) [50,320,9,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2935
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2936 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 13 140 144 114 114 242 370), lower := (rows 51 322 13 140 144 32 64 128 256), losses := [] }

theorem u2936 : Upper (D 1) (R 1) [50,320,9,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2936
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2937 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 13 200 18 180 244 180 436), lower := (rows 51 322 13 200 18 32 64 128 256), losses := [] }

theorem u2937 : Upper (D 1) (R 1) [50,320,9,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2937
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2938 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 322 13 200 20 178 242 178 434), lower := (rows 51 322 13 200 20 32 64 128 256), losses := [] }

theorem u2938 : Upper (D 1) (R 1) [50,320,9,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2938
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2939 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 13 200 48 182 214 150 406), lower := (rows 51 322 13 200 48 32 64 128 256), losses := [] }

theorem u2939 : Upper (D 1) (R 1) [50,320,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2939
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2939
end Delivery.IrregularNine14.P01
