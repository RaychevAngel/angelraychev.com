import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0070
import IrregularNine14P03C0071
import IrregularNine14P03C0072
import IrregularNine14P03C0073
import IrregularNine14P03C0074
import IrregularNine14P03C0075
import IrregularNine14P03C0076
import IrregularNine14P03C0077
import IrregularNine14P03C0079
import IrregularNine14P03C0080
import IrregularNine14P03C0081

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6900 : PairBound 9 := { available := 222, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 265 222 254 222 222 478), lower := (rows 97 35 133 265 16 32 64 128 256), losses := [] }

theorem u6900 : Upper (D 3) (R 3) [96,33,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6900
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6901 : PairBound 9 := { available := 221, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 266 221 253 221 221 477), lower := (rows 97 35 133 266 16 32 64 128 256), losses := [] }

theorem u6901 : Upper (D 3) (R 3) [96,33,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6901
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6902 : PairBound 9 := { available := 219, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 268 219 251 219 219 475), lower := (rows 97 35 133 268 16 32 64 128 256), losses := [] }

theorem u6902 : Upper (D 3) (R 3) [96,33,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6902
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6903 : PairBound 9 := { available := 159, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 328 159 191 223 159 415), lower := (rows 97 35 133 328 16 32 64 128 256), losses := [] }

theorem u6903 : Upper (D 3) (R 3) [96,33,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6903
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6904 : PairBound 9 := { available := 95, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 133 392 95 127 95 223 351), lower := (rows 97 35 133 392 16 32 64 128 256), losses := [] }

theorem u6904 : Upper (D 3) (R 3) [96,33,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6904
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6905 : PairBound 9 := { available := 285, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 200 285 317 349 413 285), lower := (rows 97 35 134 200 16 32 64 128 256), losses := [] }

theorem u6905 : Upper (D 3) (R 3) [96,33,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6905
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6906 : PairBound 9 := { available := 221, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 265 221 253 221 221 477), lower := (rows 97 35 134 265 16 32 64 128 256), losses := [] }

theorem u6906 : Upper (D 3) (R 3) [96,33,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6906
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6907 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 268 217 249 217 217 473), lower := (rows 97 35 134 268 16 32 64 128 256), losses := [] }

theorem u6907 : Upper (D 3) (R 3) [96,33,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6907
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6908 : PairBound 9 := { available := 157, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 328 157 189 221 157 413), lower := (rows 97 35 134 328 16 32 64 128 256), losses := [] }

theorem u6908 : Upper (D 3) (R 3) [96,33,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6908
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6909 : PairBound 9 := { available := 93, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 134 392 93 125 93 221 349), lower := (rows 97 35 134 392 16 32 64 128 256), losses := [] }

theorem u6909 : Upper (D 3) (R 3) [96,33,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6909
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6910 : PairBound 9 := { available := 215, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 140 265 215 247 215 215 471), lower := (rows 97 35 140 265 16 32 64 128 256), losses := [] }

theorem u6910 : Upper (D 3) (R 3) [96,33,136,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6910
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6911 : PairBound 9 := { available := 213, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 140 266 213 245 213 213 469), lower := (rows 97 35 140 266 16 32 64 128 256), losses := [] }

theorem u6911 : Upper (D 3) (R 3) [96,33,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6911
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6912 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 140 268 211 243 211 211 467), lower := (rows 97 35 140 268 16 32 64 128 256), losses := [] }

theorem u6912 : Upper (D 3) (R 3) [96,33,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6912
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6913 : PairBound 9 := { available := 151, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 140 328 151 183 215 151 407), lower := (rows 97 35 140 328 16 32 64 128 256), losses := [] }

theorem u6913 : Upper (D 3) (R 3) [96,33,136,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6913
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6914 : PairBound 9 := { available := 159, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 196 265 159 191 223 159 415), lower := (rows 97 35 196 265 16 32 64 128 256), losses := [] }

theorem u6914 : Upper (D 3) (R 3) [96,33,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6914
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6915 : PairBound 9 := { available := 157, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 196 266 157 189 221 157 413), lower := (rows 97 35 196 266 16 32 64 128 256), losses := [] }

theorem u6915 : Upper (D 3) (R 3) [96,33,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6915
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6916 : PairBound 9 := { available := 155, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 196 268 155 187 219 155 411), lower := (rows 97 35 196 268 16 32 64 128 256), losses := [] }

theorem u6916 : Upper (D 3) (R 3) [96,33,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6916
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6917 : PairBound 9 := { available := 31, camps := [{ cop := 1, region := 476, targets := 32 }], pairs := [(2,5)], upper := (rows 97 35 196 392 31 63 95 159 287), lower := (rows 97 35 196 392 16 32 64 128 256), losses := [] }

theorem u6917 : Upper (D 3) (R 3) [96,33,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6917
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6918 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 137 409 441 473 409 409), lower := (rows 97 38 70 137 16 32 64 128 256), losses := [] }

theorem u6918 : Upper (D 3) (R 3) [96,36,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6918
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6919 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 265 153 185 217 153 409), lower := (rows 97 38 70 265 16 32 64 128 256), losses := [] }

theorem u6919 : Upper (D 3) (R 3) [96,36,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6919
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6920 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 70 392 153 185 217 153 409), lower := (rows 97 38 70 392 16 32 64 128 256), losses := [] }

theorem u6920 : Upper (D 3) (R 3) [96,36,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6920
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6921_3 : Upper (D 3) (R 3) [96,36,72,129,3] 13 :=
  permutation_upper _ _ _ [96,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4238

def r6921 : Route 9 := (fun mask => (mask,id))

def c6921 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6921 : Upper (D 3) (R 3) [96,36,72,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129] 13 (by decide) (choices 2) [3,129,130,257,258,384] r6921 c6921
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6921_3
  · exact u4827
  · exact u4828
  · exact u4829
  · exact u4830
  · exact u4831

def b6922 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 76 138 401 433 465 401 401), lower := (rows 97 38 76 138 16 32 64 128 256), losses := [] }

theorem u6922 : Upper (D 3) (R 3) [96,36,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6922
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6923_3 : Upper (D 3) (R 3) [96,36,72,144,3] 13 :=
  permutation_upper _ _ _ [96,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4239

def r6923 : Route 9 := (fun mask => (mask,id))

def c6923 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6923 : Upper (D 3) (R 3) [96,36,72,144] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144] 13 (by decide) (choices 2) [3,129,130,257,258,384] r6923 c6923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6923_3
  · exact u4835
  · exact u4836
  · exact u4837
  · exact u4838
  · exact u4839

theorem m6924_3 : Upper (D 3) (R 3) [96,36,72,257,3] 13 :=
  permutation_upper _ _ _ [96,5,40,80,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4240

def r6924 : Route 9 := (fun mask => (mask,id))

def c6924 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6924 : Upper (D 3) (R 3) [96,36,72,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257] 13 (by decide) (choices 2) [3,129,130] r6924 c6924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6924_3
  · exact u4840
  · exact u4841

def b6925 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 76 266 145 177 209 145 401), lower := (rows 97 38 76 266 16 32 64 128 256), losses := [] }

theorem u6925 : Upper (D 3) (R 3) [96,36,72,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6925
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6926_3 : Upper (D 3) (R 3) [96,36,72,272,3] 13 :=
  permutation_upper _ _ _ [96,5,40,80,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4241

def r6926 : Route 9 := (fun mask => (mask,id))

def c6926 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6926 : Upper (D 3) (R 3) [96,36,72,272] 13 := by
  apply FastRouting.sound _ _ [96,36,72,272] 13 (by decide) (choices 2) [3,129,130] r6926 c6926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6926_3
  · exact u4843
  · exact u4844

theorem m6927_3 : Upper (D 3) (R 3) [96,36,72,384,3] 13 :=
  permutation_upper _ _ _ [96,5,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4242

def r6927 : Route 9 := (fun mask => (mask,id))

def c6927 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6927 : Upper (D 3) (R 3) [96,36,72,384] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384] 13 (by decide) (choices 2) [3,129,130] r6927 c6927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6927_3
  · exact u4845
  · exact u4846

theorem m6928_3 : Upper (D 3) (R 3) [96,36,80,129,3] 13 :=
  permutation_upper _ _ _ [96,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4235

theorem m6928_9 : Upper (D 3) (R 3) [96,36,80,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4313

theorem m6928_10 : Upper (D 3) (R 3) [96,36,80,129,10] 13 :=
  permutation_upper _ _ _ [96,12,48,129,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4642

theorem m6928_129 : Upper (D 3) (R 3) [96,36,80,129,129] 13 :=
  permutation_upper _ _ _ [96,36,72,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4827

theorem m6928_130 : Upper (D 3) (R 3) [96,36,80,129,130] 13 :=
  permutation_upper _ _ _ [96,36,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4832

theorem m6928_136 : Upper (D 3) (R 3) [96,36,80,129,136] 13 :=
  permutation_upper _ _ _ [96,36,72,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4835

theorem m6928_257 : Upper (D 3) (R 3) [96,36,80,129,257] 13 :=
  permutation_upper _ _ _ [96,36,72,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4840

theorem m6928_258 : Upper (D 3) (R 3) [96,36,80,129,258] 13 :=
  permutation_upper _ _ _ [96,36,72,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4842

theorem m6928_264 : Upper (D 3) (R 3) [96,36,80,129,264] 13 :=
  permutation_upper _ _ _ [96,36,72,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4843

theorem m6928_384 : Upper (D 3) (R 3) [96,36,80,129,384] 13 :=
  permutation_upper _ _ _ [96,36,72,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4845

def r6928 : Route 9 := (fun mask => (mask,id))

def c6928 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6928 : Upper (D 3) (R 3) [96,36,80,129] 13 := by
  apply FastRouting.sound _ _ [96,36,80,129] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r6928 c6928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6928_3
  · exact m6928_9
  · exact m6928_10
  · exact m6928_129
  · exact m6928_130
  · exact m6928_136
  · exact m6928_257
  · exact m6928_258
  · exact m6928_264
  · exact m6928_384

theorem m6929_9 : Upper (D 3) (R 3) [96,36,80,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4396

theorem m6929_129 : Upper (D 3) (R 3) [96,36,80,130,129] 13 :=
  permutation_upper _ _ _ [96,36,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4828

theorem m6929_136 : Upper (D 3) (R 3) [96,36,80,130,136] 13 :=
  permutation_upper _ _ _ [96,36,72,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4836

theorem m6929_257 : Upper (D 3) (R 3) [96,36,80,130,257] 13 :=
  permutation_upper _ _ _ [96,36,72,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4841

theorem m6929_264 : Upper (D 3) (R 3) [96,36,80,130,264] 13 :=
  permutation_upper _ _ _ [96,36,72,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4844

theorem m6929_384 : Upper (D 3) (R 3) [96,36,80,130,384] 13 :=
  permutation_upper _ _ _ [96,36,72,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4846

def r6929 : Route 9 := (fun mask => (mask,id))

def c6929 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6929 : Upper (D 3) (R 3) [96,36,80,130] 13 := by
  apply FastRouting.sound _ _ [96,36,80,130] 13 (by decide) (choices 2) [9,129,136,257,264,384] r6929 c6929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6929_9
  · exact m6929_129
  · exact m6929_136
  · exact m6929_257
  · exact m6929_264
  · exact m6929_384

theorem m6930_3 : Upper (D 3) (R 3) [96,36,80,257,3] 13 :=
  permutation_upper _ _ _ [96,5,40,66,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4236

theorem m6930_9 : Upper (D 3) (R 3) [96,36,80,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4480

theorem m6930_10 : Upper (D 3) (R 3) [96,36,80,257,10] 13 :=
  permutation_upper _ _ _ [96,12,48,257,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4661

theorem m6930_129 : Upper (D 3) (R 3) [96,36,80,257,129] 13 :=
  permutation_upper _ _ _ [96,36,72,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4829

theorem m6930_130 : Upper (D 3) (R 3) [96,36,80,257,130] 13 :=
  permutation_upper _ _ _ [96,36,72,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4833

theorem m6930_136 : Upper (D 3) (R 3) [96,36,80,257,136] 13 :=
  permutation_upper _ _ _ [96,36,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4837

def r6930 : Route 9 := (fun mask => (mask,id))

def c6930 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6930 : Upper (D 3) (R 3) [96,36,80,257] 13 := by
  apply FastRouting.sound _ _ [96,36,80,257] 13 (by decide) (choices 2) [3,9,10,129,130,136] r6930 c6930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6930_3
  · exact m6930_9
  · exact m6930_10
  · exact m6930_129
  · exact m6930_130
  · exact m6930_136

theorem m6931_9 : Upper (D 3) (R 3) [96,36,80,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4517

theorem m6931_129 : Upper (D 3) (R 3) [96,36,80,258,129] 13 :=
  permutation_upper _ _ _ [96,36,72,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4830

theorem m6931_136 : Upper (D 3) (R 3) [96,36,80,258,136] 13 :=
  permutation_upper _ _ _ [96,36,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4838

def r6931 : Route 9 := (fun mask => (mask,id))

def c6931 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6931 : Upper (D 3) (R 3) [96,36,80,258] 13 := by
  apply FastRouting.sound _ _ [96,36,80,258] 13 (by decide) (choices 2) [9,129,136] r6931 c6931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6931_9
  · exact m6931_129
  · exact m6931_136

theorem m6932_3 : Upper (D 3) (R 3) [96,36,80,384,3] 13 :=
  permutation_upper _ _ _ [96,5,40,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4237

theorem m6932_9 : Upper (D 3) (R 3) [96,36,80,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,34,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4564

theorem m6932_10 : Upper (D 3) (R 3) [96,36,80,384,10] 13 :=
  permutation_upper _ _ _ [96,12,48,384,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4670

theorem m6932_129 : Upper (D 3) (R 3) [96,36,80,384,129] 13 :=
  permutation_upper _ _ _ [96,36,72,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4831

theorem m6932_130 : Upper (D 3) (R 3) [96,36,80,384,130] 13 :=
  permutation_upper _ _ _ [96,36,72,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4834

theorem m6932_136 : Upper (D 3) (R 3) [96,36,80,384,136] 13 :=
  permutation_upper _ _ _ [96,36,72,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4839

def r6932 : Route 9 := (fun mask => (mask,id))

def c6932 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6932 : Upper (D 3) (R 3) [96,36,80,384] 13 := by
  apply FastRouting.sound _ _ [96,36,80,384] 13 (by decide) (choices 2) [3,9,10,129,130,136] r6932 c6932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6932_3
  · exact m6932_9
  · exact m6932_10
  · exact m6932_129
  · exact m6932_130
  · exact m6932_136

theorem m6933_3 : Upper (D 3) (R 3) [96,36,129,80,3] 13 :=
  permutation_upper _ _ _ [96,5,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4243

theorem m6933_9 : Upper (D 3) (R 3) [96,36,129,80,9] 13 :=
  permutation_upper _ _ _ [96,5,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4213

theorem m6933_10 : Upper (D 3) (R 3) [96,36,129,80,10] 13 :=
  permutation_upper _ _ _ [96,12,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4622

def r6933 : Route 9 := (fun mask => (mask,id))

def c6933 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6933 : Upper (D 3) (R 3) [96,36,129,80] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r6933 c6933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6933_3
  · exact m6933_9
  · exact m6933_10
  · exact u4847
  · exact u4848
  · exact u4849
  · exact u4850
  · exact u4851
  · exact u4852
  · exact u4853

def b6934 : PairBound 9 := { available := 347, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 133 137 347 379 347 475 347), lower := (rows 97 38 133 137 16 32 64 128 256), losses := [] }

theorem u6934 : Upper (D 3) (R 3) [96,36,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6934
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6935 : PairBound 9 := { available := 345, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 138 345 377 345 473 345), lower := (rows 97 38 133 138 16 32 64 128 256), losses := [] }

theorem u6935 : Upper (D 3) (R 3) [96,36,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6935
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6936_3 : Upper (D 3) (R 3) [96,36,129,144,3] 13 :=
  permutation_upper _ _ _ [96,5,40,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4244

theorem m6936_9 : Upper (D 3) (R 3) [96,36,129,144,9] 13 :=
  permutation_upper _ _ _ [96,5,130,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4353

theorem m6936_10 : Upper (D 3) (R 3) [96,36,129,144,10] 13 :=
  permutation_upper _ _ _ [96,12,48,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4650

theorem m6936_65 : Upper (D 3) (R 3) [96,36,129,144,65] 13 :=
  permutation_upper _ _ _ [96,33,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4784

theorem m6936_66 : Upper (D 3) (R 3) [96,36,129,144,66] 13 :=
  permutation_upper _ _ _ [96,36,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4828

theorem m6936_72 : Upper (D 3) (R 3) [96,36,129,144,72] 13 :=
  permutation_upper _ _ _ [96,36,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4849

def r6936 : Route 9 := (fun mask => (mask,id))

def c6936 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6936 : Upper (D 3) (R 3) [96,36,129,144] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r6936 c6936
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6936_3
  · exact m6936_9
  · exact m6936_10
  · exact m6936_65
  · exact m6936_66
  · exact m6936_72
  · exact u4861
  · exact u4862
  · exact u4863
  · exact u4864

theorem m6937_3 : Upper (D 3) (R 3) [96,36,129,192,3] 13 :=
  permutation_upper _ _ _ [96,5,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4245

theorem m6937_9 : Upper (D 3) (R 3) [96,36,129,192,9] 13 :=
  permutation_upper _ _ _ [96,5,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4458

theorem m6937_10 : Upper (D 3) (R 3) [96,36,129,192,10] 13 :=
  permutation_upper _ _ _ [96,12,48,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4655

def r6937 : Route 9 := (fun mask => (mask,id))

def c6937 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6937 : Upper (D 3) (R 3) [96,36,129,192] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192] 13 (by decide) (choices 2) [3,9,10,257,258,264] r6937 c6937
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6937_3
  · exact m6937_9
  · exact m6937_10
  · exact u4865
  · exact u4866
  · exact u4867

theorem m6938_3 : Upper (D 3) (R 3) [96,36,129,257,3] 13 :=
  permutation_upper _ _ _ [96,5,40,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4246

theorem m6938_9 : Upper (D 3) (R 3) [96,36,129,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4484

theorem m6938_10 : Upper (D 3) (R 3) [96,36,129,257,10] 13 :=
  permutation_upper _ _ _ [96,12,48,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4662

theorem m6938_65 : Upper (D 3) (R 3) [96,36,129,257,65] 13 :=
  permutation_upper _ _ _ [96,33,72,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4785

theorem m6938_66 : Upper (D 3) (R 3) [96,36,129,257,66] 13 :=
  permutation_upper _ _ _ [96,36,72,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4829

theorem m6938_72 : Upper (D 3) (R 3) [96,36,129,257,72] 13 :=
  permutation_upper _ _ _ [96,36,129,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4850

theorem m6938_129 : Upper (D 3) (R 3) [96,36,129,257,129] 13 :=
  permutation_upper _ _ _ [96,36,129,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4854

theorem m6938_130 : Upper (D 3) (R 3) [96,36,129,257,130] 13 :=
  permutation_upper _ _ _ [96,36,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4858

theorem m6938_136 : Upper (D 3) (R 3) [96,36,129,257,136] 13 :=
  permutation_upper _ _ _ [96,36,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4861

theorem m6938_192 : Upper (D 3) (R 3) [96,36,129,257,192] 13 :=
  permutation_upper _ _ _ [96,36,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4865

def r6938 : Route 9 := (fun mask => (mask,id))

def c6938 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6938 : Upper (D 3) (R 3) [96,36,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,257] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r6938 c6938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6938_3
  · exact m6938_9
  · exact m6938_10
  · exact m6938_65
  · exact m6938_66
  · exact m6938_72
  · exact m6938_129
  · exact m6938_130
  · exact m6938_136
  · exact m6938_192

theorem m6939_9 : Upper (D 3) (R 3) [96,36,129,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4518

theorem m6939_65 : Upper (D 3) (R 3) [96,36,129,258,65] 13 :=
  permutation_upper _ _ _ [96,33,72,129,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4787

theorem m6939_72 : Upper (D 3) (R 3) [96,36,129,258,72] 13 :=
  permutation_upper _ _ _ [96,36,129,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4851

theorem m6939_129 : Upper (D 3) (R 3) [96,36,129,258,129] 13 :=
  permutation_upper _ _ _ [96,36,129,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4855

theorem m6939_136 : Upper (D 3) (R 3) [96,36,129,258,136] 13 :=
  permutation_upper _ _ _ [96,36,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4862

theorem m6939_192 : Upper (D 3) (R 3) [96,36,129,258,192] 13 :=
  permutation_upper _ _ _ [96,36,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4866

def r6939 : Route 9 := (fun mask => (mask,id))

def c6939 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6939 : Upper (D 3) (R 3) [96,36,129,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,258] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6939 c6939
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6939_9
  · exact m6939_65
  · exact m6939_72
  · exact m6939_129
  · exact m6939_136
  · exact m6939_192

theorem m6940_3 : Upper (D 3) (R 3) [96,36,129,272,3] 13 :=
  permutation_upper _ _ _ [96,5,40,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4247

theorem m6940_9 : Upper (D 3) (R 3) [96,36,129,272,9] 13 :=
  permutation_upper _ _ _ [96,5,258,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4496

theorem m6940_10 : Upper (D 3) (R 3) [96,36,129,272,10] 13 :=
  permutation_upper _ _ _ [96,12,48,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4665

theorem m6940_65 : Upper (D 3) (R 3) [96,36,129,272,65] 13 :=
  permutation_upper _ _ _ [96,33,72,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4786

theorem m6940_66 : Upper (D 3) (R 3) [96,36,129,272,66] 13 :=
  permutation_upper _ _ _ [96,36,72,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4830

theorem m6940_72 : Upper (D 3) (R 3) [96,36,129,272,72] 13 :=
  permutation_upper _ _ _ [96,36,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4852

theorem m6940_129 : Upper (D 3) (R 3) [96,36,129,272,129] 13 :=
  permutation_upper _ _ _ [96,36,129,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4856

theorem m6940_130 : Upper (D 3) (R 3) [96,36,129,272,130] 13 :=
  permutation_upper _ _ _ [96,36,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4859

theorem m6940_136 : Upper (D 3) (R 3) [96,36,129,272,136] 13 :=
  permutation_upper _ _ _ [96,36,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4863

theorem m6940_192 : Upper (D 3) (R 3) [96,36,129,272,192] 13 :=
  permutation_upper _ _ _ [96,36,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4867

def r6940 : Route 9 := (fun mask => (mask,id))

def c6940 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6940 : Upper (D 3) (R 3) [96,36,129,272] 13 := by
  apply FastRouting.sound _ _ [96,36,129,272] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r6940 c6940
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6940_3
  · exact m6940_9
  · exact m6940_10
  · exact m6940_65
  · exact m6940_66
  · exact m6940_72
  · exact m6940_129
  · exact m6940_130
  · exact m6940_136
  · exact m6940_192

theorem m6941_3 : Upper (D 3) (R 3) [96,36,129,320,3] 13 :=
  permutation_upper _ _ _ [96,5,40,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4248

theorem m6941_9 : Upper (D 3) (R 3) [96,36,129,320,9] 13 :=
  permutation_upper _ _ _ [96,5,288,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4548

theorem m6941_10 : Upper (D 3) (R 3) [96,36,129,320,10] 13 :=
  permutation_upper _ _ _ [96,12,48,320,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4667

theorem m6941_129 : Upper (D 3) (R 3) [96,36,129,320,129] 13 :=
  permutation_upper _ _ _ [96,36,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4857

theorem m6941_130 : Upper (D 3) (R 3) [96,36,129,320,130] 13 :=
  permutation_upper _ _ _ [96,36,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4860

theorem m6941_136 : Upper (D 3) (R 3) [96,36,129,320,136] 13 :=
  permutation_upper _ _ _ [96,36,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4864

def r6941 : Route 9 := (fun mask => (mask,id))

def c6941 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6941 : Upper (D 3) (R 3) [96,36,129,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,320] 13 (by decide) (choices 2) [3,9,10,129,130,136] r6941 c6941
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6941_3
  · exact m6941_9
  · exact m6941_10
  · exact m6941_129
  · exact m6941_130
  · exact m6941_136

theorem m6942_3 : Upper (D 3) (R 3) [96,36,129,384,3] 13 :=
  permutation_upper _ _ _ [96,5,40,129,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4249

theorem m6942_9 : Upper (D 3) (R 3) [96,36,129,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4569

theorem m6942_10 : Upper (D 3) (R 3) [96,36,129,384,10] 13 :=
  permutation_upper _ _ _ [96,12,48,384,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4671

theorem m6942_65 : Upper (D 3) (R 3) [96,36,129,384,65] 13 :=
  permutation_upper _ _ _ [96,33,72,129,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4788

theorem m6942_66 : Upper (D 3) (R 3) [96,36,129,384,66] 13 :=
  permutation_upper _ _ _ [96,36,72,129,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4831

theorem m6942_72 : Upper (D 3) (R 3) [96,36,129,384,72] 13 :=
  permutation_upper _ _ _ [96,36,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4853

def r6942 : Route 9 := (fun mask => (mask,id))

def c6942 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6942 : Upper (D 3) (R 3) [96,36,129,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,384] 13 (by decide) (choices 2) [3,9,10,65,66,72] r6942 c6942
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6942_3
  · exact m6942_9
  · exact m6942_10
  · exact m6942_65
  · exact m6942_66
  · exact m6942_72

def b6943 : PairBound 9 := { available := 345, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 137 345 377 345 473 345), lower := (rows 97 38 134 137 16 32 64 128 256), losses := [] }

theorem u6943 : Upper (D 3) (R 3) [96,36,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6943
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6944 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 200 281 313 345 409 281), lower := (rows 97 38 134 200 16 32 64 128 256), losses := [] }

theorem u6944 : Upper (D 3) (R 3) [96,36,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6944
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6945 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 265 217 249 217 217 473), lower := (rows 97 38 134 265 16 32 64 128 256), losses := [] }

theorem u6945 : Upper (D 3) (R 3) [96,36,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6945
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6946 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 328 153 185 217 153 409), lower := (rows 97 38 134 328 16 32 64 128 256), losses := [] }

theorem u6946 : Upper (D 3) (R 3) [96,36,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6946
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6947 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 134 392 89 121 89 217 345), lower := (rows 97 38 134 392 16 32 64 128 256), losses := [] }

theorem u6947 : Upper (D 3) (R 3) [96,36,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6947
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6948_3 : Upper (D 3) (R 3) [96,36,136,80,3] 13 :=
  permutation_upper _ _ _ [96,5,40,144,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4255

theorem m6948_129 : Upper (D 3) (R 3) [96,36,136,80,129] 13 :=
  permutation_upper _ _ _ [96,36,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4848

def r6948 : Route 9 := (fun mask => (mask,id))

def c6948 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6948 : Upper (D 3) (R 3) [96,36,136,80] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r6948 c6948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6948_3
  · exact m6948_129
  · exact u4878
  · exact u4879
  · exact u4880
  · exact u4881

def b6949 : PairBound 9 := { available := 339, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 339 371 339 467 339), lower := (rows 97 38 140 137 16 32 64 128 256), losses := [] }

theorem u6949 : Upper (D 3) (R 3) [96,36,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6949
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6950 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 138 337 369 337 465 337), lower := (rows 97 38 140 138 16 32 64 128 256), losses := [] }

theorem u6950 : Upper (D 3) (R 3) [96,36,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6950
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6951 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 339 355 323 451 323), lower := (rows 97 38 140 152 16 32 64 128 256), losses := [] }

theorem u6951 : Upper (D 3) (R 3) [96,36,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6951
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6952 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 200 275 307 339 403 275), lower := (rows 97 38 140 200 16 32 64 128 256), losses := [] }

theorem u6952 : Upper (D 3) (R 3) [96,36,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6952
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6953_3 : Upper (D 3) (R 3) [96,36,136,257,3] 13 :=
  permutation_upper _ _ _ [96,5,40,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4256

theorem m6953_65 : Upper (D 3) (R 3) [96,36,136,257,65] 13 :=
  permutation_upper _ _ _ [96,33,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4793

theorem m6953_66 : Upper (D 3) (R 3) [96,36,136,257,66] 13 :=
  permutation_upper _ _ _ [96,36,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4837

def r6953 : Route 9 := (fun mask => (mask,id))

def c6953 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6953 : Upper (D 3) (R 3) [96,36,136,257] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r6953 c6953
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6953_3
  · exact m6953_65
  · exact m6953_66
  · exact u4892
  · exact u4893
  · exact u4894

def b6954 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 140 266 209 241 209 209 465), lower := (rows 97 38 140 266 16 32 64 128 256), losses := [] }

theorem u6954 : Upper (D 3) (R 3) [96,36,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6954
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6955_3 : Upper (D 3) (R 3) [96,36,136,272,3] 13 :=
  permutation_upper _ _ _ [96,5,40,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4257

theorem m6955_65 : Upper (D 3) (R 3) [96,36,136,272,65] 13 :=
  permutation_upper _ _ _ [96,33,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4794

theorem m6955_66 : Upper (D 3) (R 3) [96,36,136,272,66] 13 :=
  permutation_upper _ _ _ [96,36,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4838

def r6955 : Route 9 := (fun mask => (mask,id))

def c6955 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6955 : Upper (D 3) (R 3) [96,36,136,272] 13 := by
  apply FastRouting.sound _ _ [96,36,136,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r6955 c6955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6955_3
  · exact m6955_65
  · exact m6955_66
  · exact u4897
  · exact u4898
  · exact u4899

theorem m6956_3 : Upper (D 3) (R 3) [96,36,136,320,3] 13 :=
  permutation_upper _ _ _ [96,5,40,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4258

def r6956 : Route 9 := (fun mask => (mask,id))

def c6956 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6956 : Upper (D 3) (R 3) [96,36,136,320] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320] 13 (by decide) (choices 2) [3,129,130] r6956 c6956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6956_3
  · exact u4900
  · exact u4901

def b6957 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 392 83 115 83 211 339), lower := (rows 97 38 140 392 16 32 64 128 256), losses := [] }

theorem u6957 : Upper (D 3) (R 3) [96,36,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6957
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6958_3 : Upper (D 3) (R 3) [96,36,144,129,3] 13 :=
  permutation_upper _ _ _ [96,5,40,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4250

theorem m6958_9 : Upper (D 3) (R 3) [96,36,144,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4322

theorem m6958_10 : Upper (D 3) (R 3) [96,36,144,129,10] 13 :=
  permutation_upper _ _ _ [96,12,48,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4644

theorem m6958_65 : Upper (D 3) (R 3) [96,36,144,129,65] 13 :=
  permutation_upper _ _ _ [96,33,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4789

theorem m6958_66 : Upper (D 3) (R 3) [96,36,144,129,66] 13 :=
  permutation_upper _ _ _ [96,36,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4832

theorem m6958_72 : Upper (D 3) (R 3) [96,36,144,129,72] 13 :=
  permutation_upper _ _ _ [96,36,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4848

theorem m6958_257 : Upper (D 3) (R 3) [96,36,144,129,257] 13 :=
  permutation_upper _ _ _ [96,36,136,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4892

theorem m6958_258 : Upper (D 3) (R 3) [96,36,144,129,258] 13 :=
  permutation_upper _ _ _ [96,36,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4895

theorem m6958_264 : Upper (D 3) (R 3) [96,36,144,129,264] 13 :=
  permutation_upper _ _ _ [96,36,136,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4897

theorem m6958_320 : Upper (D 3) (R 3) [96,36,144,129,320] 13 :=
  permutation_upper _ _ _ [96,36,136,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4900

def r6958 : Route 9 := (fun mask => (mask,id))

def c6958 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6958 : Upper (D 3) (R 3) [96,36,144,129] 13 := by
  apply FastRouting.sound _ _ [96,36,144,129] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r6958 c6958
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6958_3
  · exact m6958_9
  · exact m6958_10
  · exact m6958_65
  · exact m6958_66
  · exact m6958_72
  · exact m6958_257
  · exact m6958_258
  · exact m6958_264
  · exact m6958_320

def b6959 : PairBound 9 := { available := 329, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 148 138 345 361 329 457 329), lower := (rows 97 38 148 138 16 32 64 128 256), losses := [] }

theorem u6959 : Upper (D 3) (R 3) [96,36,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6959
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6959
end Delivery.IrregularNine14.P03
