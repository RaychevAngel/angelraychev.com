import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0104
import IrregularNine14P01C0105
import IrregularNine14P01C0106
import IrregularNine14P01C0107

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m8880_3 : Upper (D 1) (R 1) [28,272,34,3] 13 :=
  permutation_upper _ _ _ [28,272,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6242

theorem m8880_33 : Upper (D 1) (R 1) [28,272,34,33] 13 :=
  permutation_upper _ _ _ [28,272,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6244

theorem m8880_65 : Upper (D 1) (R 1) [28,272,34,65] 13 :=
  permutation_upper _ _ _ [28,272,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6245

def r8880 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8880 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8880 : Upper (D 1) (R 1) [28,272,34] 13 := by
  apply FastRouting.sound _ _ [28,272,34] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r8880 c8880
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8880_3
  · exact m8880_33
  · exact u6248
  · exact m8880_65
  · exact u6249
  · exact u6250
  · exact u6251

theorem m8881_3 : Upper (D 1) (R 1) [28,272,96,3] 13 :=
  permutation_upper _ _ _ [28,272,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6243

theorem m8881_33 : Upper (D 1) (R 1) [28,272,96,33] 13 :=
  permutation_upper _ _ _ [28,272,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6246

theorem m8881_34 : Upper (D 1) (R 1) [28,272,96,34] 13 :=
  permutation_upper _ _ _ [28,272,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6250

theorem m8881_129 : Upper (D 1) (R 1) [28,272,96,129] 13 :=
  permutation_upper _ _ _ [28,272,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6247

theorem m8881_130 : Upper (D 1) (R 1) [28,272,96,130] 13 :=
  permutation_upper _ _ _ [28,272,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6251

def r8881 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8881 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8881 : Upper (D 1) (R 1) [28,272,96] 13 := by
  apply FastRouting.sound _ _ [28,272,96] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r8881 c8881
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8881_3
  · exact m8881_33
  · exact m8881_34
  · exact u6252
  · exact m8881_129
  · exact m8881_130
  · exact u6253

def r8882 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8882 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8882 : Upper (D 1) (R 1) [28,288,3] 13 := by
  apply FastRouting.sound _ _ [28,288,3] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8882 c8882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6254
  · exact u6255
  · exact u6256
  · exact u6257
  · exact u6258
  · exact u6259
  · exact u6260

def b8883 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 290 21 234 242 226 226 226 482), lower := (rows 29 290 21 8 16 32 64 128 256), losses := [] }

theorem u8883 : Upper (D 1) (R 1) [28,288,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8883
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8884 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 22 235 243 227 227 227 483), lower := (rows 29 290 22 8 16 32 64 128 256), losses := [] }

theorem u8884 : Upper (D 1) (R 1) [28,288,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8884
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8885 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 29 290 37 218 210 242 210 210 466), lower := (rows 29 290 37 8 16 32 64 128 256), losses := [] }

theorem u8885 : Upper (D 1) (R 1) [28,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8885
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8886 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 290 38 219 211 243 211 211 467), lower := (rows 29 290 38 8 16 32 64 128 256), losses := [] }

theorem u8886 : Upper (D 1) (R 1) [28,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8886
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8887 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 52 203 211 227 195 195 451), lower := (rows 29 290 52 8 16 32 64 128 256), losses := [] }

theorem u8887 : Upper (D 1) (R 1) [28,288,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8887
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8888_18 : Upper (D 1) (R 1) [28,288,65,18] 13 :=
  permutation_upper _ _ _ [28,288,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6264

theorem m8888_34 : Upper (D 1) (R 1) [28,288,65,34] 13 :=
  permutation_upper _ _ _ [28,288,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6270

theorem m8888_48 : Upper (D 1) (R 1) [28,288,65,48] 13 :=
  permutation_upper _ _ _ [28,288,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6273

def r8888 : Route 9 := (fun mask => (mask,id))

def c8888 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8888 : Upper (D 1) (R 1) [28,288,65] 13 := by
  apply FastRouting.sound _ _ [28,288,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r8888 c8888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8888_18
  · exact m8888_34
  · exact m8888_48
  · exact u6276
  · exact u6277
  · exact u6278
  · exact u6279
  · exact u6280
  · exact u6281
  · exact u6282

theorem m8889_3 : Upper (D 1) (R 1) [28,288,66,3] 13 :=
  permutation_upper _ _ _ [28,288,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6257

theorem m8889_17 : Upper (D 1) (R 1) [28,288,66,17] 13 :=
  permutation_upper _ _ _ [28,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6261

theorem m8889_18 : Upper (D 1) (R 1) [28,288,66,18] 13 :=
  permutation_upper _ _ _ [28,288,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6265

theorem m8889_33 : Upper (D 1) (R 1) [28,288,66,33] 13 :=
  permutation_upper _ _ _ [28,288,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6268

theorem m8889_34 : Upper (D 1) (R 1) [28,288,66,34] 13 :=
  permutation_upper _ _ _ [28,288,34,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6271

theorem m8889_48 : Upper (D 1) (R 1) [28,288,66,48] 13 :=
  permutation_upper _ _ _ [28,288,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6274

theorem m8889_65 : Upper (D 1) (R 1) [28,288,66,65] 13 :=
  permutation_upper _ _ _ [28,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6276

theorem m8889_129 : Upper (D 1) (R 1) [28,288,66,129] 13 :=
  permutation_upper _ _ _ [28,288,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6279

def r8889 : Route 9 := (fun mask => (mask,id))

def c8889 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8889 : Upper (D 1) (R 1) [28,288,66] 13 := by
  apply FastRouting.sound _ _ [28,288,66] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r8889 c8889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8889_3
  · exact m8889_17
  · exact m8889_18
  · exact m8889_33
  · exact m8889_34
  · exact m8889_48
  · exact m8889_65
  · exact u6283
  · exact u6284
  · exact u6285
  · exact m8889_129
  · exact u6286
  · exact u6287
  · exact u6288
  · exact u6289

def b8890 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 84 235 243 227 227 227 483), lower := (rows 29 290 84 8 16 32 64 128 256), losses := [] }

theorem u8890 : Upper (D 1) (R 1) [28,288,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8890
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8891_3 : Upper (D 1) (R 1) [28,288,96,3] 13 :=
  permutation_upper _ _ _ [28,288,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6259

theorem m8891_17 : Upper (D 1) (R 1) [28,288,96,17] 13 :=
  permutation_upper _ _ _ [28,288,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6262

theorem m8891_18 : Upper (D 1) (R 1) [28,288,96,18] 13 :=
  permutation_upper _ _ _ [28,288,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6266

theorem m8891_65 : Upper (D 1) (R 1) [28,288,96,65] 13 :=
  permutation_upper _ _ _ [28,288,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6278

theorem m8891_66 : Upper (D 1) (R 1) [28,288,96,66] 13 :=
  permutation_upper _ _ _ [28,288,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6285

theorem m8891_80 : Upper (D 1) (R 1) [28,288,96,80] 13 :=
  permutation_upper _ _ _ [28,288,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6290

theorem m8891_129 : Upper (D 1) (R 1) [28,288,96,129] 13 :=
  permutation_upper _ _ _ [28,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6281

theorem m8891_130 : Upper (D 1) (R 1) [28,288,96,130] 13 :=
  permutation_upper _ _ _ [28,288,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6288

theorem m8891_144 : Upper (D 1) (R 1) [28,288,96,144] 13 :=
  permutation_upper _ _ _ [28,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6291

def r8891 : Route 9 := (fun mask => (mask,id))

def c8891 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8891 : Upper (D 1) (R 1) [28,288,96] 13 := by
  apply FastRouting.sound _ _ [28,288,96] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r8891 c8891
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8891_3
  · exact m8891_17
  · exact m8891_18
  · exact m8891_65
  · exact m8891_66
  · exact m8891_80
  · exact m8891_129
  · exact m8891_130
  · exact m8891_144
  · exact u6293

theorem m8892_3 : Upper (D 1) (R 1) [28,288,192,3] 13 :=
  permutation_upper _ _ _ [28,288,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6260

theorem m8892_17 : Upper (D 1) (R 1) [28,288,192,17] 13 :=
  permutation_upper _ _ _ [28,288,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6263

theorem m8892_18 : Upper (D 1) (R 1) [28,288,192,18] 13 :=
  permutation_upper _ _ _ [28,288,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6267

theorem m8892_33 : Upper (D 1) (R 1) [28,288,192,33] 13 :=
  permutation_upper _ _ _ [28,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6269

theorem m8892_34 : Upper (D 1) (R 1) [28,288,192,34] 13 :=
  permutation_upper _ _ _ [28,288,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6272

theorem m8892_48 : Upper (D 1) (R 1) [28,288,192,48] 13 :=
  permutation_upper _ _ _ [28,288,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6275

theorem m8892_65 : Upper (D 1) (R 1) [28,288,192,65] 13 :=
  permutation_upper _ _ _ [28,288,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6282

theorem m8892_66 : Upper (D 1) (R 1) [28,288,192,66] 13 :=
  permutation_upper _ _ _ [28,288,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6289

theorem m8892_80 : Upper (D 1) (R 1) [28,288,192,80] 13 :=
  permutation_upper _ _ _ [28,288,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6292

theorem m8892_96 : Upper (D 1) (R 1) [28,288,192,96] 13 :=
  permutation_upper _ _ _ [28,288,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6293

def r8892 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8892 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8892 : Upper (D 1) (R 1) [28,288,192] 13 := by
  apply FastRouting.sound _ _ [28,288,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r8892 c8892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8892_3
  · exact m8892_17
  · exact m8892_18
  · exact m8892_33
  · exact m8892_34
  · exact m8892_48
  · exact m8892_65
  · exact m8892_66
  · exact m8892_80
  · exact m8892_96
  · exact u6294

def b8893 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 14 504 496 496 496 496 496), lower := (rows 51 7 14 8 16 32 64 128 256), losses := [] }

theorem u8893 : Upper (D 1) (R 1) [50,5,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8893
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8894 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 22 488 504 488 488 488 488), lower := (rows 51 7 22 8 16 32 64 128 256), losses := [] }

theorem u8894 : Upper (D 1) (R 1) [50,5,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8894
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8895 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 7 28 490 498 482 482 482 482), lower := (rows 51 7 28 8 16 32 64 128 256), losses := [] }

theorem u8895 : Upper (D 1) (R 1) [50,5,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8895
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8896 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 51 7 52 458 474 490 458 458 458), lower := (rows 51 7 52 8 16 32 64 128 256), losses := [] }

theorem u8896 : Upper (D 1) (R 1) [50,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8896
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8897 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 70 504 504 504 504 504 504), lower := (rows 51 7 70 8 16 32 64 128 256), losses := [] }

theorem u8897 : Upper (D 1) (R 1) [50,5,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8897
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8898 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8898 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8898 : Upper (D 1) (R 1) [50,5,72] 13 := by
  apply FastRouting.sound _ _ [50,5,72] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r8898 c8898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6295
  · exact u6296
  · exact u6297
  · exact u6298
  · exact u6299
  · exact u6300
  · exact u6301
  · exact u6302
  · exact u6303
  · exact u6304
  · exact u6305

def b8899 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 7 84 490 506 490 490 490 490), lower := (rows 51 7 84 8 16 32 64 128 256), losses := [] }

theorem u8899 : Upper (D 1) (R 1) [50,5,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8899
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8900 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8900 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8900 : Upper (D 1) (R 1) [50,5,192] 13 := by
  apply FastRouting.sound _ _ [50,5,192] 13 (by decide) (choices 2) [18,48,66,80,192,258,272,320] r8900 c8900
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6306
  · exact u6307
  · exact u6308
  · exact u6309
  · exact u6310
  · exact u6311
  · exact u6312
  · exact u6313

def b8901 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 262 248 248 248 248 248 504), lower := (rows 51 7 262 8 16 32 64 128 256), losses := [] }

theorem u8901 : Upper (D 1) (R 1) [50,5,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8902 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8902 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8902 : Upper (D 1) (R 1) [50,5,264] 13 := by
  apply FastRouting.sound _ _ [50,5,264] 13 (by decide) (choices 2) [18,48,66,80,192] r8902 c8902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u6314
  · exact u6315
  · exact u6316
  · exact u6317
  · exact u6318

def b8903 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 51 7 276 234 250 234 234 234 490), lower := (rows 51 7 276 8 16 32 64 128 256), losses := [] }

theorem u8903 : Upper (D 1) (R 1) [50,5,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8904 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8904 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8904 : Upper (D 1) (R 1) [50,5,320] 13 := by
  apply FastRouting.sound _ _ [50,5,320] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r8904 c8904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6319
  · exact u6320
  · exact u6321
  · exact u6322
  · exact u6323
  · exact u6324
  · exact u6325

def b8905 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 7 504 496 496 496 496 496), lower := (rows 51 14 7 8 16 32 64 128 256), losses := [] }

theorem u8905 : Upper (D 1) (R 1) [50,12,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8905
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8906 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 21 490 498 482 482 482 482), lower := (rows 51 14 21 8 16 32 64 128 256), losses := [] }

theorem u8906 : Upper (D 1) (R 1) [50,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8906
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8907 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 22 489 497 481 481 481 481), lower := (rows 51 14 22 8 16 32 64 128 256), losses := [] }

theorem u8907 : Upper (D 1) (R 1) [50,12,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8907
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8908 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 52 459 467 483 451 451 451), lower := (rows 51 14 52 8 16 32 64 128 256), losses := [] }

theorem u8908 : Upper (D 1) (R 1) [50,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8908
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8909_18 : Upper (D 1) (R 1) [50,12,65,18] 13 :=
  permutation_upper _ _ _ [50,12,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6330

theorem m8909_48 : Upper (D 1) (R 1) [50,12,65,48] 13 :=
  permutation_upper _ _ _ [50,12,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6334

def r8909 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8909 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8909 : Upper (D 1) (R 1) [50,12,65] 13 := by
  apply FastRouting.sound _ _ [50,12,65] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r8909 c8909
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8909_18
  · exact m8909_48
  · exact u6338
  · exact u6339
  · exact u6340
  · exact u6341
  · exact u6342
  · exact u6343
  · exact u6344
  · exact u6345
  · exact u6346

def b8910 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 51 14 70 505 497 497 497 497 497), lower := (rows 51 14 70 8 16 32 64 128 256), losses := [] }

theorem u8910 : Upper (D 1) (R 1) [50,12,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8910
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8911 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 491 499 483 483 483 483), lower := (rows 51 14 84 8 16 32 64 128 256), losses := [] }

theorem u8911 : Upper (D 1) (R 1) [50,12,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8911
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8912_3 : Upper (D 1) (R 1) [50,12,192,3] 13 :=
  permutation_upper _ _ _ [50,12,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6326

theorem m8912_17 : Upper (D 1) (R 1) [50,12,192,17] 13 :=
  permutation_upper _ _ _ [50,12,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6328

theorem m8912_18 : Upper (D 1) (R 1) [50,12,192,18] 13 :=
  permutation_upper _ _ _ [50,12,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6331

theorem m8912_48 : Upper (D 1) (R 1) [50,12,192,48] 13 :=
  permutation_upper _ _ _ [50,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6335

theorem m8912_65 : Upper (D 1) (R 1) [50,12,192,65] 13 :=
  permutation_upper _ _ _ [50,12,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6342

theorem m8912_66 : Upper (D 1) (R 1) [50,12,192,66] 13 :=
  permutation_upper _ _ _ [50,12,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6347

theorem m8912_80 : Upper (D 1) (R 1) [50,12,192,80] 13 :=
  permutation_upper _ _ _ [50,12,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6351

def r8912 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8912 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8912 : Upper (D 1) (R 1) [50,12,192] 13 := by
  apply FastRouting.sound _ _ [50,12,192] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192,257,258,272,320] r8912 c8912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8912_3
  · exact m8912_17
  · exact m8912_18
  · exact m8912_48
  · exact m8912_65
  · exact m8912_66
  · exact m8912_80
  · exact u6355
  · exact u6356
  · exact u6357
  · exact u6358
  · exact u6359

theorem m8913_18 : Upper (D 1) (R 1) [50,12,257,18] 13 :=
  permutation_upper _ _ _ [50,12,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6332

theorem m8913_48 : Upper (D 1) (R 1) [50,12,257,48] 13 :=
  permutation_upper _ _ _ [50,12,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6336

theorem m8913_66 : Upper (D 1) (R 1) [50,12,257,66] 13 :=
  permutation_upper _ _ _ [50,12,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6348

theorem m8913_80 : Upper (D 1) (R 1) [50,12,257,80] 13 :=
  permutation_upper _ _ _ [50,12,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6352

theorem m8913_192 : Upper (D 1) (R 1) [50,12,257,192] 13 :=
  permutation_upper _ _ _ [50,12,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6356

def r8913 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8913 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8913 : Upper (D 1) (R 1) [50,12,257] 13 := by
  apply FastRouting.sound _ _ [50,12,257] 13 (by decide) (choices 2) [18,48,66,80,192] r8913 c8913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m8913_18
  · exact m8913_48
  · exact m8913_66
  · exact m8913_80
  · exact m8913_192

def b8914 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 51 14 262 249 241 241 241 241 497), lower := (rows 51 14 262 8 16 32 64 128 256), losses := [] }

theorem u8914 : Upper (D 1) (R 1) [50,12,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8914
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8915 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 276 235 243 227 227 227 483), lower := (rows 51 14 276 8 16 32 64 128 256), losses := [] }

theorem u8915 : Upper (D 1) (R 1) [50,12,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8915
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8916_3 : Upper (D 1) (R 1) [50,12,320,3] 13 :=
  permutation_upper _ _ _ [50,12,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6327

theorem m8916_17 : Upper (D 1) (R 1) [50,12,320,17] 13 :=
  permutation_upper _ _ _ [50,12,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6329

theorem m8916_18 : Upper (D 1) (R 1) [50,12,320,18] 13 :=
  permutation_upper _ _ _ [50,12,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6333

theorem m8916_48 : Upper (D 1) (R 1) [50,12,320,48] 13 :=
  permutation_upper _ _ _ [50,12,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6337

theorem m8916_65 : Upper (D 1) (R 1) [50,12,320,65] 13 :=
  permutation_upper _ _ _ [50,12,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6345

theorem m8916_66 : Upper (D 1) (R 1) [50,12,320,66] 13 :=
  permutation_upper _ _ _ [50,12,66,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6349

theorem m8916_80 : Upper (D 1) (R 1) [50,12,320,80] 13 :=
  permutation_upper _ _ _ [50,12,80,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6353

theorem m8916_129 : Upper (D 1) (R 1) [50,12,320,129] 13 :=
  permutation_upper _ _ _ [50,12,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6346

theorem m8916_130 : Upper (D 1) (R 1) [50,12,320,130] 13 :=
  permutation_upper _ _ _ [50,12,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6350

theorem m8916_144 : Upper (D 1) (R 1) [50,12,320,144] 13 :=
  permutation_upper _ _ _ [50,12,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6354

theorem m8916_192 : Upper (D 1) (R 1) [50,12,320,192] 13 :=
  permutation_upper _ _ _ [50,12,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6359

def r8916 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8916 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8916 : Upper (D 1) (R 1) [50,12,320] 13 := by
  apply FastRouting.sound _ _ [50,12,320] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r8916 c8916
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8916_3
  · exact m8916_17
  · exact m8916_18
  · exact m8916_48
  · exact m8916_65
  · exact m8916_66
  · exact m8916_80
  · exact m8916_129
  · exact m8916_130
  · exact m8916_144
  · exact m8916_192

def b8917 : PairBound 9 := { available := 500, camps := [{ cop := 2, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 14 508 500 500 500 500 500), lower := (rows 51 67 14 8 16 32 64 128 256), losses := [] }

theorem u8917 : Upper (D 1) (R 1) [50,65,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8917
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8918 : PairBound 9 := { available := 492, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 22 492 508 492 492 492 492), lower := (rows 51 67 22 8 16 32 64 128 256), losses := [] }

theorem u8918 : Upper (D 1) (R 1) [50,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8918
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8919_6 : Upper (D 1) (R 1) [50,65,24,6] 13 :=
  permutation_upper _ _ _ [50,65,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6360

theorem m8919_34 : Upper (D 1) (R 1) [50,65,24,34] 13 :=
  permutation_upper _ _ _ [50,65,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6370

def r8919 : Route 9 := (fun mask => (mask,id))

def c8919 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u8919 : Upper (D 1) (R 1) [50,65,24] 13 := by
  apply FastRouting.sound _ _ [50,65,24] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,258,260,288,320,384] r8919 c8919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8919_6
  · exact m8919_34
  · exact u6380
  · exact u6381
  · exact u6382
  · exact u6383
  · exact u6384
  · exact u6385
  · exact u6386
  · exact u6387
  · exact u6388
  · exact u6389
  · exact u6390
  · exact u6391
  · exact u6392

def b8920 : PairBound 9 := { available := 462, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 52 462 478 494 462 462 462), lower := (rows 51 67 52 8 16 32 64 128 256), losses := [] }

theorem u8920 : Upper (D 1) (R 1) [50,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8920
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8921 : PairBound 9 := { available := 444, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 70 444 444 444 508 444 444), lower := (rows 51 67 70 8 16 32 64 128 256), losses := [] }

theorem u8921 : Upper (D 1) (R 1) [50,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8921
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8922_6 : Upper (D 1) (R 1) [50,65,72,6] 13 :=
  permutation_upper _ _ _ [50,65,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6361

theorem m8922_18 : Upper (D 1) (R 1) [50,65,72,18] 13 :=
  permutation_upper _ _ _ [50,65,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6371

theorem m8922_20 : Upper (D 1) (R 1) [50,65,72,20] 13 :=
  permutation_upper _ _ _ [50,65,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6382

theorem m8922_48 : Upper (D 1) (R 1) [50,65,72,48] 13 :=
  permutation_upper _ _ _ [50,65,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6393

def r8922 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8922 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8922 : Upper (D 1) (R 1) [50,65,72] 13 := by
  apply FastRouting.sound _ _ [50,65,72] 13 (by decide) (choices 2) [6,18,20,48,130,132,144,258,260,272,384] r8922 c8922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8922_6
  · exact m8922_18
  · exact m8922_20
  · exact m8922_48
  · exact u6404
  · exact u6405
  · exact u6406
  · exact u6407
  · exact u6408
  · exact u6409
  · exact u6410

theorem m8923_6 : Upper (D 1) (R 1) [50,65,80,6] 13 :=
  permutation_upper _ _ _ [50,65,10,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6362

theorem m8923_34 : Upper (D 1) (R 1) [50,65,80,34] 13 :=
  permutation_upper _ _ _ [50,65,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6372

theorem m8923_36 : Upper (D 1) (R 1) [50,65,80,36] 13 :=
  permutation_upper _ _ _ [50,65,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6383

def r8923 : Route 9 := (fun mask => (mask,id))

def c8923 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8923 : Upper (D 1) (R 1) [50,65,80] 13 := by
  apply FastRouting.sound _ _ [50,65,80] 13 (by decide) (choices 2) [6,34,36,130,132,160,258,260,288,384] r8923 c8923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8923_6
  · exact m8923_34
  · exact m8923_36
  · exact u6411
  · exact u6412
  · exact u6413
  · exact u6414
  · exact u6415
  · exact u6416
  · exact u6417

def b8924 : PairBound 9 := { available := 508, camps := [{ cop := 2, region := 376, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 134 508 508 508 508 508 508), lower := (rows 51 67 134 8 16 32 64 128 256), losses := [] }

theorem u8924 : Upper (D 1) (R 1) [50,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8924
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8925_6 : Upper (D 1) (R 1) [50,65,136,6] 13 :=
  permutation_upper _ _ _ [50,65,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6363

theorem m8925_18 : Upper (D 1) (R 1) [50,65,136,18] 13 :=
  permutation_upper _ _ _ [50,65,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6373

theorem m8925_20 : Upper (D 1) (R 1) [50,65,136,20] 13 :=
  permutation_upper _ _ _ [50,65,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6385

theorem m8925_48 : Upper (D 1) (R 1) [50,65,136,48] 13 :=
  permutation_upper _ _ _ [50,65,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6394

theorem m8925_66 : Upper (D 1) (R 1) [50,65,136,66] 13 :=
  permutation_upper _ _ _ [50,65,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6399

theorem m8925_68 : Upper (D 1) (R 1) [50,65,136,68] 13 :=
  permutation_upper _ _ _ [50,65,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6405

theorem m8925_80 : Upper (D 1) (R 1) [50,65,136,80] 13 :=
  permutation_upper _ _ _ [50,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6412

theorem m8925_130 : Upper (D 1) (R 1) [50,65,136,130] 13 :=
  permutation_upper _ _ _ [50,65,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6418

def r8925 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8925 : Nat → Fin 9 := (fun _ => 0)

theorem u8925 : Upper (D 1) (R 1) [50,65,136] 13 := by
  apply FastRouting.sound _ _ [50,65,136] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192,258,260,272,320,384] r8925 c8925
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8925_6
  · exact m8925_18
  · exact m8925_20
  · exact m8925_48
  · exact m8925_66
  · exact m8925_68
  · exact m8925_80
  · exact m8925_130
  · exact u6425
  · exact u6426
  · exact u6427
  · exact u6428
  · exact u6429
  · exact u6430
  · exact u6431
  · exact u6432

theorem m8926_6 : Upper (D 1) (R 1) [50,65,144,6] 13 :=
  permutation_upper _ _ _ [50,65,10,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6364

theorem m8926_34 : Upper (D 1) (R 1) [50,65,144,34] 13 :=
  permutation_upper _ _ _ [50,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6374

theorem m8926_36 : Upper (D 1) (R 1) [50,65,144,36] 13 :=
  permutation_upper _ _ _ [50,65,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6386

theorem m8926_66 : Upper (D 1) (R 1) [50,65,144,66] 13 :=
  permutation_upper _ _ _ [50,65,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6400

theorem m8926_68 : Upper (D 1) (R 1) [50,65,144,68] 13 :=
  permutation_upper _ _ _ [50,65,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6406

theorem m8926_96 : Upper (D 1) (R 1) [50,65,144,96] 13 :=
  permutation_upper _ _ _ [50,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6413

theorem m8926_130 : Upper (D 1) (R 1) [50,65,144,130] 13 :=
  permutation_upper _ _ _ [50,65,130,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6419

theorem m8926_132 : Upper (D 1) (R 1) [50,65,144,132] 13 :=
  permutation_upper _ _ _ [50,65,136,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6426

def r8926 : Route 9 := (fun mask => (mask,id))

def c8926 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u8926 : Upper (D 1) (R 1) [50,65,144] 13 := by
  apply FastRouting.sound _ _ [50,65,144] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,258,260,288,320,384] r8926 c8926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8926_6
  · exact m8926_34
  · exact m8926_36
  · exact m8926_66
  · exact m8926_68
  · exact m8926_96
  · exact m8926_130
  · exact m8926_132
  · exact u6433
  · exact u6434
  · exact u6435
  · exact u6436
  · exact u6437
  · exact u6438
  · exact u6439

theorem m8927_6 : Upper (D 1) (R 1) [50,65,192,6] 13 :=
  permutation_upper _ _ _ [50,65,10,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6365

theorem m8927_18 : Upper (D 1) (R 1) [50,65,192,18] 13 :=
  permutation_upper _ _ _ [50,65,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6375

theorem m8927_20 : Upper (D 1) (R 1) [50,65,192,20] 13 :=
  permutation_upper _ _ _ [50,65,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6387

theorem m8927_48 : Upper (D 1) (R 1) [50,65,192,48] 13 :=
  permutation_upper _ _ _ [50,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6395

theorem m8927_130 : Upper (D 1) (R 1) [50,65,192,130] 13 :=
  permutation_upper _ _ _ [50,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6420

theorem m8927_132 : Upper (D 1) (R 1) [50,65,192,132] 13 :=
  permutation_upper _ _ _ [50,65,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6427

theorem m8927_144 : Upper (D 1) (R 1) [50,65,192,144] 13 :=
  permutation_upper _ _ _ [50,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6434

def r8927 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8927 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8927 : Upper (D 1) (R 1) [50,65,192] 13 := by
  apply FastRouting.sound _ _ [50,65,192] 13 (by decide) (choices 2) [6,18,20,48,130,132,144,258,260,272,384] r8927 c8927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8927_6
  · exact m8927_18
  · exact m8927_20
  · exact m8927_48
  · exact m8927_130
  · exact m8927_132
  · exact m8927_144
  · exact u6440
  · exact u6441
  · exact u6442
  · exact u6443

def b8928 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 51 67 262 252 252 252 252 252 508), lower := (rows 51 67 262 8 16 32 64 128 256), losses := [] }

theorem u8928 : Upper (D 1) (R 1) [50,65,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8928
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8929_6 : Upper (D 1) (R 1) [50,65,264,6] 13 :=
  permutation_upper _ _ _ [50,65,10,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6366

theorem m8929_18 : Upper (D 1) (R 1) [50,65,264,18] 13 :=
  permutation_upper _ _ _ [50,65,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6376

theorem m8929_20 : Upper (D 1) (R 1) [50,65,264,20] 13 :=
  permutation_upper _ _ _ [50,65,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6389

theorem m8929_48 : Upper (D 1) (R 1) [50,65,264,48] 13 :=
  permutation_upper _ _ _ [50,65,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6396

theorem m8929_66 : Upper (D 1) (R 1) [50,65,264,66] 13 :=
  permutation_upper _ _ _ [50,65,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6401

theorem m8929_68 : Upper (D 1) (R 1) [50,65,264,68] 13 :=
  permutation_upper _ _ _ [50,65,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6408

theorem m8929_80 : Upper (D 1) (R 1) [50,65,264,80] 13 :=
  permutation_upper _ _ _ [50,65,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6415

theorem m8929_130 : Upper (D 1) (R 1) [50,65,264,130] 13 :=
  permutation_upper _ _ _ [50,65,130,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6421

theorem m8929_132 : Upper (D 1) (R 1) [50,65,264,132] 13 :=
  permutation_upper _ _ _ [50,65,136,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6429

theorem m8929_144 : Upper (D 1) (R 1) [50,65,264,144] 13 :=
  permutation_upper _ _ _ [50,65,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6436

theorem m8929_192 : Upper (D 1) (R 1) [50,65,264,192] 13 :=
  permutation_upper _ _ _ [50,65,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6441

def r8929 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8929 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8929 : Upper (D 1) (R 1) [50,65,264] 13 := by
  apply FastRouting.sound _ _ [50,65,264] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192] r8929 c8929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8929_6
  · exact m8929_18
  · exact m8929_20
  · exact m8929_48
  · exact m8929_66
  · exact m8929_68
  · exact m8929_80
  · exact m8929_130
  · exact m8929_132
  · exact m8929_144
  · exact m8929_192

theorem m8930_6 : Upper (D 1) (R 1) [50,65,272,6] 13 :=
  permutation_upper _ _ _ [50,65,10,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6367

theorem m8930_34 : Upper (D 1) (R 1) [50,65,272,34] 13 :=
  permutation_upper _ _ _ [50,65,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6377

theorem m8930_36 : Upper (D 1) (R 1) [50,65,272,36] 13 :=
  permutation_upper _ _ _ [50,65,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6390

theorem m8930_66 : Upper (D 1) (R 1) [50,65,272,66] 13 :=
  permutation_upper _ _ _ [50,65,66,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6402

theorem m8930_68 : Upper (D 1) (R 1) [50,65,272,68] 13 :=
  permutation_upper _ _ _ [50,65,72,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6409

theorem m8930_96 : Upper (D 1) (R 1) [50,65,272,96] 13 :=
  permutation_upper _ _ _ [50,65,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6416

theorem m8930_130 : Upper (D 1) (R 1) [50,65,272,130] 13 :=
  permutation_upper _ _ _ [50,65,130,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6422

theorem m8930_132 : Upper (D 1) (R 1) [50,65,272,132] 13 :=
  permutation_upper _ _ _ [50,65,136,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6430

theorem m8930_160 : Upper (D 1) (R 1) [50,65,272,160] 13 :=
  permutation_upper _ _ _ [50,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6437

theorem m8930_192 : Upper (D 1) (R 1) [50,65,272,192] 13 :=
  permutation_upper _ _ _ [50,65,192,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6442

def r8930 : Route 9 := (fun mask => (mask,id))

def c8930 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8930 : Upper (D 1) (R 1) [50,65,272] 13 := by
  apply FastRouting.sound _ _ [50,65,272] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r8930 c8930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8930_6
  · exact m8930_34
  · exact m8930_36
  · exact m8930_66
  · exact m8930_68
  · exact m8930_96
  · exact m8930_130
  · exact m8930_132
  · exact m8930_160
  · exact m8930_192

theorem m8931_6 : Upper (D 1) (R 1) [50,65,320,6] 13 :=
  permutation_upper _ _ _ [50,65,10,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6368

theorem m8931_18 : Upper (D 1) (R 1) [50,65,320,18] 13 :=
  permutation_upper _ _ _ [50,65,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6378

theorem m8931_20 : Upper (D 1) (R 1) [50,65,320,20] 13 :=
  permutation_upper _ _ _ [50,65,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6391

theorem m8931_48 : Upper (D 1) (R 1) [50,65,320,48] 13 :=
  permutation_upper _ _ _ [50,65,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6397

theorem m8931_130 : Upper (D 1) (R 1) [50,65,320,130] 13 :=
  permutation_upper _ _ _ [50,65,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6423

theorem m8931_132 : Upper (D 1) (R 1) [50,65,320,132] 13 :=
  permutation_upper _ _ _ [50,65,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6431

theorem m8931_144 : Upper (D 1) (R 1) [50,65,320,144] 13 :=
  permutation_upper _ _ _ [50,65,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6438

def r8931 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8931 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u8931 : Upper (D 1) (R 1) [50,65,320] 13 := by
  apply FastRouting.sound _ _ [50,65,320] 13 (by decide) (choices 2) [6,18,20,48,130,132,144] r8931 c8931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8931_6
  · exact m8931_18
  · exact m8931_20
  · exact m8931_48
  · exact m8931_130
  · exact m8931_132
  · exact m8931_144

theorem m8932_6 : Upper (D 1) (R 1) [50,65,384,6] 13 :=
  permutation_upper _ _ _ [50,65,10,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6369

theorem m8932_18 : Upper (D 1) (R 1) [50,65,384,18] 13 :=
  permutation_upper _ _ _ [50,65,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6379

theorem m8932_20 : Upper (D 1) (R 1) [50,65,384,20] 13 :=
  permutation_upper _ _ _ [50,65,24,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6392

theorem m8932_48 : Upper (D 1) (R 1) [50,65,384,48] 13 :=
  permutation_upper _ _ _ [50,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6398

theorem m8932_66 : Upper (D 1) (R 1) [50,65,384,66] 13 :=
  permutation_upper _ _ _ [50,65,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6403

theorem m8932_68 : Upper (D 1) (R 1) [50,65,384,68] 13 :=
  permutation_upper _ _ _ [50,65,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6410

theorem m8932_80 : Upper (D 1) (R 1) [50,65,384,80] 13 :=
  permutation_upper _ _ _ [50,65,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6417

theorem m8932_130 : Upper (D 1) (R 1) [50,65,384,130] 13 :=
  permutation_upper _ _ _ [50,65,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6424

theorem m8932_132 : Upper (D 1) (R 1) [50,65,384,132] 13 :=
  permutation_upper _ _ _ [50,65,136,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6432

theorem m8932_144 : Upper (D 1) (R 1) [50,65,384,144] 13 :=
  permutation_upper _ _ _ [50,65,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6439

theorem m8932_192 : Upper (D 1) (R 1) [50,65,384,192] 13 :=
  permutation_upper _ _ _ [50,65,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6443

def r8932 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8932 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8932 : Upper (D 1) (R 1) [50,65,384] 13 := by
  apply FastRouting.sound _ _ [50,65,384] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192] r8932 c8932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8932_6
  · exact m8932_18
  · exact m8932_20
  · exact m8932_48
  · exact m8932_66
  · exact m8932_68
  · exact m8932_80
  · exact m8932_130
  · exact m8932_132
  · exact m8932_144
  · exact m8932_192

def b8933 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 70 7 504 504 504 504 504 504), lower := (rows 51 70 7 8 16 32 64 128 256), losses := [] }

theorem u8933 : Upper (D 1) (R 1) [50,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8933
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8934 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8934 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8934 : Upper (D 1) (R 1) [50,68,9] 13 := by
  apply FastRouting.sound _ _ [50,68,9] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r8934 c8934
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6444
  · exact u6445
  · exact u6446
  · exact u6447
  · exact u6448
  · exact u6449
  · exact u6450
  · exact u6451
  · exact u6452
  · exact u6453
  · exact u6454

def b8935 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 14 505 497 497 497 497 497), lower := (rows 51 70 14 8 16 32 64 128 256), losses := [] }

theorem u8935 : Upper (D 1) (R 1) [50,68,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8935
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8936 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 21 490 506 490 490 490 490), lower := (rows 51 70 21 8 16 32 64 128 256), losses := [] }

theorem u8936 : Upper (D 1) (R 1) [50,68,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8936
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8937 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 70 22 489 505 489 489 489 489), lower := (rows 51 70 22 8 16 32 64 128 256), losses := [] }

theorem u8937 : Upper (D 1) (R 1) [50,68,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8937
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8938 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 28 491 499 483 483 483 483), lower := (rows 51 70 28 8 16 32 64 128 256), losses := [] }

theorem u8938 : Upper (D 1) (R 1) [50,68,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8938
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8939 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 52 459 475 491 459 459 459), lower := (rows 51 70 52 8 16 32 64 128 256), losses := [] }

theorem u8939 : Upper (D 1) (R 1) [50,68,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8939
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8939
end Delivery.IrregularNine14.P01
