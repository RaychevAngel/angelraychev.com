import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0086
import IrregularNine14P08C0087

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14880 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 208 35 99 163 291), lower := (rows 97 38 268 152 208 32 64 128 256), losses := [] }

theorem u14880 : Upper (D 8) (R 8) [96,36,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14881 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 168 81 179 211 147 403), lower := (rows 97 38 268 168 81 32 64 128 256), losses := [] }

theorem u14881 : Upper (D 8) (R 8) [96,36,264,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14882 : Route 9 := (fun mask => (mask,id))

def c14882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14882 : Upper (D 8) (R 8) [96,36,264,160,66] 13 := by
  apply FastRouting.sound _ _ [96,36,264,160,66] 13 (by decide) (choices 1) [1,16,128] r14882 c14882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5218
  · exact u5219
  · exact u5220

def r14883 : Route 9 := (fun mask => (mask,id))

def c14883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14883 : Upper (D 8) (R 8) [96,36,264,160,129] 13 := by
  apply FastRouting.sound _ _ [96,36,264,160,129] 13 (by decide) (choices 1) [1,2,16,64] r14883 c14883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5221
  · exact u5222
  · exact u5223
  · exact u5224

def b14884 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 168 146 113 81 209 337), lower := (rows 97 38 268 168 146 32 64 128 256), losses := [] }

theorem u14884 : Upper (D 8) (R 8) [96,36,264,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14885 : Route 9 := (fun mask => (mask,id))

def c14885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14885 : Upper (D 8) (R 8) [96,36,264,160,192] 13 := by
  apply FastRouting.sound _ _ [96,36,264,160,192] 13 (by decide) (choices 1) [1,2,16] r14885 c14885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5225
  · exact u5226
  · exact u5227

def r14886 : Route 9 := (fun mask => (mask,id))

def c14886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14886 : Upper (D 8) (R 8) [96,36,264,192,129] 13 := by
  apply FastRouting.sound _ _ [96,36,264,192,129] 13 (by decide) (choices 1) [1,2,16] r14886 c14886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5228
  · exact u5229
  · exact u5230

def b14887 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 200 146 49 113 177 305), lower := (rows 97 38 268 200 146 32 64 128 256), losses := [] }

theorem u14887 : Upper (D 8) (R 8) [96,36,264,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14888 : Route 9 := (fun mask => (mask,id))

def c14888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14888 : Upper (D 8) (R 8) [96,36,264,192,160] 13 := by
  apply FastRouting.sound _ _ [96,36,264,192,160] 13 (by decide) (choices 1) [1,2,16] r14888 c14888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5231
  · exact u5232
  · exact u5233

def b14889 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 292 74 145 185 217 153 409), lower := (rows 97 38 292 74 145 32 64 128 256), losses := [] }

theorem u14889 : Upper (D 8) (R 8) [96,36,288,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14890 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 292 74 152 177 209 145 401), lower := (rows 97 38 292 74 152 32 64 128 256), losses := [] }

theorem u14890 : Upper (D 8) (R 8) [96,36,288,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14891 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 292 88 145 171 203 139 395), lower := (rows 97 38 292 88 145 32 64 128 256), losses := [] }

theorem u14891 : Upper (D 8) (R 8) [96,36,288,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14892 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 292 88 146 169 201 137 393), lower := (rows 97 38 292 88 146 32 64 128 256), losses := [] }

theorem u14892 : Upper (D 8) (R 8) [96,36,288,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14893 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 292 137 146 121 89 217 345), lower := (rows 97 38 292 137 146 32 64 128 256), losses := [] }

theorem u14893 : Upper (D 8) (R 8) [96,36,288,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14894 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 292 137 208 59 91 155 283), lower := (rows 97 38 292 137 208 32 64 128 256), losses := [] }

theorem u14894 : Upper (D 8) (R 8) [96,36,288,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14895 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 292 138 208 57 89 153 281), lower := (rows 97 38 292 138 208 32 64 128 256), losses := [] }

theorem u14895 : Upper (D 8) (R 8) [96,36,288,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14896 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 324 137 145 58 122 186 314), lower := (rows 97 38 324 137 145 32 64 128 256), losses := [] }

theorem u14896 : Upper (D 8) (R 8) [96,36,320,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14897 : Route 9 := (fun mask => (mask,id))

def c14897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14897 : Upper (D 8) (R 8) [96,36,320,129,130] 13 := by
  apply FastRouting.sound _ _ [96,36,320,129,130] 13 (by decide) (choices 1) [1,8,16] r14897 c14897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5234
  · exact u5235
  · exact u5236

def b14898 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 324 137 152 51 115 179 307), lower := (rows 97 38 324 137 152 32 64 128 256), losses := [] }

theorem u14898 : Upper (D 8) (R 8) [96,36,320,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14899 : Route 9 := (fun mask => (mask,id))

def c14899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14899 : Upper (D 8) (R 8) [96,36,320,129,160] 13 := by
  apply FastRouting.sound _ _ [96,36,320,129,160] 13 (by decide) (choices 1) [1,2,8,16] r14899 c14899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5237
  · exact u5238
  · exact u5239
  · exact u5240

def b14900 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 324 138 152 49 113 177 305), lower := (rows 97 38 324 138 152 32 64 128 256), losses := [] }

theorem u14900 : Upper (D 8) (R 8) [96,36,320,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14901 : Route 9 := (fun mask => (mask,id))

def c14901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14901 : Upper (D 8) (R 8) [96,36,320,130,160] 13 := by
  apply FastRouting.sound _ _ [96,36,320,130,160] 13 (by decide) (choices 1) [1,8,16] r14901 c14901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5241
  · exact u5242
  · exact u5243

def b14902 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 324 152 152 35 99 163 291), lower := (rows 97 38 324 152 152 32 64 128 256), losses := [] }

theorem u14902 : Upper (D 8) (R 8) [96,36,320,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14903 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 324 152 176 43 75 139 267), lower := (rows 97 38 324 152 176 32 64 128 256), losses := [] }

theorem u14903 : Upper (D 8) (R 8) [96,36,320,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14904 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 388 73 145 58 122 186 314), lower := (rows 97 38 388 73 145 32 64 128 256), losses := [] }

theorem u14904 : Upper (D 8) (R 8) [96,36,384,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14905 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 388 73 152 51 115 179 307), lower := (rows 97 38 388 73 152 32 64 128 256), losses := [] }

theorem u14905 : Upper (D 8) (R 8) [96,36,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14906 : PairBound 9 := { available := 27, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 388 73 176 59 91 155 283), lower := (rows 97 38 388 73 176 32 64 128 256), losses := [] }

theorem u14906 : Upper (D 8) (R 8) [96,36,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14907 : Route 9 := (fun mask => (mask,id))

def c14907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14907 : Upper (D 8) (R 8) [96,36,384,66,129] 13 := by
  apply FastRouting.sound _ _ [96,36,384,66,129] 13 (by decide) (choices 1) [1,8,16] r14907 c14907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5244
  · exact u5245
  · exact u5246

def b14908 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 388 74 152 49 113 177 305), lower := (rows 97 38 388 74 152 32 64 128 256), losses := [] }

theorem u14908 : Upper (D 8) (R 8) [96,36,384,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14909 : Route 9 := (fun mask => (mask,id))

def c14909 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14909 : Upper (D 8) (R 8) [96,36,384,66,160] 13 := by
  apply FastRouting.sound _ _ [96,36,384,66,160] 13 (by decide) (choices 1) [1,8,16] r14909 c14909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5247
  · exact u5248
  · exact u5249

def r14910 : Route 9 := (fun mask => (mask,id))

def c14910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14910 : Upper (D 8) (R 8) [96,36,384,80,129] 13 := by
  apply FastRouting.sound _ _ [96,36,384,80,129] 13 (by decide) (choices 1) [1,2,8] r14910 c14910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5250
  · exact u5251
  · exact u5252

def b14911 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 388 88 146 41 105 169 297), lower := (rows 97 38 388 88 146 32 64 128 256), losses := [] }

theorem u14911 : Upper (D 8) (R 8) [96,36,384,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14912 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 388 88 152 35 99 163 291), lower := (rows 97 38 388 88 152 32 64 128 256), losses := [] }

theorem u14912 : Upper (D 8) (R 8) [96,36,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14913 : Route 9 := (fun mask => (mask,id))

def c14913 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14913 : Upper (D 8) (R 8) [96,36,384,80,160] 13 := by
  apply FastRouting.sound _ _ [96,36,384,80,160] 13 (by decide) (choices 1) [1,2,8] r14913 c14913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5253
  · exact u5254
  · exact u5255

def b14914 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 388 104 145 59 91 155 283), lower := (rows 97 38 388 104 145 32 64 128 256), losses := [] }

theorem u14914 : Upper (D 8) (R 8) [96,36,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14915 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 388 104 152 51 83 147 275), lower := (rows 97 38 388 104 152 32 64 128 256), losses := [] }

theorem u14915 : Upper (D 8) (R 8) [96,36,384,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14916 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 138 276 56 120 184 312), lower := (rows 97 67 133 138 276 32 64 128 256), losses := [] }

theorem u14916 : Upper (D 8) (R 8) [96,65,129,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14917 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 138 280 52 116 180 308), lower := (rows 97 67 133 138 280 32 64 128 256), losses := [] }

theorem u14917 : Upper (D 8) (R 8) [96,65,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14918 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 138 304 60 124 188 316), lower := (rows 97 67 133 138 304 32 64 128 256), losses := [] }

theorem u14918 : Upper (D 8) (R 8) [96,65,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14919 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 152 274 44 108 172 300), lower := (rows 97 67 133 152 274 32 64 128 256), losses := [] }

theorem u14919 : Upper (D 8) (R 8) [96,65,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14920 : PairBound 9 := { available := 46, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 152 304 46 110 174 302), lower := (rows 97 67 133 152 304 32 64 128 256), losses := [] }

theorem u14920 : Upper (D 8) (R 8) [96,65,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14921 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 168 274 60 124 188 316), lower := (rows 97 67 133 168 274 32 64 128 256), losses := [] }

theorem u14921 : Upper (D 8) (R 8) [96,65,129,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14922 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 168 276 58 122 186 314), lower := (rows 97 67 133 168 276 32 64 128 256), losses := [] }

theorem u14922 : Upper (D 8) (R 8) [96,65,129,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14923 : PairBound 9 := { available := 54, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 168 280 54 118 182 310), lower := (rows 97 67 133 168 280 32 64 128 256), losses := [] }

theorem u14923 : Upper (D 8) (R 8) [96,65,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14924 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 133 168 304 62 94 158 286), lower := (rows 97 67 133 168 304 32 64 128 256), losses := [] }

theorem u14924 : Upper (D 8) (R 8) [96,65,129,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14925 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 134 152 273 44 108 172 300), lower := (rows 97 67 134 152 273 32 64 128 256), losses := [] }

theorem u14925 : Upper (D 8) (R 8) [96,65,130,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14926 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 134 152 304 45 109 173 301), lower := (rows 97 67 134 152 304 32 64 128 256), losses := [] }

theorem u14926 : Upper (D 8) (R 8) [96,65,130,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14927 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 134 168 273 60 124 188 316), lower := (rows 97 67 134 168 273 32 64 128 256), losses := [] }

theorem u14927 : Upper (D 8) (R 8) [96,65,130,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14928 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 134 168 276 57 121 185 313), lower := (rows 97 67 134 168 276 32 64 128 256), losses := [] }

theorem u14928 : Upper (D 8) (R 8) [96,65,130,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14929 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 134 168 280 53 117 181 309), lower := (rows 97 67 134 168 280 32 64 128 256), losses := [] }

theorem u14929 : Upper (D 8) (R 8) [96,65,130,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14930 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 134 168 304 61 93 157 285), lower := (rows 97 67 134 168 304 32 64 128 256), losses := [] }

theorem u14930 : Upper (D 8) (R 8) [96,65,130,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14931 : PairBound 9 := { available := 54, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 140 265 176 54 118 182 310), lower := (rows 97 67 140 265 176 32 64 128 256), losses := [] }

theorem u14931 : Upper (D 8) (R 8) [96,65,136,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14932 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 140 266 176 53 117 181 309), lower := (rows 97 67 140 266 176 32 64 128 256), losses := [] }

theorem u14932 : Upper (D 8) (R 8) [96,65,136,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14933 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 444, targets := 64 }], pairs := [(2,6)], upper := (rows 97 67 140 296 176 55 87 151 279), lower := (rows 97 67 140 296 176 32 64 128 256), losses := [] }

theorem u14933 : Upper (D 8) (R 8) [96,65,136,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14934 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 70 133 137 274 56 120 184 312), lower := (rows 97 70 133 137 274 32 64 128 256), losses := [] }

theorem u14934 : Upper (D 8) (R 8) [96,68,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14935 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 70 133 137 280 50 114 178 306), lower := (rows 97 70 133 137 280 32 64 128 256), losses := [] }

theorem u14935 : Upper (D 8) (R 8) [96,68,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14936 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 70 133 137 304 58 122 186 314), lower := (rows 97 70 133 137 304 32 64 128 256), losses := [] }

theorem u14936 : Upper (D 8) (R 8) [96,68,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14937 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 138 273 56 120 184 312), lower := (rows 97 70 133 138 273 32 64 128 256), losses := [] }

theorem u14937 : Upper (D 8) (R 8) [96,68,129,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14938 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 138 280 49 113 177 305), lower := (rows 97 70 133 138 280 32 64 128 256), losses := [] }

theorem u14938 : Upper (D 8) (R 8) [96,68,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14939 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 133 138 304 57 121 185 313), lower := (rows 97 70 133 138 304 32 64 128 256), losses := [] }

theorem u14939 : Upper (D 8) (R 8) [96,68,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14939
end Delivery.IrregularNine14.P08
