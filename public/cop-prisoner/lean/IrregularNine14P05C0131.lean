import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0070
import IrregularNine14P05C0071

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7860 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 265 22 44 108 172 300), lower := (rows 19 98 133 265 22 32 64 128 256), losses := [] }

theorem u7860 : Upper (D 5) (R 5) [18,96,129,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7860
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m7861_8 : Upper (D 5) (R 5) [18,96,129,257,12,8] 13 :=
  permutation_upper _ _ _ [18,96,129,257,12,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4240

def r7861 : Route 9 := (fun mask => (mask,id))

def c7861 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7861 : Upper (D 5) (R 5) [18,96,129,257,12] 13 := by
  apply FastRouting.sound _ _ [18,96,129,257,12] 13 (by decide) (choices 1) [2,4,8] r7861 c7861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4239
  · exact u4240
  · exact m7861_8

def b7862 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 265 50 44 76 140 268), lower := (rows 19 98 133 265 50 32 64 128 256), losses := [] }

theorem u7862 : Upper (D 5) (R 5) [18,96,129,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7863 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 98 133 265 52 46 78 142 270), lower := (rows 19 98 133 265 52 32 64 128 256), losses := [] }

theorem u7863 : Upper (D 5) (R 5) [18,96,129,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7864 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 19 98 133 266 21 44 108 172 300), lower := (rows 19 98 133 266 21 32 64 128 256), losses := [] }

theorem u7864 : Upper (D 5) (R 5) [18,96,129,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7864
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7865 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 98 133 266 25 44 108 172 300), lower := (rows 19 98 133 266 25 32 64 128 256), losses := [] }

theorem u7865 : Upper (D 5) (R 5) [18,96,129,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7865
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7866 : Route 9 := (fun mask => (mask,id))

def c7866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7866 : Upper (D 5) (R 5) [18,96,129,258,12] 13 := by
  apply FastRouting.sound _ _ [18,96,129,258,12] 13 (by decide) (choices 1) [1,4,8] r7866 c7866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4241
  · exact u4242
  · exact u4243

def b7867 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 266 49 44 76 140 268), lower := (rows 19 98 133 266 49 32 64 128 256), losses := [] }

theorem u7867 : Upper (D 5) (R 5) [18,96,129,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7867
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7868 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 98 133 266 52 45 77 141 269), lower := (rows 19 98 133 266 52 32 64 128 256), losses := [] }

theorem u7868 : Upper (D 5) (R 5) [18,96,129,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7868
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7869 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 98 133 266 56 45 77 141 269), lower := (rows 19 98 133 266 56 32 64 128 256), losses := [] }

theorem u7869 : Upper (D 5) (R 5) [18,96,129,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7870 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 268 19 44 108 172 300), lower := (rows 19 98 133 268 19 32 64 128 256), losses := [] }

theorem u7870 : Upper (D 5) (R 5) [18,96,129,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7870
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7871 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 19 98 133 268 21 42 106 170 298), lower := (rows 19 98 133 268 21 32 64 128 256), losses := [] }

theorem u7871 : Upper (D 5) (R 5) [18,96,129,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7871
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7872 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 268 22 41 105 169 297), lower := (rows 19 98 133 268 22 32 64 128 256), losses := [] }

theorem u7872 : Upper (D 5) (R 5) [18,96,129,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7872
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7873 : PairBound 9 := { available := 46, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 133 268 25 46 110 174 302), lower := (rows 19 98 133 268 25 32 64 128 256), losses := [] }

theorem u7873 : Upper (D 5) (R 5) [18,96,129,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7873
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7874 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 268 26 45 109 173 301), lower := (rows 19 98 133 268 26 32 64 128 256), losses := [] }

theorem u7874 : Upper (D 5) (R 5) [18,96,129,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7874
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7875 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 98 133 268 28 43 107 171 299), lower := (rows 19 98 133 268 28 32 64 128 256), losses := [] }

theorem u7875 : Upper (D 5) (R 5) [18,96,129,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7875
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7876 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 268 49 46 78 142 270), lower := (rows 19 98 133 268 49 32 64 128 256), losses := [] }

theorem u7876 : Upper (D 5) (R 5) [18,96,129,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7876
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7877 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 268 50 45 77 141 269), lower := (rows 19 98 133 268 50 32 64 128 256), losses := [] }

theorem u7877 : Upper (D 5) (R 5) [18,96,129,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7877
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7878 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 98 133 268 52 43 75 139 267), lower := (rows 19 98 133 268 52 32 64 128 256), losses := [] }

theorem u7878 : Upper (D 5) (R 5) [18,96,129,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7878
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7879 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 98 133 268 56 47 79 143 271), lower := (rows 19 98 133 268 56 32 64 128 256), losses := [] }

theorem u7879 : Upper (D 5) (R 5) [18,96,129,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7879
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7880 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 296 19 44 76 140 268), lower := (rows 19 98 133 296 19 32 64 128 256), losses := [] }

theorem u7880 : Upper (D 5) (R 5) [18,96,129,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7880
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7881 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 19 98 133 296 21 46 78 142 270), lower := (rows 19 98 133 296 21 32 64 128 256), losses := [] }

theorem u7881 : Upper (D 5) (R 5) [18,96,129,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7881
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7882 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 133 296 22 45 77 141 269), lower := (rows 19 98 133 296 22 32 64 128 256), losses := [] }

theorem u7882 : Upper (D 5) (R 5) [18,96,129,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7882
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7883 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 98 133 296 25 46 78 142 270), lower := (rows 19 98 133 296 25 32 64 128 256), losses := [] }

theorem u7883 : Upper (D 5) (R 5) [18,96,129,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7883
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7884 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 133 296 26 45 77 141 269), lower := (rows 19 98 133 296 26 32 64 128 256), losses := [] }

theorem u7884 : Upper (D 5) (R 5) [18,96,129,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7884
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7885 : Route 9 := (fun mask => (mask,id))

def c7885 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7885 : Upper (D 5) (R 5) [18,96,129,288,12] 13 := by
  apply FastRouting.sound _ _ [18,96,129,288,12] 13 (by decide) (choices 1) [1,2,4,8] r7885 c7885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4244
  · exact u4245
  · exact u4246
  · exact u4247

def b7886 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 98 134 268 21 41 105 169 297), lower := (rows 19 98 134 268 21 32 64 128 256), losses := [] }

theorem u7886 : Upper (D 5) (R 5) [18,96,130,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7886
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7887 : Route 9 := (fun mask => (mask,id))

def c7887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7887 : Upper (D 5) (R 5) [18,96,130,260,9] 13 := by
  apply FastRouting.sound _ _ [18,96,130,260,9] 13 (by decide) (choices 1) [1,4,8] r7887 c7887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4248
  · exact u4249
  · exact u4250

def b7888 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 98 134 268 28 41 105 169 297), lower := (rows 19 98 134 268 28 32 64 128 256), losses := [] }

theorem u7888 : Upper (D 5) (R 5) [18,96,130,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7888
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7889 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 134 268 49 45 77 141 269), lower := (rows 19 98 134 268 49 32 64 128 256), losses := [] }

theorem u7889 : Upper (D 5) (R 5) [18,96,130,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7889
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7890 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 98 134 268 52 41 73 137 265), lower := (rows 19 98 134 268 52 32 64 128 256), losses := [] }

theorem u7890 : Upper (D 5) (R 5) [18,96,130,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7890
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7891 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 98 134 268 56 45 77 141 269), lower := (rows 19 98 134 268 56 32 64 128 256), losses := [] }

theorem u7891 : Upper (D 5) (R 5) [18,96,130,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7891
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7892 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 98 134 296 21 45 77 141 269), lower := (rows 19 98 134 296 21 32 64 128 256), losses := [] }

theorem u7892 : Upper (D 5) (R 5) [18,96,130,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7892
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7893 : Route 9 := (fun mask => (mask,id))

def c7893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7893 : Upper (D 5) (R 5) [18,96,130,288,9] 13 := by
  apply FastRouting.sound _ _ [18,96,130,288,9] 13 (by decide) (choices 1) [1,4,8] r7893 c7893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4251
  · exact u4252
  · exact u4253

def r7894 : Route 9 := (fun mask => (mask,id))

def c7894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7894 : Upper (D 5) (R 5) [18,96,130,288,12] 13 := by
  apply FastRouting.sound _ _ [18,96,130,288,12] 13 (by decide) (choices 1) [1,4,8] r7894 c7894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4254
  · exact u4255
  · exact u4256

def b7895 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 140 268 19 45 109 173 301), lower := (rows 19 98 140 268 19 32 64 128 256), losses := [] }

theorem u7895 : Upper (D 5) (R 5) [18,96,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7895
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7896 : Route 9 := (fun mask => (mask,id))

def c7896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7896 : Upper (D 5) (R 5) [18,96,136,260,5] 13 := by
  apply FastRouting.sound _ _ [18,96,136,260,5] 13 (by decide) (choices 1) [1,2,8] r7896 c7896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4257
  · exact u4258
  · exact u4259

def b7897 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 140 268 22 41 105 169 297), lower := (rows 19 98 140 268 22 32 64 128 256), losses := [] }

theorem u7897 : Upper (D 5) (R 5) [18,96,136,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7897
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7898 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 140 268 28 35 99 163 291), lower := (rows 19 98 140 268 28 32 64 128 256), losses := [] }

theorem u7898 : Upper (D 5) (R 5) [18,96,136,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7898
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7899 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 140 268 49 47 79 143 271), lower := (rows 19 98 140 268 49 32 64 128 256), losses := [] }

theorem u7899 : Upper (D 5) (R 5) [18,96,136,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7899
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7900 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 140 268 50 45 77 141 269), lower := (rows 19 98 140 268 50 32 64 128 256), losses := [] }

theorem u7900 : Upper (D 5) (R 5) [18,96,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7900
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7901 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 98 140 268 52 43 75 139 267), lower := (rows 19 98 140 268 52 32 64 128 256), losses := [] }

theorem u7901 : Upper (D 5) (R 5) [18,96,136,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7901
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7902 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 140 296 19 45 77 141 269), lower := (rows 19 98 140 296 19 32 64 128 256), losses := [] }

theorem u7902 : Upper (D 5) (R 5) [18,96,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7902
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7903 : Route 9 := (fun mask => (mask,id))

def c7903 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7903 : Upper (D 5) (R 5) [18,96,136,288,5] 13 := by
  apply FastRouting.sound _ _ [18,96,136,288,5] 13 (by decide) (choices 1) [1,2,4,8] r7903 c7903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4260
  · exact u4261
  · exact u4262
  · exact u4263

def b7904 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 98 140 296 22 45 77 141 269), lower := (rows 19 98 140 296 22 32 64 128 256), losses := [] }

theorem u7904 : Upper (D 5) (R 5) [18,96,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7904
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7905 : Route 9 := (fun mask => (mask,id))

def c7905 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7905 : Upper (D 5) (R 5) [18,96,136,288,9] 13 := by
  apply FastRouting.sound _ _ [18,96,136,288,9] 13 (by decide) (choices 1) [1,2,4] r7905 c7905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4264
  · exact u4265
  · exact u4266

def b7906 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 140 296 26 37 69 133 261), lower := (rows 19 98 140 296 26 32 64 128 256), losses := [] }

theorem u7906 : Upper (D 5) (R 5) [18,96,136,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7906
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7907 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 98 140 296 28 39 71 135 263), lower := (rows 19 98 140 296 28 32 64 128 256), losses := [] }

theorem u7907 : Upper (D 5) (R 5) [18,96,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7907
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7908 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 19 194 37 42 21 300 332 396 268), lower := (rows 19 194 37 42 21 32 64 128 256), losses := [] }

theorem u7908 : Upper (D 5) (R 5) [18,192,33,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7908
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7909 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 194 37 42 25 300 332 396 268), lower := (rows 19 194 37 42 25 32 64 128 256), losses := [] }

theorem u7909 : Upper (D 5) (R 5) [18,192,33,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7909
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7910 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 451, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 37 42 28 301 333 397 269), lower := (rows 19 194 37 42 28 32 64 128 256), losses := [] }

theorem u7910 : Upper (D 5) (R 5) [18,192,33,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7910
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7911 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 194 37 42 273 44 76 140 268), lower := (rows 19 194 37 42 273 32 64 128 256), losses := [] }

theorem u7911 : Upper (D 5) (R 5) [18,192,33,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7911
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7912 : Route 9 := (fun mask => (mask,id))

def c7912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7912 : Upper (D 5) (R 5) [18,192,33,34,260] 13 := by
  apply FastRouting.sound _ _ [18,192,33,34,260] 13 (by decide) (choices 1) [1,4,8] r7912 c7912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4267
  · exact u4268
  · exact u4269

def r7913 : Route 9 := (fun mask => (mask,id))

def c7913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7913 : Upper (D 5) (R 5) [18,192,33,34,264] 13 := by
  apply FastRouting.sound _ _ [18,192,33,34,264] 13 (by decide) (choices 1) [1,4,8] r7913 c7913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4270
  · exact u4271
  · exact u4272

def b7914 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 37 265 22 44 108 172 300), lower := (rows 19 194 37 265 22 32 64 128 256), losses := [] }

theorem u7914 : Upper (D 5) (R 5) [18,192,33,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7914
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7915 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 37 265 26 44 108 172 300), lower := (rows 19 194 37 265 26 32 64 128 256), losses := [] }

theorem u7915 : Upper (D 5) (R 5) [18,192,33,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7916 : Route 9 := (fun mask => (mask,id))

def c7916 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7916 : Upper (D 5) (R 5) [18,192,33,257,12] 13 := by
  apply FastRouting.sound _ _ [18,192,33,257,12] 13 (by decide) (choices 1) [2,4,8] r7916 c7916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4273
  · exact u4274
  · exact u4275

def b7917 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 300, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 194 37 265 50 44 76 140 268), lower := (rows 19 194 37 265 50 32 64 128 256), losses := [] }

theorem u7917 : Upper (D 5) (R 5) [18,192,33,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7917
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7918 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 37 265 52 46 78 142 270), lower := (rows 19 194 37 265 52 32 64 128 256), losses := [] }

theorem u7918 : Upper (D 5) (R 5) [18,192,33,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7918
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7919 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 19 194 37 265 56 46 78 142 270), lower := (rows 19 194 37 265 56 32 64 128 256), losses := [] }

theorem u7919 : Upper (D 5) (R 5) [18,192,33,257,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7919
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7919
end Delivery.IrregularNine14.P05
