import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0076
import IrregularNine14P01C0077

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7860 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 69 200 186 186 250 186 442), lower := (rows 263 50 69 200 16 32 64 128 256), losses := [] }

theorem u7860 : Upper (D 1) (R 1) [262,48,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7860
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7861 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 263 50 76 11 240 240 240 240 496), lower := (rows 263 50 76 11 16 32 64 128 256), losses := [] }

theorem u7861 : Upper (D 1) (R 1) [262,48,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7861
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7862 : PairBound 9 := { available := 226, camps := [], pairs := [(2,4)], upper := (rows 263 50 76 25 242 226 226 226 482), lower := (rows 263 50 76 25 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 12 8 0 35 67 131 259), good := (rows 487 482 76 493 0 32 64 128 256) }] }

theorem u7862 : Upper (D 1) (R 1) [262,48,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7862
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7863 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 263 50 76 26 241 225 225 225 481), lower := (rows 263 50 76 26 16 32 64 128 256), losses := [] }

theorem u7863 : Upper (D 1) (R 1) [262,48,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7863
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7864 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 263 50 76 56 211 227 195 195 451), lower := (rows 263 50 76 56 16 32 64 128 256), losses := [] }

theorem u7864 : Upper (D 1) (R 1) [262,48,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7864
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7865 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 263 50 76 73 178 178 242 178 434), lower := (rows 263 50 76 73 16 32 64 128 256), losses := [] }

theorem u7865 : Upper (D 1) (R 1) [262,48,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7865
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7866 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 263 50 76 74 177 177 241 177 433), lower := (rows 263 50 76 74 16 32 64 128 256), losses := [] }

theorem u7866 : Upper (D 1) (R 1) [262,48,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7866
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7867 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 263 50 76 88 179 163 227 163 419), lower := (rows 263 50 76 88 16 32 64 128 256), losses := [] }

theorem u7867 : Upper (D 1) (R 1) [262,48,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7867
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7868 : Route 9 := (fun mask => (mask,id))

def c7868 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7868 : Upper (D 1) (R 1) [262,48,72,129] 13 := by
  apply FastRouting.sound _ _ [262,48,72,129] 13 (by decide) (choices 1) [2,32,64,128] r7868 c7868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4573
  · exact u4574
  · exact u4575
  · exact u4576

def r7869 : Route 9 := (fun mask => (mask,id))

def c7869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7869 : Upper (D 1) (R 1) [262,48,72,130] 13 := by
  apply FastRouting.sound _ _ [262,48,72,130] 13 (by decide) (choices 1) [1,32,64,128] r7869 c7869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4577
  · exact u4578
  · exact u4579
  · exact u4580

def r7870 : Route 9 := (fun mask => (mask,id))

def c7870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7870 : Upper (D 1) (R 1) [262,48,72,144] 13 := by
  apply FastRouting.sound _ _ [262,48,72,144] 13 (by decide) (choices 1) [1,2,32,64,128] r7870 c7870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4581
  · exact u4582
  · exact u4583
  · exact u4584
  · exact u4585

def b7871 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 263 50 76 200 179 179 243 179 435), lower := (rows 263 50 76 200 16 32 64 128 256), losses := [] }

theorem u7871 : Upper (D 1) (R 1) [262,48,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7871
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7872 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 263 50 196 11 248 248 248 248 504), lower := (rows 263 50 196 11 16 32 64 128 256), losses := [] }

theorem u7872 : Upper (D 1) (R 1) [262,48,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7872
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7873 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7873 : Upper (D 1) (R 1) [262,48,192,17] 13 := by
  apply FastRouting.sound _ _ [262,48,192,17] 13 (by decide) (choices 1) [2,8,32,64] r7873 c7873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4586
  · exact u4587
  · exact u4588
  · exact u4589

def b7874 : PairBound 9 := { available := 233, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 263 50 196 26 249 233 233 233 489), lower := (rows 263 50 196 26 16 32 64 128 256), losses := [] }

theorem u7874 : Upper (D 1) (R 1) [262,48,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7874
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7875 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 263 50 196 56 219 235 203 203 459), lower := (rows 263 50 196 56 16 32 64 128 256), losses := [] }

theorem u7875 : Upper (D 1) (R 1) [262,48,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7875
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7876 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 196 73 186 186 250 186 442), lower := (rows 263 50 196 73 16 32 64 128 256), losses := [] }

theorem u7876 : Upper (D 1) (R 1) [262,48,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7876
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7877 : Route 9 := (fun mask => (mask,id))

def c7877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7877 : Upper (D 1) (R 1) [262,48,192,66] 13 := by
  apply FastRouting.sound _ _ [262,48,192,66] 13 (by decide) (choices 1) [1,8,32,128] r7877 c7877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4590
  · exact u4591
  · exact u4592
  · exact u4593

def r7878 : Route 9 := (fun mask => (mask,id))

def c7878 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7878 : Upper (D 1) (R 1) [262,48,192,80] 13 := by
  apply FastRouting.sound _ _ [262,48,192,80] 13 (by decide) (choices 1) [1,2,8,32,128] r7878 c7878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4594
  · exact u4595
  · exact u4596
  · exact u4597
  · exact u4598

def b7879 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 263 50 196 200 59 59 123 187 315), lower := (rows 263 50 196 200 16 32 64 128 256), losses := [] }

theorem u7879 : Upper (D 1) (R 1) [262,48,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7879
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7880 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 269 19 22 42 240 224 224 224 480), lower := (rows 269 19 22 42 16 32 64 128 256), losses := [] }

theorem u7880 : Upper (D 1) (R 1) [268,17,18,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7880
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7881 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 269 19 22 104 242 226 226 226 482), lower := (rows 269 19 22 104 16 32 64 128 256), losses := [] }

theorem u7881 : Upper (D 1) (R 1) [268,17,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7881
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7882 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 269 19 38 42 208 240 208 208 464), lower := (rows 269 19 38 42 16 32 64 128 256), losses := [] }

theorem u7882 : Upper (D 1) (R 1) [268,17,34,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7882
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7883 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 269 19 38 56 210 226 194 194 450), lower := (rows 269 19 38 56 16 32 64 128 256), losses := [] }

theorem u7883 : Upper (D 1) (R 1) [268,17,34,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7883
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m7884_64 : Upper (D 1) (R 1) [268,17,34,66,64] 13 :=
  permutation_upper _ _ _ [268,17,34,66,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4599

def r7884 : Route 9 := (fun mask => (mask,id))

def c7884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7884 : Upper (D 1) (R 1) [268,17,34,66] 13 := by
  apply FastRouting.sound _ _ [268,17,34,66] 13 (by decide) (choices 1) [32,64,128] r7884 c7884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4599
  · exact m7884_64
  · exact u4600

def b7885 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 269 19 38 88 242 226 226 226 482), lower := (rows 269 19 38 88 16 32 64 128 256), losses := [] }

theorem u7885 : Upper (D 1) (R 1) [268,17,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7885
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7886 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 269 19 38 104 210 242 210 210 466), lower := (rows 269 19 38 104 16 32 64 128 256), losses := [] }

theorem u7886 : Upper (D 1) (R 1) [268,17,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7886
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7887 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7887 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7887 : Upper (D 1) (R 1) [268,17,34,192] 13 := by
  apply FastRouting.sound _ _ [268,17,34,192] 13 (by decide) (choices 1) [2,32,64] r7887 c7887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4601
  · exact u4602
  · exact u4603

def b7888 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 269 19 52 104 210 226 194 194 450), lower := (rows 269 19 52 104 16 32 64 128 256), losses := [] }

theorem u7888 : Upper (D 1) (R 1) [268,17,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7888
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7889 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 269 19 52 200 242 226 226 226 482), lower := (rows 269 19 52 200 16 32 64 128 256), losses := [] }

theorem u7889 : Upper (D 1) (R 1) [268,17,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7889
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7890 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 269 19 100 104 146 178 210 146 402), lower := (rows 269 19 100 104 16 32 64 128 256), losses := [] }

theorem u7890 : Upper (D 1) (R 1) [268,17,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7890
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7891 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 269 19 100 168 210 242 210 210 466), lower := (rows 269 19 100 168 16 32 64 128 256), losses := [] }

theorem u7891 : Upper (D 1) (R 1) [268,17,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7891
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7892 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 269 50 7 26 240 224 224 224 480), lower := (rows 269 50 7 26 16 32 64 128 256), losses := [] }

theorem u7892 : Upper (D 1) (R 1) [268,48,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7892
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7893 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 269 50 7 56 210 226 194 194 450), lower := (rows 269 50 7 56 16 32 64 128 256), losses := [] }

theorem u7893 : Upper (D 1) (R 1) [268,48,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7893
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7894 : Route 9 := (fun mask => (mask,id))

def c7894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7894 : Upper (D 1) (R 1) [268,48,3,66] 13 := by
  apply FastRouting.sound _ _ [268,48,3,66] 13 (by decide) (choices 1) [32,64,128] r7894 c7894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4604
  · exact u4605
  · exact u4606

def r7895 : Route 9 := (fun mask => (mask,id))

def c7895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7895 : Upper (D 1) (R 1) [268,48,3,80] 13 := by
  apply FastRouting.sound _ _ [268,48,3,80] 13 (by decide) (choices 1) [2,32,64,128] r7895 c7895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4607
  · exact u4608
  · exact u4609
  · exact u4610

def r7896 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7896 : Upper (D 1) (R 1) [268,48,3,192] 13 := by
  apply FastRouting.sound _ _ [268,48,3,192] 13 (by decide) (choices 1) [2,32,64] r7896 c7896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4611
  · exact u4612
  · exact u4613

def b7897 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 269 50 21 74 242 226 226 226 482), lower := (rows 269 50 21 74 16 32 64 128 256), losses := [] }

theorem u7897 : Upper (D 1) (R 1) [268,48,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7897
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7898 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 269 50 21 104 210 226 194 194 450), lower := (rows 269 50 21 104 16 32 64 128 256), losses := [] }

theorem u7898 : Upper (D 1) (R 1) [268,48,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7898
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7899 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 269 50 21 200 242 226 226 226 482), lower := (rows 269 50 21 200 16 32 64 128 256), losses := [] }

theorem u7899 : Upper (D 1) (R 1) [268,48,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7899
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7900 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 269 50 22 73 242 226 226 226 482), lower := (rows 269 50 22 73 16 32 64 128 256), losses := [] }

theorem u7900 : Upper (D 1) (R 1) [268,48,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7900
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7901 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 269 50 22 74 241 225 225 225 481), lower := (rows 269 50 22 74 16 32 64 128 256), losses := [] }

theorem u7901 : Upper (D 1) (R 1) [268,48,18,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7902 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 269 50 22 104 211 227 195 195 451), lower := (rows 269 50 22 104 16 32 64 128 256), losses := [] }

theorem u7902 : Upper (D 1) (R 1) [268,48,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7902
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7903 : PairBound 9 := { available := 227, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 269 50 22 200 243 227 227 227 483), lower := (rows 269 50 22 200 16 32 64 128 256), losses := [] }

theorem u7903 : Upper (D 1) (R 1) [268,48,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7904 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 269 50 52 73 210 226 194 194 450), lower := (rows 269 50 52 73 16 32 64 128 256), losses := [] }

theorem u7904 : Upper (D 1) (R 1) [268,48,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7904
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7905 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 269 50 52 74 211 227 195 195 451), lower := (rows 269 50 52 74 16 32 64 128 256), losses := [] }

theorem u7905 : Upper (D 1) (R 1) [268,48,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7905
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7906 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 269 50 52 200 211 227 195 195 451), lower := (rows 269 50 52 200 16 32 64 128 256), losses := [] }

theorem u7906 : Upper (D 1) (R 1) [268,48,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7906
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7907 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 69 74 178 178 242 178 434), lower := (rows 269 50 69 74 16 32 64 128 256), losses := [] }

theorem u7907 : Upper (D 1) (R 1) [268,48,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7907
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7908 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 69 88 178 162 226 162 418), lower := (rows 269 50 69 88 16 32 64 128 256), losses := [] }

theorem u7908 : Upper (D 1) (R 1) [268,48,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7908
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7909 : Route 9 := (fun mask => (mask,id))

def c7909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7909 : Upper (D 1) (R 1) [268,48,65,130] 13 := by
  apply FastRouting.sound _ _ [268,48,65,130] 13 (by decide) (choices 1) [2,32,64,128] r7909 c7909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4614
  · exact u4615
  · exact u4616
  · exact u4617

def r7910 : Route 9 := (fun mask => (mask,id))

def c7910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7910 : Upper (D 1) (R 1) [268,48,65,144] 13 := by
  apply FastRouting.sound _ _ [268,48,65,144] 13 (by decide) (choices 1) [2,32,64,128] r7910 c7910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4618
  · exact u4619
  · exact u4620
  · exact u4621

def b7911 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 69 200 178 178 242 178 434), lower := (rows 269 50 69 200 16 32 64 128 256), losses := [] }

theorem u7911 : Upper (D 1) (R 1) [268,48,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7911
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7912 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 269 50 70 74 177 177 241 177 433), lower := (rows 269 50 70 74 16 32 64 128 256), losses := [] }

theorem u7912 : Upper (D 1) (R 1) [268,48,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7912
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7913 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 70 88 179 163 227 163 419), lower := (rows 269 50 70 88 16 32 64 128 256), losses := [] }

theorem u7913 : Upper (D 1) (R 1) [268,48,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7913
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m7914_128 : Upper (D 1) (R 1) [268,48,66,130,128] 13 :=
  permutation_upper _ _ _ [268,48,66,130,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4624

def r7914 : Route 9 := (fun mask => (mask,id))

def c7914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7914 : Upper (D 1) (R 1) [268,48,66,130] 13 := by
  apply FastRouting.sound _ _ [268,48,66,130] 13 (by decide) (choices 1) [1,32,64,128] r7914 c7914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4622
  · exact u4623
  · exact u4624
  · exact m7914_128

def r7915 : Route 9 := (fun mask => (mask,id))

def c7915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7915 : Upper (D 1) (R 1) [268,48,66,144] 13 := by
  apply FastRouting.sound _ _ [268,48,66,144] 13 (by decide) (choices 1) [1,2,32,64,128] r7915 c7915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4625
  · exact u4626
  · exact u4627
  · exact u4628
  · exact u4629

def b7916 : PairBound 9 := { available := 179, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 70 200 179 179 243 179 435), lower := (rows 269 50 70 200 16 32 64 128 256), losses := [] }

theorem u7916 : Upper (D 1) (R 1) [268,48,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7916
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7917 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 84 104 147 163 195 131 387), lower := (rows 269 50 84 104 16 32 64 128 256), losses := [] }

theorem u7917 : Upper (D 1) (R 1) [268,48,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7917
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7918 : Route 9 := (fun mask => (mask,id))

def c7918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7918 : Upper (D 1) (R 1) [268,48,80,160] 13 := by
  apply FastRouting.sound _ _ [268,48,80,160] 13 (by decide) (choices 1) [1,2,64,128] r7918 c7918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4630
  · exact u4631
  · exact u4632
  · exact u4633

def b7919 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 84 200 179 163 227 163 419), lower := (rows 269 50 84 200 16 32 64 128 256), losses := [] }

theorem u7919 : Upper (D 1) (R 1) [268,48,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7919
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7919
end Delivery.IrregularNine14.P01
