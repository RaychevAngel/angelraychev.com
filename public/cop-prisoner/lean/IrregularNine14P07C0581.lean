import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0330
import IrregularNine14P07C0331

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34860 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 262 25 25 224 224 224 480), lower := (rows 35 70 262 25 25 32 64 128 256), losses := [] }

theorem u34860 : Upper (D 7) (R 7) [34,68,258,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34861 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 262 25 49 232 200 200 456), lower := (rows 35 70 262 25 49 32 64 128 256), losses := [] }

theorem u34861 : Upper (D 7) (R 7) [34,68,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34862 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 262 25 56 225 193 193 449), lower := (rows 35 70 262 25 56 32 64 128 256), losses := [] }

theorem u34862 : Upper (D 7) (R 7) [34,68,258,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34863 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 70 262 25 81 168 232 168 424), lower := (rows 35 70 262 25 81 32 64 128 256), losses := [] }

theorem u34863 : Upper (D 7) (R 7) [34,68,258,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34864 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 35 70 262 25 88 161 225 161 417), lower := (rows 35 70 262 25 88 32 64 128 256), losses := [] }

theorem u34864 : Upper (D 7) (R 7) [34,68,258,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34865 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 262 25 112 169 201 137 393), lower := (rows 35 70 262 25 112 32 64 128 256), losses := [] }

theorem u34865 : Upper (D 7) (R 7) [34,68,258,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34866 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 0, region := 216, targets := 2 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 262 25 145 232 232 232 488), lower := (rows 35 70 262 25 145 32 64 128 256), losses := [] }

theorem u34866 : Upper (D 7) (R 7) [34,68,258,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34867 : Route 9 := (fun mask => (mask,id))

def c34867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34867 : Upper (D 7) (R 7) [34,68,258,17,136] 13 := by
  apply FastRouting.sound _ _ [34,68,258,17,136] 13 (by decide) (choices 1) [1,64,128] r34867 c34867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19838
  · exact u19839
  · exact u19840

def b34868 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 262 25 176 233 201 201 457), lower := (rows 35 70 262 25 176 32 64 128 256), losses := [] }

theorem u34868 : Upper (D 7) (R 7) [34,68,258,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34869 : Route 9 := (fun mask => (mask,id))

def c34869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34869 : Upper (D 7) (R 7) [34,68,258,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,258,17,192] 13 (by decide) (choices 1) [1,8,128] r34869 c34869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19841
  · exact u19842
  · exact u19843

def b34870 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 262 41 81 184 216 152 408), lower := (rows 35 70 262 41 81 32 64 128 256), losses := [] }

theorem u34870 : Upper (D 7) (R 7) [34,68,258,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34871 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 262 41 88 177 209 145 401), lower := (rows 35 70 262 41 88 32 64 128 256), losses := [] }

theorem u34871 : Upper (D 7) (R 7) [34,68,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34872 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 262 41 145 248 216 216 472), lower := (rows 35 70 262 41 145 32 64 128 256), losses := [] }

theorem u34872 : Upper (D 7) (R 7) [34,68,258,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34873 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 262 41 152 241 209 209 465), lower := (rows 35 70 262 41 152 32 64 128 256), losses := [] }

theorem u34873 : Upper (D 7) (R 7) [34,68,258,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34874 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 262 41 208 185 217 153 409), lower := (rows 35 70 262 41 208 32 64 128 256), losses := [] }

theorem u34874 : Upper (D 7) (R 7) [34,68,258,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34875 : Route 9 := (fun mask => (mask,id))

def c34875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34875 : Upper (D 7) (R 7) [34,68,258,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,258,48,65] 13 (by decide) (choices 1) [1,8,128] r34875 c34875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19844
  · exact u19845
  · exact u19846

def b34876 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 262 56 88 161 193 129 385), lower := (rows 35 70 262 56 88 32 64 128 256), losses := [] }

theorem u34876 : Upper (D 7) (R 7) [34,68,258,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34877 : Route 9 := (fun mask => (mask,id))

def c34877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34877 : Upper (D 7) (R 7) [34,68,258,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,258,48,129] 13 (by decide) (choices 1) [1,8,64,128] r34877 c34877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19847
  · exact u19848
  · exact u19849
  · exact u19850

def b34878 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 262 56 152 225 193 193 449), lower := (rows 35 70 262 56 152 32 64 128 256), losses := [] }

theorem u34878 : Upper (D 7) (R 7) [34,68,258,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34879 : Route 9 := (fun mask => (mask,id))

def c34879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34879 : Upper (D 7) (R 7) [34,68,258,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,258,48,192] 13 (by decide) (choices 1) [1,8,128] r34879 c34879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19851
  · exact u19852
  · exact u19853

def r34880 : Route 9 := (fun mask => (mask,id))

def c34880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34880 : Upper (D 7) (R 7) [34,68,258,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,258,65,129] 13 (by decide) (choices 1) [8,16,128] r34880 c34880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19854
  · exact u19855
  · exact u19856

def r34881 : Route 9 := (fun mask => (mask,id))

def c34881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34881 : Upper (D 7) (R 7) [34,68,258,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,258,65,136] 13 (by decide) (choices 1) [1,16,128] r34881 c34881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19857
  · exact u19858
  · exact u19859

def r34882 : Route 9 := (fun mask => (mask,id))

def c34882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34882 : Upper (D 7) (R 7) [34,68,258,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,258,65,160] 13 (by decide) (choices 1) [1,8,16,128] r34882 c34882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19860
  · exact u19861
  · exact u19862
  · exact u19863

def r34883 : Route 9 := (fun mask => (mask,id))

def c34883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34883 : Upper (D 7) (R 7) [34,68,258,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,258,80,129] 13 (by decide) (choices 1) [1,8,128] r34883 c34883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19864
  · exact u19865
  · exact u19866

def b34884 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 35 70 262 88 152 161 225 161 417), lower := (rows 35 70 262 88 152 32 64 128 256), losses := [] }

theorem u34884 : Upper (D 7) (R 7) [34,68,258,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34885 : Route 9 := (fun mask => (mask,id))

def c34885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34885 : Upper (D 7) (R 7) [34,68,258,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,258,80,160] 13 (by decide) (choices 1) [1,8,128] r34885 c34885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19867
  · exact u19868
  · exact u19869

def r34886 : Route 9 := (fun mask => (mask,id))

def c34886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34886 : Upper (D 7) (R 7) [34,68,258,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,258,96,129] 13 (by decide) (choices 1) [1,8,16,128] r34886 c34886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19870
  · exact u19871
  · exact u19872
  · exact u19873

def r34887 : Route 9 := (fun mask => (mask,id))

def c34887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34887 : Upper (D 7) (R 7) [34,68,258,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,258,96,136] 13 (by decide) (choices 1) [1,16,128] r34887 c34887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19874
  · exact u19875
  · exact u19876

def b34888 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 16, targets := 96 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 262 137 145 120 120 248 376), lower := (rows 35 70 262 137 145 32 64 128 256), losses := [] }

theorem u34888 : Upper (D 7) (R 7) [34,68,258,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34889 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 35 70 262 137 152 113 113 241 369), lower := (rows 35 70 262 137 152 32 64 128 256), losses := [] }

theorem u34889 : Upper (D 7) (R 7) [34,68,258,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34890 : Route 9 := (fun mask => (mask,id))

def c34890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34890 : Upper (D 7) (R 7) [34,68,258,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,258,129,160] 13 (by decide) (choices 1) [1,8,16,64] r34890 c34890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19877
  · exact u19878
  · exact u19879
  · exact u19880

def r34891 : Route 9 := (fun mask => (mask,id))

def c34891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34891 : Upper (D 7) (R 7) [34,68,258,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,258,129,192] 13 (by decide) (choices 1) [1,8,16] r34891 c34891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19881
  · exact u19882
  · exact u19883

def b34892 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 262 152 152 97 97 225 353), lower := (rows 35 70 262 152 152 32 64 128 256), losses := [] }

theorem u34892 : Upper (D 7) (R 7) [34,68,258,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34893 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 262 152 176 105 73 201 329), lower := (rows 35 70 262 152 176 32 64 128 256), losses := [] }

theorem u34893 : Upper (D 7) (R 7) [34,68,258,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34894 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 262 152 208 41 105 169 297), lower := (rows 35 70 262 152 208 32 64 128 256), losses := [] }

theorem u34894 : Upper (D 7) (R 7) [34,68,258,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34895 : Route 9 := (fun mask => (mask,id))

def c34895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34895 : Upper (D 7) (R 7) [34,68,258,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,258,160,192] 13 (by decide) (choices 1) [1,8,16] r34895 c34895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19884
  · exact u19885
  · exact u19886

def b34896 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 268 25 19 224 224 224 480), lower := (rows 35 70 268 25 19 32 64 128 256), losses := [] }

theorem u34896 : Upper (D 7) (R 7) [34,68,264,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34897 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 268 25 49 226 194 194 450), lower := (rows 35 70 268 25 49 32 64 128 256), losses := [] }

theorem u34897 : Upper (D 7) (R 7) [34,68,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34898 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 268 25 50 225 193 193 449), lower := (rows 35 70 268 25 50 32 64 128 256), losses := [] }

theorem u34898 : Upper (D 7) (R 7) [34,68,264,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34899 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 268 25 81 162 226 162 418), lower := (rows 35 70 268 25 81 32 64 128 256), losses := [] }

theorem u34899 : Upper (D 7) (R 7) [34,68,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34900 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 268 25 82 161 225 161 417), lower := (rows 35 70 268 25 82 32 64 128 256), losses := [] }

theorem u34900 : Upper (D 7) (R 7) [34,68,264,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34901 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 35 70 268 25 112 163 195 131 387), lower := (rows 35 70 268 25 112 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 35 0 131 259), good := (rows 419 423 268 445 48 32 0 128 256) }] }

theorem u34901 : Upper (D 7) (R 7) [34,68,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34902 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 268 25 145 226 226 226 482), lower := (rows 35 70 268 25 145 32 64 128 256), losses := [] }

theorem u34902 : Upper (D 7) (R 7) [34,68,264,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34903 : Route 9 := (fun mask => (mask,id))

def c34903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34903 : Upper (D 7) (R 7) [34,68,264,17,130] 13 := by
  apply FastRouting.sound _ _ [34,68,264,17,130] 13 (by decide) (choices 1) [1,64,128] r34903 c34903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19887
  · exact u19888
  · exact u19889

def r34904 : Route 9 := (fun mask => (mask,id))

def c34904 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34904 : Upper (D 7) (R 7) [34,68,264,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,17,160] 13 (by decide) (choices 1) [1,2,64,128] r34904 c34904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19890
  · exact u19891
  · exact u19892
  · exact u19893

def r34905 : Route 9 := (fun mask => (mask,id))

def c34905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34905 : Upper (D 7) (R 7) [34,68,264,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,17,192] 13 (by decide) (choices 1) [1,2,128] r34905 c34905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19894
  · exact u19895
  · exact u19896

def b34906 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 268 26 49 225 193 193 449), lower := (rows 35 70 268 26 49 32 64 128 256), losses := [] }

theorem u34906 : Upper (D 7) (R 7) [34,68,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34907 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,1),(2,6),(4,1)], upper := (rows 35 70 268 26 81 161 225 161 417), lower := (rows 35 70 268 26 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 497 68 268 508 497 32 64 128 256) }] }

theorem u34907 : Upper (D 7) (R 7) [34,68,264,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34908 : Route 9 := (fun mask => (mask,id))

def c34908 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34908 : Upper (D 7) (R 7) [34,68,264,18,96] 13 := by
  apply FastRouting.sound _ _ [34,68,264,18,96] 13 (by decide) (choices 1) [1,128] r34908 c34908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19897
  · exact u19898

def r34909 : Route 9 := (fun mask => (mask,id))

def c34909 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34909 : Upper (D 7) (R 7) [34,68,264,18,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,18,129] 13 (by decide) (choices 1) [1,64,128] r34909 c34909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19899
  · exact u19900
  · exact u19901

def r34910 : Route 9 := (fun mask => (mask,id))

def c34910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34910 : Upper (D 7) (R 7) [34,68,264,18,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,18,160] 13 (by decide) (choices 1) [1,64,128] r34910 c34910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19902
  · exact u19903
  · exact u19904

def r34911 : Route 9 := (fun mask => (mask,id))

def c34911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34911 : Upper (D 7) (R 7) [34,68,264,18,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,18,192] 13 (by decide) (choices 1) [1,128] r34911 c34911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19905
  · exact u19906

def b34912 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 268 56 19 225 193 193 449), lower := (rows 35 70 268 56 19 32 64 128 256), losses := [] }

theorem u34912 : Upper (D 7) (R 7) [34,68,264,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34913 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 35 70 268 56 81 163 195 131 387), lower := (rows 35 70 268 56 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 35 0 131 259), good := (rows 419 423 268 60 445 32 0 128 256) }] }

theorem u34913 : Upper (D 7) (R 7) [34,68,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34914 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 268 56 82 161 193 129 385), lower := (rows 35 70 268 56 82 32 64 128 256), losses := [] }

theorem u34914 : Upper (D 7) (R 7) [34,68,264,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34915 : Route 9 := (fun mask => (mask,id))

def c34915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34915 : Upper (D 7) (R 7) [34,68,264,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,48,129] 13 (by decide) (choices 1) [1,2,64,128] r34915 c34915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19907
  · exact u19908
  · exact u19909
  · exact u19910

def r34916 : Route 9 := (fun mask => (mask,id))

def c34916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34916 : Upper (D 7) (R 7) [34,68,264,48,130] 13 := by
  apply FastRouting.sound _ _ [34,68,264,48,130] 13 (by decide) (choices 1) [1,64,128] r34916 c34916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19911
  · exact u19912
  · exact u19913

def r34917 : Route 9 := (fun mask => (mask,id))

def c34917 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34917 : Upper (D 7) (R 7) [34,68,264,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,264,48,192] 13 (by decide) (choices 1) [1,2,128] r34917 c34917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19914
  · exact u19915
  · exact u19916

def b34918 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 268 73 19 176 240 176 432), lower := (rows 35 70 268 73 19 32 64 128 256), losses := [] }

theorem u34918 : Upper (D 7) (R 7) [34,68,264,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34919 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 268 73 49 178 210 146 402), lower := (rows 35 70 268 73 49 32 64 128 256), losses := [] }

theorem u34919 : Upper (D 7) (R 7) [34,68,264,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34919
end Delivery.IrregularNine14.P07
