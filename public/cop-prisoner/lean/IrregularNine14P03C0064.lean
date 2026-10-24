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

def r3840 : Route 9 := (fun mask => (mask,id))

def c3840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3840 : Upper (D 3) (R 3) [34,260,65,129,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129,192] 13 (by decide) (choices 1) [1,8,16] r3840 c3840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1563
  · exact u1564
  · exact u1565

def b3841 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 152 152 97 97 225 353), lower := (rows 35 262 69 152 152 32 64 128 256), losses := [] }

theorem u3841 : Upper (D 3) (R 3) [34,260,65,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3841
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3842 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 152 176 105 73 201 329), lower := (rows 35 262 69 152 176 32 64 128 256), losses := [] }

theorem u3842 : Upper (D 3) (R 3) [34,260,65,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3842
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3843 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 152 208 41 105 169 297), lower := (rows 35 262 69 152 208 32 64 128 256), losses := [] }

theorem u3843 : Upper (D 3) (R 3) [34,260,65,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3843
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3844 : Route 9 := (fun mask => (mask,id))

def c3844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3844 : Upper (D 3) (R 3) [34,260,65,160,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,160,192] 13 (by decide) (choices 1) [1,8,16] r3844 c3844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1566
  · exact u1567
  · exact u1568

def b3845 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 25 49 225 193 193 449), lower := (rows 35 262 76 25 49 32 64 128 256), losses := [] }

theorem u3845 : Upper (D 3) (R 3) [34,260,72,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3845
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3846 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 76 25 81 161 225 161 417), lower := (rows 35 262 76 25 81 32 64 128 256), losses := [] }

theorem u3846 : Upper (D 3) (R 3) [34,260,72,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3846
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3847 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 25 112 161 193 129 385), lower := (rows 35 262 76 25 112 32 64 128 256), losses := [] }

theorem u3847 : Upper (D 3) (R 3) [34,260,72,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3847
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3848 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 76 25 145 225 225 225 481), lower := (rows 35 262 76 25 145 32 64 128 256), losses := [] }

theorem u3848 : Upper (D 3) (R 3) [34,260,72,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3848
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3849 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 76 25 176 225 193 193 449), lower := (rows 35 262 76 25 176 32 64 128 256), losses := [] }

theorem u3849 : Upper (D 3) (R 3) [34,260,72,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3849
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3850 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 25 208 161 225 161 417), lower := (rows 35 262 76 25 208 32 64 128 256), losses := [] }

theorem u3850 : Upper (D 3) (R 3) [34,260,72,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3850
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3851 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 76 137 49 241 209 209 465), lower := (rows 35 262 76 137 49 32 64 128 256), losses := [] }

theorem u3851 : Upper (D 3) (R 3) [34,260,72,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3851
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3852 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 137 81 177 241 177 433), lower := (rows 35 262 76 137 81 32 64 128 256), losses := [] }

theorem u3852 : Upper (D 3) (R 3) [34,260,72,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3852
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3853 : Route 9 := (fun mask => (mask,id))

def c3853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3853 : Upper (D 3) (R 3) [34,260,72,129,96] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,96] 13 (by decide) (choices 1) [1,16,128] r3853 c3853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1569
  · exact u1570
  · exact u1571

def b3854 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 76 137 145 113 113 241 369), lower := (rows 35 262 76 137 145 32 64 128 256), losses := [] }

theorem u3854 : Upper (D 3) (R 3) [34,260,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3854
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3855 : Route 9 := (fun mask => (mask,id))

def c3855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3855 : Upper (D 3) (R 3) [34,260,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,160] 13 (by decide) (choices 1) [1,16,64] r3855 c3855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1572
  · exact u1573
  · exact u1574

def r3856 : Route 9 := (fun mask => (mask,id))

def c3856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3856 : Upper (D 3) (R 3) [34,260,72,129,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,192] 13 (by decide) (choices 1) [1,16] r3856 c3856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1575
  · exact u1576

def b3857 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 76 152 49 225 193 193 449), lower := (rows 35 262 76 152 49 32 64 128 256), losses := [] }

theorem u3857 : Upper (D 3) (R 3) [34,260,72,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3857
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3858 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 152 81 161 225 161 417), lower := (rows 35 262 76 152 81 32 64 128 256), losses := [] }

theorem u3858 : Upper (D 3) (R 3) [34,260,72,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3858
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3859 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 152 112 161 193 129 385), lower := (rows 35 262 76 152 112 32 64 128 256), losses := [] }

theorem u3859 : Upper (D 3) (R 3) [34,260,72,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3859
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3860 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 76 152 145 97 97 225 353), lower := (rows 35 262 76 152 145 32 64 128 256), losses := [] }

theorem u3860 : Upper (D 3) (R 3) [34,260,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3860
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3861 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 76 152 176 97 65 193 321), lower := (rows 35 262 76 152 176 32 64 128 256), losses := [] }

theorem u3861 : Upper (D 3) (R 3) [34,260,72,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3861
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3862 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 76 152 208 33 97 161 289), lower := (rows 35 262 76 152 208 32 64 128 256), losses := [] }

theorem u3862 : Upper (D 3) (R 3) [34,260,72,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3862
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3863 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 196 25 25 225 225 225 481), lower := (rows 35 262 196 25 25 32 64 128 256), losses := [] }

theorem u3863 : Upper (D 3) (R 3) [34,260,192,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3863
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3864 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 25 49 233 201 201 457), lower := (rows 35 262 196 25 49 32 64 128 256), losses := [] }

theorem u3864 : Upper (D 3) (R 3) [34,260,192,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3864
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3865 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 25 56 225 193 193 449), lower := (rows 35 262 196 25 56 32 64 128 256), losses := [] }

theorem u3865 : Upper (D 3) (R 3) [34,260,192,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3865
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3866 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 196 25 81 169 233 169 425), lower := (rows 35 262 196 25 81 32 64 128 256), losses := [] }

theorem u3866 : Upper (D 3) (R 3) [34,260,192,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3866
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3867 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 196 25 88 161 225 161 417), lower := (rows 35 262 196 25 88 32 64 128 256), losses := [] }

theorem u3867 : Upper (D 3) (R 3) [34,260,192,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3867
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3868 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 196 25 112 169 201 137 393), lower := (rows 35 262 196 25 112 32 64 128 256), losses := [] }

theorem u3868 : Upper (D 3) (R 3) [34,260,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3868
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3869 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 196 25 208 41 105 169 297), lower := (rows 35 262 196 25 208 32 64 128 256), losses := [] }

theorem u3869 : Upper (D 3) (R 3) [34,260,192,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3869
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3870 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 196 41 88 177 209 145 401), lower := (rows 35 262 196 41 88 32 64 128 256), losses := [] }

theorem u3870 : Upper (D 3) (R 3) [34,260,192,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3870
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3871 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 56 81 169 201 137 393), lower := (rows 35 262 196 56 81 32 64 128 256), losses := [] }

theorem u3871 : Upper (D 3) (R 3) [34,260,192,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3871
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3872 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 196 56 88 161 193 129 385), lower := (rows 35 262 196 56 88 32 64 128 256), losses := [] }

theorem u3872 : Upper (D 3) (R 3) [34,260,192,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3872
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3873 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 196 56 208 41 73 137 265), lower := (rows 35 262 196 56 208 32 64 128 256), losses := [] }

theorem u3873 : Upper (D 3) (R 3) [34,260,192,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3873
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3874 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 196 73 152 49 113 177 305), lower := (rows 35 262 196 73 152 32 64 128 256), losses := [] }

theorem u3874 : Upper (D 3) (R 3) [34,260,192,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3874
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3875 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 196 73 176 57 89 153 281), lower := (rows 35 262 196 73 176 32 64 128 256), losses := [] }

theorem u3875 : Upper (D 3) (R 3) [34,260,192,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3875
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3876 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 196 88 152 33 97 161 289), lower := (rows 35 262 196 88 152 32 64 128 256), losses := [] }

theorem u3876 : Upper (D 3) (R 3) [34,260,192,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3876
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3877 : Route 9 := (fun mask => (mask,id))

def c3877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3877 : Upper (D 3) (R 3) [34,260,192,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,192,80,160] 13 (by decide) (choices 1) [1,8] r3877 c3877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1577
  · exact u1578

def b3878 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 112 177 209 145 401), lower := (rows 35 322 13 13 112 32 64 128 256), losses := [] }

theorem u3878 : Upper (D 3) (R 3) [34,320,9,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3878
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3879 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 145 240 240 240 496), lower := (rows 35 322 13 13 145 32 64 128 256), losses := [] }

theorem u3879 : Upper (D 3) (R 3) [34,320,9,5,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3879
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3880 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 176 241 209 209 465), lower := (rows 35 322 13 13 176 32 64 128 256), losses := [] }

theorem u3880 : Upper (D 3) (R 3) [34,320,9,5,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3880
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3881 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 208 177 241 177 433), lower := (rows 35 322 13 13 208 32 64 128 256), losses := [] }

theorem u3881 : Upper (D 3) (R 3) [34,320,9,5,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3881
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3882 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 25 52 225 193 193 449), lower := (rows 35 322 13 25 52 32 64 128 256), losses := [] }

theorem u3882 : Upper (D 3) (R 3) [34,320,9,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3882
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3883 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 25 84 161 225 161 417), lower := (rows 35 322 13 25 84 32 64 128 256), losses := [] }

theorem u3883 : Upper (D 3) (R 3) [34,320,9,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3883
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3884 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 25 112 165 197 133 389), lower := (rows 35 322 13 25 112 32 64 128 256), losses := [] }

theorem u3884 : Upper (D 3) (R 3) [34,320,9,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3884
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3885 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 25 145 228 228 228 484), lower := (rows 35 322 13 25 145 32 64 128 256), losses := [] }

theorem u3885 : Upper (D 3) (R 3) [34,320,9,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3885
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3886 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 25 148 225 225 225 481), lower := (rows 35 322 13 25 148 32 64 128 256), losses := [] }

theorem u3886 : Upper (D 3) (R 3) [34,320,9,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3886
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3887 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 25 176 229 197 197 453), lower := (rows 35 322 13 25 176 32 64 128 256), losses := [] }

theorem u3887 : Upper (D 3) (R 3) [34,320,9,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3887
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3888 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 25 208 165 229 165 421), lower := (rows 35 322 13 25 208 32 64 128 256), losses := [] }

theorem u3888 : Upper (D 3) (R 3) [34,320,9,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3888
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3889 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 28 49 225 193 193 449), lower := (rows 35 322 13 28 49 32 64 128 256), losses := [] }

theorem u3889 : Upper (D 3) (R 3) [34,320,9,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3889
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3890 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 28 81 161 225 161 417), lower := (rows 35 322 13 28 81 32 64 128 256), losses := [] }

theorem u3890 : Upper (D 3) (R 3) [34,320,9,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3890
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3891 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 28 112 161 193 129 385), lower := (rows 35 322 13 28 112 32 64 128 256), losses := [] }

theorem u3891 : Upper (D 3) (R 3) [34,320,9,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3891
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3892 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 28 145 225 225 225 481), lower := (rows 35 322 13 28 145 32 64 128 256), losses := [] }

theorem u3892 : Upper (D 3) (R 3) [34,320,9,20,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3892
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3893 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 13 28 176 225 193 193 449), lower := (rows 35 322 13 28 176 32 64 128 256), losses := [] }

theorem u3893 : Upper (D 3) (R 3) [34,320,9,20,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3893
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3894 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 28 208 161 225 161 417), lower := (rows 35 322 13 28 208 32 64 128 256), losses := [] }

theorem u3894 : Upper (D 3) (R 3) [34,320,9,20,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3894
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3895 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 84 177 209 145 401), lower := (rows 35 322 13 41 84 32 64 128 256), losses := [] }

theorem u3895 : Upper (D 3) (R 3) [34,320,9,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3895
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3896 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 145 244 212 212 468), lower := (rows 35 322 13 41 145 32 64 128 256), losses := [] }

theorem u3896 : Upper (D 3) (R 3) [34,320,9,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3896
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3897 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 148 241 209 209 465), lower := (rows 35 322 13 41 148 32 64 128 256), losses := [] }

theorem u3897 : Upper (D 3) (R 3) [34,320,9,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3897
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3898 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 208 181 213 149 405), lower := (rows 35 322 13 41 208 32 64 128 256), losses := [] }

theorem u3898 : Upper (D 3) (R 3) [34,320,9,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3898
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3899 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 44 145 241 209 209 465), lower := (rows 35 322 13 44 145 32 64 128 256), losses := [] }

theorem u3899 : Upper (D 3) (R 3) [34,320,9,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3899
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3899
end Delivery.IrregularNine14.P03
