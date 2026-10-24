import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0067
import IrregularNine14P05C0068

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7680 : Route 9 := (fun mask => (mask,id))

def c7680 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7680 : Upper (D 5) (R 5) [18,68,136,33,264] 13 := by
  apply FastRouting.sound _ _ [18,68,136,33,264] 13 (by decide) (choices 1) [1,2,4] r7680 c7680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4047
  · exact u4048
  · exact u4049

def b7681 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 19 70 140 41 304 47 79 143 271), lower := (rows 19 70 140 41 304 32 64 128 256), losses := [] }

theorem u7681 : Upper (D 5) (R 5) [18,68,136,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7681
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7682 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 42 21 297 361 425 297), lower := (rows 19 70 140 42 21 32 64 128 256), losses := [] }

theorem u7682 : Upper (D 5) (R 5) [18,68,136,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7682
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7683 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 140 42 25 293 357 421 293), lower := (rows 19 70 140 42 25 32 64 128 256), losses := [] }

theorem u7683 : Upper (D 5) (R 5) [18,68,136,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7683
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7684 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 42 28 289 353 417 289), lower := (rows 19 70 140 42 28 32 64 128 256), losses := [] }

theorem u7684 : Upper (D 5) (R 5) [18,68,136,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7684
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7685 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 17, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 140 42 49 301 333 397 269), lower := (rows 19 70 140 42 49 32 64 128 256), losses := [] }

theorem u7685 : Upper (D 5) (R 5) [18,68,136,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7685
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7686 : Route 9 := (fun mask => (mask,id))

def c7686 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7686 : Upper (D 5) (R 5) [18,68,136,34,36] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34,36] 13 (by decide) (choices 1) [1,8,256] r7686 c7686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4050
  · exact u4051
  · exact u4052

def b7687 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 140 42 56 293 325 389 261), lower := (rows 19 70 140 42 56 32 64 128 256), losses := [] }

theorem u7687 : Upper (D 5) (R 5) [18,68,136,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7688 : Route 9 := (fun mask => (mask,id))

def c7688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7688 : Upper (D 5) (R 5) [18,68,136,34,257] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34,257] 13 (by decide) (choices 1) [1,4,8] r7688 c7688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4053
  · exact u4054
  · exact u4055

def r7689 : Route 9 := (fun mask => (mask,id))

def c7689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7689 : Upper (D 5) (R 5) [18,68,136,34,260] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34,260] 13 (by decide) (choices 1) [1,8] r7689 c7689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4056
  · exact u4057

def r7690 : Route 9 := (fun mask => (mask,id))

def c7690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7690 : Upper (D 5) (R 5) [18,68,136,34,264] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34,264] 13 (by decide) (choices 1) [1,4] r7690 c7690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4058
  · exact u4059

def r7691 : Route 9 := (fun mask => (mask,id))

def c7691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7691 : Upper (D 5) (R 5) [18,68,136,34,288] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34,288] 13 (by decide) (choices 1) [1,4,8] r7691 c7691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4060
  · exact u4061
  · exact u4062

def b7692 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 19 297 361 425 297), lower := (rows 19 70 140 44 19 32 64 128 256), losses := [] }

theorem u7692 : Upper (D 5) (R 5) [18,68,136,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7692
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7693 : Route 9 := (fun mask => (mask,id))

def c7693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7693 : Upper (D 5) (R 5) [18,68,136,36,9] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,9] 13 (by decide) (choices 1) [1,2,256] r7693 c7693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4063
  · exact u4064
  · exact u4065

def b7694 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 140 44 26 289 353 417 289), lower := (rows 19 70 140 44 26 32 64 128 256), losses := [] }

theorem u7694 : Upper (D 5) (R 5) [18,68,136,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7695 : Route 9 := (fun mask => (mask,id))

def c7695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7695 : Upper (D 5) (R 5) [18,68,136,36,33] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,33] 13 (by decide) (choices 1) [1,2,8,256] r7695 c7695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4066
  · exact u4067
  · exact u4068
  · exact u4069

def b7696 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 50 297 329 393 265), lower := (rows 19 70 140 44 50 32 64 128 256), losses := [] }

theorem u7696 : Upper (D 5) (R 5) [18,68,136,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7697 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 44 56 291 323 387 259), lower := (rows 19 70 140 44 56 32 64 128 256), losses := [] }

theorem u7697 : Upper (D 5) (R 5) [18,68,136,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7697
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7698 : Route 9 := (fun mask => (mask,id))

def c7698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7698 : Upper (D 5) (R 5) [18,68,136,36,257] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,257] 13 (by decide) (choices 1) [1,2,8] r7698 c7698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4070
  · exact u4071
  · exact u4072

def b7699 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 274 41 105 169 297), lower := (rows 19 70 140 44 274 32 64 128 256), losses := [] }

theorem u7699 : Upper (D 5) (R 5) [18,68,136,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7699
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7700 : Route 9 := (fun mask => (mask,id))

def c7700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7700 : Upper (D 5) (R 5) [18,68,136,36,264] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,264] 13 (by decide) (choices 1) [1,2] r7700 c7700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4073
  · exact u4074

def r7701 : Route 9 := (fun mask => (mask,id))

def c7701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7701 : Upper (D 5) (R 5) [18,68,136,36,288] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36,288] 13 (by decide) (choices 1) [1,2,8] r7701 c7701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4075
  · exact u4076
  · exact u4077

def b7702 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 265 19 44 108 172 300), lower := (rows 19 70 140 265 19 32 64 128 256), losses := [] }

theorem u7702 : Upper (D 5) (R 5) [18,68,136,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7702
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7703 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 265 21 42 106 170 298), lower := (rows 19 70 140 265 21 32 64 128 256), losses := [] }

theorem u7703 : Upper (D 5) (R 5) [18,68,136,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7703
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7704 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 265 22 41 105 169 297), lower := (rows 19 70 140 265 22 32 64 128 256), losses := [] }

theorem u7704 : Upper (D 5) (R 5) [18,68,136,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7704
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7705 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 140 265 25 38 102 166 294), lower := (rows 19 70 140 265 25 32 64 128 256), losses := [] }

theorem u7705 : Upper (D 5) (R 5) [18,68,136,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7705
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7706 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 265 26 37 101 165 293), lower := (rows 19 70 140 265 26 32 64 128 256), losses := [] }

theorem u7706 : Upper (D 5) (R 5) [18,68,136,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7706
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7707 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 265 28 35 99 163 291), lower := (rows 19 70 140 265 28 32 64 128 256), losses := [] }

theorem u7707 : Upper (D 5) (R 5) [18,68,136,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7707
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7708 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 265 49 46 110 174 302), lower := (rows 19 70 140 265 49 32 64 128 256), losses := [] }

theorem u7708 : Upper (D 5) (R 5) [18,68,136,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7708
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7709 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 265 50 45 109 173 301), lower := (rows 19 70 140 265 50 32 64 128 256), losses := [] }

theorem u7709 : Upper (D 5) (R 5) [18,68,136,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7709
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7710 : Route 9 := (fun mask => (mask,id))

def c7710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7710 : Upper (D 5) (R 5) [18,68,136,257,36] 13 := by
  apply FastRouting.sound _ _ [18,68,136,257,36] 13 (by decide) (choices 1) [1,2,8] r7710 c7710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4078
  · exact u4079
  · exact u4080

def r7711 : Route 9 := (fun mask => (mask,id))

def c7711 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7711 : Upper (D 5) (R 5) [18,68,136,257,40] 13 := by
  apply FastRouting.sound _ _ [18,68,136,257,40] 13 (by decide) (choices 1) [1,2,4] r7711 c7711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4081
  · exact u4082
  · exact u4083

def b7712 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 266 21 41 105 169 297), lower := (rows 19 70 140 266 21 32 64 128 256), losses := [] }

theorem u7712 : Upper (D 5) (R 5) [18,68,136,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7712
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7713 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 140 266 25 37 101 165 293), lower := (rows 19 70 140 266 25 32 64 128 256), losses := [] }

theorem u7713 : Upper (D 5) (R 5) [18,68,136,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7713
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7714 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 266 28 33 97 161 289), lower := (rows 19 70 140 266 28 32 64 128 256), losses := [] }

theorem u7714 : Upper (D 5) (R 5) [18,68,136,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7714
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7715 : Route 9 := (fun mask => (mask,id))

def c7715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7715 : Upper (D 5) (R 5) [18,68,136,258,33] 13 := by
  apply FastRouting.sound _ _ [18,68,136,258,33] 13 (by decide) (choices 1) [1,4,8] r7715 c7715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4084
  · exact u4085
  · exact u4086

def r7716 : Route 9 := (fun mask => (mask,id))

def c7716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7716 : Upper (D 5) (R 5) [18,68,136,258,36] 13 := by
  apply FastRouting.sound _ _ [18,68,136,258,36] 13 (by decide) (choices 1) [1,8] r7716 c7716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4087
  · exact u4088

def r7717 : Route 9 := (fun mask => (mask,id))

def c7717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7717 : Upper (D 5) (R 5) [18,68,136,258,40] 13 := by
  apply FastRouting.sound _ _ [18,68,136,258,40] 13 (by decide) (choices 1) [1,4] r7717 c7717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4089
  · exact u4090

def b7718 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 268 19 41 105 169 297), lower := (rows 19 70 140 268 19 32 64 128 256), losses := [] }

theorem u7718 : Upper (D 5) (R 5) [18,68,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7718
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7719 : Route 9 := (fun mask => (mask,id))

def c7719 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7719 : Upper (D 5) (R 5) [18,68,136,260,9] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260,9] 13 (by decide) (choices 1) [1,2] r7719 c7719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4091
  · exact u4092

def b7720 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 70 140 268 26 33 97 161 289), lower := (rows 19 70 140 268 26 32 64 128 256), losses := [] }

theorem u7720 : Upper (D 5) (R 5) [18,68,136,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7720
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7721 : Route 9 := (fun mask => (mask,id))

def c7721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7721 : Upper (D 5) (R 5) [18,68,136,260,33] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260,33] 13 (by decide) (choices 1) [1,2,8] r7721 c7721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4093
  · exact u4094
  · exact u4095

def b7722 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 268 50 41 105 169 297), lower := (rows 19 70 140 268 50 32 64 128 256), losses := [] }

theorem u7722 : Upper (D 5) (R 5) [18,68,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7722
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7723 : Route 9 := (fun mask => (mask,id))

def c7723 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7723 : Upper (D 5) (R 5) [18,68,136,260,40] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260,40] 13 (by decide) (choices 1) [1,2] r7723 c7723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4096
  · exact u4097

def b7724 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 296 19 45 109 173 301), lower := (rows 19 70 140 296 19 32 64 128 256), losses := [] }

theorem u7724 : Upper (D 5) (R 5) [18,68,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7724
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7725 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 296 21 43 107 171 299), lower := (rows 19 70 140 296 21 32 64 128 256), losses := [] }

theorem u7725 : Upper (D 5) (R 5) [18,68,136,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7725
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7726 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 296 22 41 105 169 297), lower := (rows 19 70 140 296 22 32 64 128 256), losses := [] }

theorem u7726 : Upper (D 5) (R 5) [18,68,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7726
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7727 : Route 9 := (fun mask => (mask,id))

def c7727 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7727 : Upper (D 5) (R 5) [18,68,136,288,9] 13 := by
  apply FastRouting.sound _ _ [18,68,136,288,9] 13 (by decide) (choices 1) [1,2,4] r7727 c7727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4098
  · exact u4099
  · exact u4100

def b7728 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 296 26 37 101 165 293), lower := (rows 19 70 140 296 26 32 64 128 256), losses := [] }

theorem u7728 : Upper (D 5) (R 5) [18,68,136,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7728
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7729 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 296 28 35 99 163 291), lower := (rows 19 70 140 296 28 32 64 128 256), losses := [] }

theorem u7729 : Upper (D 5) (R 5) [18,68,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7729
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7730 : Route 9 := (fun mask => (mask,id))

def c7730 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7730 : Upper (D 5) (R 5) [18,68,136,288,33] 13 := by
  apply FastRouting.sound _ _ [18,68,136,288,33] 13 (by decide) (choices 1) [1,2,4,8] r7730 c7730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4101
  · exact u4102
  · exact u4103
  · exact u4104

def b7731 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 296 50 45 77 141 269), lower := (rows 19 70 140 296 50 32 64 128 256), losses := [] }

theorem u7731 : Upper (D 5) (R 5) [18,68,136,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7731
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7732 : Route 9 := (fun mask => (mask,id))

def c7732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7732 : Upper (D 5) (R 5) [18,68,136,288,36] 13 := by
  apply FastRouting.sound _ _ [18,68,136,288,36] 13 (by decide) (choices 1) [1,2,8] r7732 c7732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4105
  · exact u4106
  · exact u4107

def b7733 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 296 56 39 71 135 263), lower := (rows 19 70 140 296 56 32 64 128 256), losses := [] }

theorem u7733 : Upper (D 5) (R 5) [18,68,136,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7733
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7734 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 41 19 300 332 396 268), lower := (rows 19 70 164 41 19 32 64 128 256), losses := [] }

theorem u7734 : Upper (D 5) (R 5) [18,68,160,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7735 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 41 21 298 330 394 266), lower := (rows 19 70 164 41 21 32 64 128 256), losses := [] }

theorem u7735 : Upper (D 5) (R 5) [18,68,160,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7735
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7736 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 164 41 22 297 329 393 265), lower := (rows 19 70 164 41 22 32 64 128 256), losses := [] }

theorem u7736 : Upper (D 5) (R 5) [18,68,160,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7736
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7737 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 164 41 25 302 334 398 270), lower := (rows 19 70 164 41 25 32 64 128 256), losses := [] }

theorem u7737 : Upper (D 5) (R 5) [18,68,160,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7738 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 41 26 301 333 397 269), lower := (rows 19 70 164 41 26 32 64 128 256), losses := [] }

theorem u7738 : Upper (D 5) (R 5) [18,68,160,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7738
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7739 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 164 41 28 299 331 395 267), lower := (rows 19 70 164 41 28 32 64 128 256), losses := [] }

theorem u7739 : Upper (D 5) (R 5) [18,68,160,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7739
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7739
end Delivery.IrregularNine14.P05
