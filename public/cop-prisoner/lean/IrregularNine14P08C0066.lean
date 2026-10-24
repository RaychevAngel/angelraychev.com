import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0009

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3960 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 28 41 176 96 197 133 389), lower := (rows 67 290 28 41 176 96 64 128 256), losses := [] }

theorem u3960 : Upper (D 8) (R 8) [66,288,24,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3961 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 41 176 160 69 197 325), lower := (rows 67 290 28 41 176 160 64 128 256), losses := [] }

theorem u3961 : Upper (D 8) (R 8) [66,288,24,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3962 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 28 41 208 33 228 164 420), lower := (rows 67 290 28 41 208 33 64 128 256), losses := [] }

theorem u3962 : Upper (D 8) (R 8) [66,288,24,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3963 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 28 41 208 36 225 161 417), lower := (rows 67 290 28 41 208 36 64 128 256), losses := [] }

theorem u3963 : Upper (D 8) (R 8) [66,288,24,33,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3963 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3964 : Route 9 := (fun mask => (mask,id))

def c3964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3964 : Upper (D 8) (R 8) [66,288,24,33,192,128] 13 := by
  apply FastRouting.sound _ _ [66,288,24,33,192,128] 13 (by decide) (choices 1) [1,4,32] r3964 c3964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u548
  · exact u549
  · exact u550

def b3965 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 28 44 145 33 224 224 480), lower := (rows 67 290 28 44 145 33 64 128 256), losses := [] }

theorem u3965 : Upper (D 8) (R 8) [66,288,24,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3966 : PairBound 9 := { available := 161, camps := [], pairs := [(2,0)], upper := (rows 67 290 28 44 145 96 225 161 417), lower := (rows 67 290 28 44 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 97 64 128 256), good := (rows 98 290 28 44 188 96 96 128 256) }] }

theorem u3966 : Upper (D 8) (R 8) [66,288,24,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3967 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 44, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 28 44 145 160 97 225 353), lower := (rows 67 290 28 44 145 160 64 128 256), losses := [] }

theorem u3967 : Upper (D 8) (R 8) [66,288,24,36,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3968 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 290 28 104 145 33 228 164 420), lower := (rows 67 290 28 104 145 33 64 128 256), losses := [] }

theorem u3968 : Upper (D 8) (R 8) [66,288,24,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3969 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 28 104 145 36 225 161 417), lower := (rows 67 290 28 104 145 36 64 128 256), losses := [] }

theorem u3969 : Upper (D 8) (R 8) [66,288,24,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3969 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3970 : Route 9 := (fun mask => (mask,id))

def c3970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3970 : Upper (D 8) (R 8) [66,288,24,96,129,128] 13 := by
  apply FastRouting.sound _ _ [66,288,24,96,129,128] 13 (by decide) (choices 1) [1,4,32] r3970 c3970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u551
  · exact u552
  · exact u553

def b3971 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 290 28 104 176 33 197 133 389), lower := (rows 67 290 28 104 176 33 64 128 256), losses := [] }

theorem u3971 : Upper (D 8) (R 8) [66,288,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3972 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 28 104 176 36 193 129 385), lower := (rows 67 290 28 104 176 36 64 128 256), losses := [] }

theorem u3972 : Upper (D 8) (R 8) [66,288,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3972 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3973 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 104 176 160 69 133 261), lower := (rows 67 290 28 104 176 160 64 128 256), losses := [] }

theorem u3973 : Upper (D 8) (R 8) [66,288,24,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3974 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 290 37 56 84 33 200 136 392), lower := (rows 67 290 37 56 84 33 64 128 256), losses := [] }

theorem u3974 : Upper (D 8) (R 8) [66,288,33,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3975 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 37 56 84 40 193 129 385), lower := (rows 67 290 37 56 84 40 64 128 256), losses := [] }

theorem u3975 : Upper (D 8) (R 8) [66,288,33,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3975 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3976 : Route 9 := (fun mask => (mask,id))

def c3976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3976 : Upper (D 8) (R 8) [66,288,33,48,68,128] 13 := by
  apply FastRouting.sound _ _ [66,288,33,48,68,128] 13 (by decide) (choices 1) [1,8,128] r3976 c3976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u554
  · exact u555
  · exact u556

def b3977 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 67 290 37 56 145 36 200 200 456), lower := (rows 67 290 37 56 145 36 64 128 256), losses := [] }

theorem u3977 : Upper (D 8) (R 8) [66,288,33,48,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3977 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3978 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 67 290 37 56 145 40 196 196 452), lower := (rows 67 290 37 56 145 40 64 128 256), losses := [] }

theorem u3978 : Upper (D 8) (R 8) [66,288,33,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3978 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3979 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 56 145 96 204 140 396), lower := (rows 67 290 37 56 145 96 64 128 256), losses := [] }

theorem u3979 : Upper (D 8) (R 8) [66,288,33,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3980 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 56 145 160 76 204 332), lower := (rows 67 290 37 56 145 160 64 128 256), losses := [] }

theorem u3980 : Upper (D 8) (R 8) [66,288,33,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3981 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 56 148 33 200 200 456), lower := (rows 67 290 37 56 148 33 64 128 256), losses := [] }

theorem u3981 : Upper (D 8) (R 8) [66,288,33,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3982 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 290 37 56 148 40 193 193 449), lower := (rows 67 290 37 56 148 40 64 128 256), losses := [] }

theorem u3982 : Upper (D 8) (R 8) [66,288,33,48,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3982 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3983 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 56 148 96 201 137 393), lower := (rows 67 290 37 56 148 96 64 128 256), losses := [] }

theorem u3983 : Upper (D 8) (R 8) [66,288,33,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3984 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 56 148 160 73 201 329), lower := (rows 67 290 37 56 148 160 64 128 256), losses := [] }

theorem u3984 : Upper (D 8) (R 8) [66,288,33,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3985 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 56 152 33 196 196 452), lower := (rows 67 290 37 56 152 33 64 128 256), losses := [] }

theorem u3985 : Upper (D 8) (R 8) [66,288,33,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3986 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 290 37 56 152 36 193 193 449), lower := (rows 67 290 37 56 152 36 64 128 256), losses := [] }

theorem u3986 : Upper (D 8) (R 8) [66,288,33,48,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3986 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3987 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 37 56 152 96 197 133 389), lower := (rows 67 290 37 56 152 96 64 128 256), losses := [] }

theorem u3987 : Upper (D 8) (R 8) [66,288,33,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3988 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 37 56 152 160 69 197 325), lower := (rows 67 290 37 56 152 160 64 128 256), losses := [] }

theorem u3988 : Upper (D 8) (R 8) [66,288,33,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3989 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 56 208 33 204 140 396), lower := (rows 67 290 37 56 208 33 64 128 256), losses := [] }

theorem u3989 : Upper (D 8) (R 8) [66,288,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3990 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 290 37 56 208 36 201 137 393), lower := (rows 67 290 37 56 208 36 64 128 256), losses := [] }

theorem u3990 : Upper (D 8) (R 8) [66,288,33,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3990 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3991 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 290 37 56 208 40 197 133 389), lower := (rows 67 290 37 56 208 40 64 128 256), losses := [] }

theorem u3991 : Upper (D 8) (R 8) [66,288,33,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3991 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3992 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 56 208 160 77 141 269), lower := (rows 67 290 37 56 208 160 64 128 256), losses := [] }

theorem u3992 : Upper (D 8) (R 8) [66,288,33,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3993 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 67 290 37 76 145 40 240 176 432), lower := (rows 67 290 37 76 145 40 64 128 256), losses := [] }

theorem u3993 : Upper (D 8) (R 8) [66,288,33,68,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3993 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3994 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 67 290 37 76 145 48 232 168 424), lower := (rows 67 290 37 76 145 48 64 128 256), losses := [] }

theorem u3994 : Upper (D 8) (R 8) [66,288,33,68,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3994 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3995 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 37 76 145 160 120 184 312), lower := (rows 67 290 37 76 145 160 64 128 256), losses := [] }

theorem u3995 : Upper (D 8) (R 8) [66,288,33,68,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3996 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 76 152 33 240 176 432), lower := (rows 67 290 37 76 152 33 64 128 256), losses := [] }

theorem u3996 : Upper (D 8) (R 8) [66,288,33,68,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3997 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 37 76 152 48 225 161 417), lower := (rows 67 290 37 76 152 48 64 128 256), losses := [] }

theorem u3997 : Upper (D 8) (R 8) [66,288,33,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3997 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3998 : Route 9 := (fun mask => (mask,id))

def c3998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3998 : Upper (D 8) (R 8) [66,288,33,68,136,128] 13 := by
  apply FastRouting.sound _ _ [66,288,33,68,136,128] 13 (by decide) (choices 1) [1,16,32] r3998 c3998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u557
  · exact u558
  · exact u559

def b3999 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 76 176 33 216 152 408), lower := (rows 67 290 37 76 176 33 64 128 256), losses := [] }

theorem u3999 : Upper (D 8) (R 8) [66,288,33,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4000 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 290 37 76 176 40 209 145 401), lower := (rows 67 290 37 76 176 40 64 128 256), losses := [] }

theorem u4000 : Upper (D 8) (R 8) [66,288,33,68,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4000 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4001 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 290 37 76 176 48 201 137 393), lower := (rows 67 290 37 76 176 48 64 128 256), losses := [] }

theorem u4001 : Upper (D 8) (R 8) [66,288,33,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4001 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4002 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 76 176 160 89 153 281), lower := (rows 67 290 37 76 176 160 64 128 256), losses := [] }

theorem u4002 : Upper (D 8) (R 8) [66,288,33,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4003 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 67 290 37 88 145 36 232 168 424), lower := (rows 67 290 37 88 145 36 64 128 256), losses := [] }

theorem u4003 : Upper (D 8) (R 8) [66,288,33,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4003 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4004 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 67 290 37 88 145 40 228 164 420), lower := (rows 67 290 37 88 145 40 64 128 256), losses := [] }

theorem u4004 : Upper (D 8) (R 8) [66,288,33,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4004 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4005 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 37 88 145 160 108 172 300), lower := (rows 67 290 37 88 145 160 64 128 256), losses := [] }

theorem u4005 : Upper (D 8) (R 8) [66,288,33,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4006 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 88 148 33 232 168 424), lower := (rows 67 290 37 88 148 33 64 128 256), losses := [] }

theorem u4006 : Upper (D 8) (R 8) [66,288,33,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4007 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 290 37 88 148 40 225 161 417), lower := (rows 67 290 37 88 148 40 64 128 256), losses := [] }

theorem u4007 : Upper (D 8) (R 8) [66,288,33,80,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4007 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4008 : Route 9 := (fun mask => (mask,id))

def c4008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4008 : Upper (D 8) (R 8) [66,288,33,80,132,128] 13 := by
  apply FastRouting.sound _ _ [66,288,33,80,132,128] 13 (by decide) (choices 1) [1,8,32] r4008 c4008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u560
  · exact u561
  · exact u562

def b4009 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 88 176 33 204 140 396), lower := (rows 67 290 37 88 176 33 64 128 256), losses := [] }

theorem u4009 : Upper (D 8) (R 8) [66,288,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4010 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 290 37 88 176 36 201 137 393), lower := (rows 67 290 37 88 176 36 64 128 256), losses := [] }

theorem u4010 : Upper (D 8) (R 8) [66,288,33,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4010 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4011 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 290 37 88 176 40 197 133 389), lower := (rows 67 290 37 88 176 40 64 128 256), losses := [] }

theorem u4011 : Upper (D 8) (R 8) [66,288,33,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4011 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4012 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 88 176 160 77 141 269), lower := (rows 67 290 37 88 176 160 64 128 256), losses := [] }

theorem u4012 : Upper (D 8) (R 8) [66,288,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4013 : PairBound 9 := { available := 152, camps := [], pairs := [], upper := (rows 67 290 37 104 145 36 216 152 408), lower := (rows 67 290 37 104 145 36 64 128 256), losses := [] }

theorem u4013 : Upper (D 8) (R 8) [66,288,33,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4013 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4014 : PairBound 9 := { available := 148, camps := [], pairs := [], upper := (rows 67 290 37 104 145 40 212 148 404), lower := (rows 67 290 37 104 145 40 64 128 256), losses := [] }

theorem u4014 : Upper (D 8) (R 8) [66,288,33,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4014 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4015 : PairBound 9 := { available := 140, camps := [], pairs := [], upper := (rows 67 290 37 104 145 48 204 140 396), lower := (rows 67 290 37 104 145 48 64 128 256), losses := [] }

theorem u4015 : Upper (D 8) (R 8) [66,288,33,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4015 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4016 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 37 104 145 160 92 156 284), lower := (rows 67 290 37 104 145 160 64 128 256), losses := [] }

theorem u4016 : Upper (D 8) (R 8) [66,288,33,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4017 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 104 148 33 216 152 408), lower := (rows 67 290 37 104 148 33 64 128 256), losses := [] }

theorem u4017 : Upper (D 8) (R 8) [66,288,33,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4018 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 290 37 104 148 40 209 145 401), lower := (rows 67 290 37 104 148 40 64 128 256), losses := [] }

theorem u4018 : Upper (D 8) (R 8) [66,288,33,96,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4018 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4019 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 290 37 104 148 48 201 137 393), lower := (rows 67 290 37 104 148 48 64 128 256), losses := [] }

theorem u4019 : Upper (D 8) (R 8) [66,288,33,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4019 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4019
end Delivery.IrregularNine14.P08
