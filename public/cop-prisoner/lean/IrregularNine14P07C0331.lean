import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0090

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19860 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 262 73 176 33 216 152 408), lower := (rows 35 70 262 73 176 33 64 128 256), losses := [] }

theorem u19860 : Upper (D 7) (R 7) [34,68,258,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19861 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 262 73 176 40 209 145 401), lower := (rows 35 70 262 73 176 40 64 128 256), losses := [] }

theorem u19861 : Upper (D 7) (R 7) [34,68,258,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19861 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19862 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 262 73 176 48 201 137 393), lower := (rows 35 70 262 73 176 48 64 128 256), losses := [] }

theorem u19862 : Upper (D 7) (R 7) [34,68,258,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19862 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19863 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 262 73 176 160 89 153 281), lower := (rows 35 70 262 73 176 160 64 128 256), losses := [] }

theorem u19863 : Upper (D 7) (R 7) [34,68,258,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19864 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 262 88 145 33 232 168 424), lower := (rows 35 70 262 88 145 33 64 128 256), losses := [] }

theorem u19864 : Upper (D 7) (R 7) [34,68,258,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19865 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 262 88 145 40 225 161 417), lower := (rows 35 70 262 88 145 40 64 128 256), losses := [] }

theorem u19865 : Upper (D 7) (R 7) [34,68,258,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19865 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19866 : Route 9 := (fun mask => (mask,id))

def c19866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19866 : Upper (D 7) (R 7) [34,68,258,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,258,80,129,128] 13 (by decide) (choices 1) [1,8,32] r19866 c19866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5427
  · exact u5428
  · exact u5429

def b19867 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 262 88 176 33 201 137 393), lower := (rows 35 70 262 88 176 33 64 128 256), losses := [] }

theorem u19867 : Upper (D 7) (R 7) [34,68,258,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19868 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 262 88 176 40 193 129 385), lower := (rows 35 70 262 88 176 40 64 128 256), losses := [] }

theorem u19868 : Upper (D 7) (R 7) [34,68,258,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19868 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19869 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 262 88 176 160 73 137 265), lower := (rows 35 70 262 88 176 160 64 128 256), losses := [] }

theorem u19869 : Upper (D 7) (R 7) [34,68,258,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19870 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 262 104 145 33 216 152 408), lower := (rows 35 70 262 104 145 33 64 128 256), losses := [] }

theorem u19870 : Upper (D 7) (R 7) [34,68,258,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19871 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 262 104 145 40 209 145 401), lower := (rows 35 70 262 104 145 40 64 128 256), losses := [] }

theorem u19871 : Upper (D 7) (R 7) [34,68,258,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19871 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19872 : Route 9 := (fun mask => (mask,id))

def c19872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19872 : Upper (D 7) (R 7) [34,68,258,96,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,258,96,129,16] 13 (by decide) (choices 1) [1,8,128] r19872 c19872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5430
  · exact u5431
  · exact u5432

def r19873 : Route 9 := (fun mask => (mask,id))

def c19873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19873 : Upper (D 7) (R 7) [34,68,258,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,258,96,129,128] 13 (by decide) (choices 1) [1,8,16] r19873 c19873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5433
  · exact u5434
  · exact u5435

def b19874 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 35 70 262 104 152 33 209 145 401), lower := (rows 35 70 262 104 152 33 64 128 256), losses := [] }

theorem u19874 : Upper (D 7) (R 7) [34,68,258,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19875 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 262 104 152 48 193 129 385), lower := (rows 35 70 262 104 152 48 64 128 256), losses := [] }

theorem u19875 : Upper (D 7) (R 7) [34,68,258,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19875 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19876 : Route 9 := (fun mask => (mask,id))

def c19876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19876 : Upper (D 7) (R 7) [34,68,258,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,68,258,96,136,128] 13 (by decide) (choices 1) [1,16] r19876 c19876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5436
  · exact u5437

def b19877 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 262 137 176 33 88 216 344), lower := (rows 35 70 262 137 176 33 64 128 256), losses := [] }

theorem u19877 : Upper (D 7) (R 7) [34,68,258,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19878 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 262 137 176 40 81 209 337), lower := (rows 35 70 262 137 176 40 64 128 256), losses := [] }

theorem u19878 : Upper (D 7) (R 7) [34,68,258,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19878 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19879 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 262 137 176 48 73 201 329), lower := (rows 35 70 262 137 176 48 64 128 256), losses := [] }

theorem u19879 : Upper (D 7) (R 7) [34,68,258,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19879 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19880 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 152, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 262 137 176 96 89 153 281), lower := (rows 35 70 262 137 176 96 64 128 256), losses := [] }

theorem u19880 : Upper (D 7) (R 7) [34,68,258,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19881 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 262 137 208 33 120 184 312), lower := (rows 35 70 262 137 208 33 64 128 256), losses := [] }

theorem u19881 : Upper (D 7) (R 7) [34,68,258,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19882 : Route 9 := (fun mask => (mask,id))

def c19882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19882 : Upper (D 7) (R 7) [34,68,258,129,192,8] 13 := by
  apply FastRouting.sound _ _ [34,68,258,129,192,8] 13 (by decide) (choices 1) [1,16,32] r19882 c19882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5438
  · exact u5439
  · exact u5440

def b19883 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 35 70 262 137 208 48 105 169 297), lower := (rows 35 70 262 137 208 48 64 128 256), losses := [] }

theorem u19883 : Upper (D 7) (R 7) [34,68,258,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19883 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19884 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 70 262 168 208 33 89 153 281), lower := (rows 35 70 262 168 208 33 64 128 256), losses := [] }

theorem u19884 : Upper (D 7) (R 7) [34,68,258,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19885 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 262 168 208 40 81 145 273), lower := (rows 35 70 262 168 208 40 64 128 256), losses := [] }

theorem u19885 : Upper (D 7) (R 7) [34,68,258,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19885 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19886 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 262 168 208 48 73 137 265), lower := (rows 35 70 262 168 208 48 64 128 256), losses := [] }

theorem u19886 : Upper (D 7) (R 7) [34,68,258,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19886 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19887 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 268 25 146 33 224 224 480), lower := (rows 35 70 268 25 146 33 64 128 256), losses := [] }

theorem u19887 : Upper (D 7) (R 7) [34,68,264,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19888 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 268 25 146 96 225 161 417), lower := (rows 35 70 268 25 146 96 64 128 256), losses := [] }

theorem u19888 : Upper (D 7) (R 7) [34,68,264,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19889 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 3, region := 484, targets := 2 }], pairs := [(0,6),(1,7),(2,1),(3,6)], upper := (rows 35 70 268 25 146 160 97 225 353), lower := (rows 35 70 268 25 146 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 32 65 0 257), good := (rows 355 70 270 351 18 32 64 0 256) }] }

theorem u19889 : Upper (D 7) (R 7) [34,68,264,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19890 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 268 25 176 33 194 194 450), lower := (rows 35 70 268 25 176 33 64 128 256), losses := [] }

theorem u19890 : Upper (D 7) (R 7) [34,68,264,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19891 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 25 176 34 193 193 449), lower := (rows 35 70 268 25 176 34 64 128 256), losses := [] }

theorem u19891 : Upper (D 7) (R 7) [34,68,264,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19892 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 268 25 176 96 195 131 387), lower := (rows 35 70 268 25 176 96 64 128 256), losses := [] }

theorem u19892 : Upper (D 7) (R 7) [34,68,264,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19893 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 268 25 176 160 67 195 323), lower := (rows 35 70 268 25 176 160 64 128 256), losses := [] }

theorem u19893 : Upper (D 7) (R 7) [34,68,264,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19894 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 208, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 70 268 25 208 33 226 162 418), lower := (rows 35 70 268 25 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 57 32 65 129 257), good := (rows 498 70 286 478 208 496 64 128 256) }] }

theorem u19894 : Upper (D 7) (R 7) [34,68,264,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19895 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 25 208 34 225 161 417), lower := (rows 35 70 268 25 208 34 64 128 256), losses := [] }

theorem u19895 : Upper (D 7) (R 7) [34,68,264,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19896 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,7),(2,6),(2,7)], upper := (rows 35 70 268 25 208 160 99 163 291), lower := (rows 35 70 268 25 208 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 187 0 131 259), good := (rows 419 423 300 445 176 160 0 160 256) },{ target := 7, region := (rows 1 10 12 8 16 32 65 0 257), good := (rows 355 70 270 351 80 32 64 0 256) }] }

theorem u19896 : Upper (D 7) (R 7) [34,68,264,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19897 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 57, targets := 128 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,7)], upper := (rows 35 70 268 26 112 33 193 129 385), lower := (rows 35 70 268 26 112 33 64 128 256), losses := [] }

theorem u19897 : Upper (D 7) (R 7) [34,68,264,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19898 : Route 9 := (fun mask => (mask,id))

def c19898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19898 : Upper (D 7) (R 7) [34,68,264,18,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,18,96,128] 13 (by decide) (choices 1) [1,128] r19898 c19898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5441
  · exact u5442

def b19899 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(1,0),(4,1)], upper := (rows 35 70 268 26 145 33 224 224 480), lower := (rows 35 70 268 26 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 97 161 289), good := (rows 482 70 268 30 478 480 64 128 256) }] }

theorem u19899 : Upper (D 7) (R 7) [34,68,264,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19900 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 268 26 145 96 225 161 417), lower := (rows 35 70 268 26 145 96 64 128 256), losses := [] }

theorem u19900 : Upper (D 7) (R 7) [34,68,264,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19901 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,7),(2,1),(4,1)], upper := (rows 35 70 268 26 145 160 97 225 353), lower := (rows 35 70 268 26 145 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 185 81 145 273), good := (rows 497 68 300 508 497 160 64 160 256) },{ target := 6, region := (rows 9 2 4 8 16 176 0 128 256), good := (rows 35 6 269 59 177 160 0 160 256) },{ target := 7, region := (rows 1 18 20 24 16 32 65 0 257), good := (rows 355 70 268 30 351 32 64 0 256) }] }

theorem u19901 : Upper (D 7) (R 7) [34,68,264,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19902 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(1,5),(4,1)], upper := (rows 35 70 268 26 176 33 193 193 449), lower := (rows 35 70 268 26 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 20 24 16 0 97 161 289), good := (rows 451 70 268 30 478 449 64 128 256) }] }

theorem u19902 : Upper (D 7) (R 7) [34,68,264,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19903 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 268 26 176 96 193 129 385), lower := (rows 35 70 268 26 176 96 64 128 256), losses := [] }

theorem u19903 : Upper (D 7) (R 7) [34,68,264,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19904 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 268 26 176 160 65 193 321), lower := (rows 35 70 268 26 176 160 64 128 256), losses := [] }

theorem u19904 : Upper (D 7) (R 7) [34,68,264,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19905 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,1)], upper := (rows 35 70 268 26 208 33 225 161 417), lower := (rows 35 70 268 26 208 33 64 128 256), losses := [] }

theorem u19905 : Upper (D 7) (R 7) [34,68,264,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19906 : Route 9 := (fun mask => (mask,id))

def c19906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19906 : Upper (D 7) (R 7) [34,68,264,18,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,18,192,128] 13 (by decide) (choices 1) [1,32] r19906 c19906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5443
  · exact u5444

def b19907 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 268 56 145 33 194 194 450), lower := (rows 35 70 268 56 145 33 64 128 256), losses := [] }

theorem u19907 : Upper (D 7) (R 7) [34,68,264,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19908 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 56 145 34 193 193 449), lower := (rows 35 70 268 56 145 34 64 128 256), losses := [] }

theorem u19908 : Upper (D 7) (R 7) [34,68,264,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19909 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 70 268 56 145 96 195 131 387), lower := (rows 35 70 268 56 145 96 64 128 256), losses := [] }

theorem u19909 : Upper (D 7) (R 7) [34,68,264,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19910 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 268 56 145 160 67 195 323), lower := (rows 35 70 268 56 145 160 64 128 256), losses := [] }

theorem u19910 : Upper (D 7) (R 7) [34,68,264,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19911 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 268 56 146 33 193 193 449), lower := (rows 35 70 268 56 146 33 64 128 256), losses := [] }

theorem u19911 : Upper (D 7) (R 7) [34,68,264,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19912 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 70 268 56 146 96 193 129 385), lower := (rows 35 70 268 56 146 96 64 128 256), losses := [] }

theorem u19912 : Upper (D 7) (R 7) [34,68,264,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19913 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 268 56 146 160 65 193 321), lower := (rows 35 70 268 56 146 160 64 128 256), losses := [] }

theorem u19913 : Upper (D 7) (R 7) [34,68,264,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19914 : Route 9 := (fun mask => (mask,id))

def c19914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19914 : Upper (D 7) (R 7) [34,68,264,48,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,48,192,1] 13 (by decide) (choices 1) [1,2,128] r19914 c19914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5445
  · exact u5446
  · exact u5447

def b19915 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,1),(4,1),(4,5)], upper := (rows 35 70 268 56 208 34 193 129 385), lower := (rows 35 70 268 56 208 34 64 128 256), losses := [] }

theorem u19915 : Upper (D 7) (R 7) [34,68,264,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19916 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 268 56 208 160 67 131 259), lower := (rows 35 70 268 56 208 160 64 128 256), losses := [] }

theorem u19916 : Upper (D 7) (R 7) [34,68,264,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19917 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 73 145 34 240 176 432), lower := (rows 35 70 268 73 145 34 64 128 256), losses := [] }

theorem u19917 : Upper (D 7) (R 7) [34,68,264,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19918 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 70 268 73 145 48 226 162 418), lower := (rows 35 70 268 73 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 65 129 257), good := (rows 482 70 270 462 496 48 64 128 256) }] }

theorem u19918 : Upper (D 7) (R 7) [34,68,264,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19918 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19919 : Route 9 := (fun mask => (mask,id))

def c19919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19919 : Upper (D 7) (R 7) [34,68,264,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,65,129,128] 13 (by decide) (choices 1) [2,16,32] r19919 c19919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5448
  · exact u5449
  · exact u5450

#print axioms u19919
end Delivery.IrregularNine14.P07
