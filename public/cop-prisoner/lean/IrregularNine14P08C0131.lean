import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0023
import IrregularNine14P08C0024

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7860 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 276 41 145 224 224 224 480), lower := (rows 7 74 276 41 145 32 64 128 256), losses := [] }

theorem u7860 : Upper (D 8) (R 8) [6,72,272,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7861 : Route 9 := (fun mask => (mask,id))

def c7861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7861 : Upper (D 8) (R 8) [6,72,272,33,160] 13 := by
  apply FastRouting.sound _ _ [6,72,272,33,160] 13 (by decide) (choices 1) [1,64,128] r7861 c7861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1416
  · exact u1417
  · exact u1418

def b7862 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 276 41 208 161 225 161 417), lower := (rows 7 74 276 41 208 32 64 128 256), losses := [] }

theorem u7862 : Upper (D 8) (R 8) [6,72,272,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7863 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 276 137 49 224 224 224 480), lower := (rows 7 74 276 137 49 32 64 128 256), losses := [] }

theorem u7863 : Upper (D 8) (R 8) [6,72,272,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7864 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 276 137 81 160 224 160 416), lower := (rows 7 74 276 137 81 32 64 128 256), losses := [] }

theorem u7864 : Upper (D 8) (R 8) [6,72,272,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7865 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 276 137 112 161 225 161 417), lower := (rows 7 74 276 137 112 32 64 128 256), losses := [] }

theorem u7865 : Upper (D 8) (R 8) [6,72,272,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7866 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 74 276 137 145 96 96 224 352), lower := (rows 7 74 276 137 145 32 64 128 256), losses := [] }

theorem u7866 : Upper (D 8) (R 8) [6,72,272,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7867 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 276 137 176 97 97 225 353), lower := (rows 7 74 276 137 176 32 64 128 256), losses := [] }

theorem u7867 : Upper (D 8) (R 8) [6,72,272,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7868 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 276 137 208 33 97 161 289), lower := (rows 7 74 276 137 208 32 64 128 256), losses := [] }

theorem u7868 : Upper (D 8) (R 8) [6,72,272,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7869 : Route 9 := (fun mask => (mask,id))

def c7869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7869 : Upper (D 8) (R 8) [6,72,272,160,33] 13 := by
  apply FastRouting.sound _ _ [6,72,272,160,33] 13 (by decide) (choices 1) [1,64,128] r7869 c7869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1419
  · exact u1420
  · exact u1421

def b7870 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 276 168 81 161 225 161 417), lower := (rows 7 74 276 168 81 32 64 128 256), losses := [] }

theorem u7870 : Upper (D 8) (R 8) [6,72,272,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7871 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 276 168 112 161 225 161 417), lower := (rows 7 74 276 168 112 32 64 128 256), losses := [] }

theorem u7871 : Upper (D 8) (R 8) [6,72,272,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7872 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 7 74 276 168 145 97 97 225 353), lower := (rows 7 74 276 168 145 32 64 128 256), losses := [] }

theorem u7872 : Upper (D 8) (R 8) [6,72,272,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7873 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 276 168 176 97 97 225 353), lower := (rows 7 74 276 168 176 32 64 128 256), losses := [] }

theorem u7873 : Upper (D 8) (R 8) [6,72,272,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7874 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 276 168 208 33 97 161 289), lower := (rows 7 74 276 168 208 32 64 128 256), losses := [] }

theorem u7874 : Upper (D 8) (R 8) [6,72,272,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7875 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 74 292 25 49 224 224 224 480), lower := (rows 7 74 292 25 49 32 64 128 256), losses := [] }

theorem u7875 : Upper (D 8) (R 8) [6,72,288,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7876 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 74 292 25 81 160 224 160 416), lower := (rows 7 74 292 25 81 32 64 128 256), losses := [] }

theorem u7876 : Upper (D 8) (R 8) [6,72,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7877 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 25 112 161 225 161 417), lower := (rows 7 74 292 25 112 32 64 128 256), losses := [] }

theorem u7877 : Upper (D 8) (R 8) [6,72,288,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7878 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 74 292 25 145 224 224 224 480), lower := (rows 7 74 292 25 145 32 64 128 256), losses := [] }

theorem u7878 : Upper (D 8) (R 8) [6,72,288,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7879 : Route 9 := (fun mask => (mask,id))

def c7879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7879 : Upper (D 8) (R 8) [6,72,288,17,160] 13 := by
  apply FastRouting.sound _ _ [6,72,288,17,160] 13 (by decide) (choices 1) [1,64,128] r7879 c7879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1422
  · exact u1423
  · exact u1424

def b7880 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 25 208 161 225 161 417), lower := (rows 7 74 292 25 208 32 64 128 256), losses := [] }

theorem u7880 : Upper (D 8) (R 8) [6,72,288,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7881 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 292 41 49 240 208 208 464), lower := (rows 7 74 292 41 49 32 64 128 256), losses := [] }

theorem u7881 : Upper (D 8) (R 8) [6,72,288,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7882 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 292 41 81 176 240 176 432), lower := (rows 7 74 292 41 81 32 64 128 256), losses := [] }

theorem u7882 : Upper (D 8) (R 8) [6,72,288,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7883 : Route 9 := (fun mask => (mask,id))

def c7883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7883 : Upper (D 8) (R 8) [6,72,288,33,96] 13 := by
  apply FastRouting.sound _ _ [6,72,288,33,96] 13 (by decide) (choices 1) [1,16,128] r7883 c7883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1425
  · exact u1426
  · exact u1427

def b7884 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 41 145 240 240 240 496), lower := (rows 7 74 292 41 145 32 64 128 256), losses := [] }

theorem u7884 : Upper (D 8) (R 8) [6,72,288,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7885 : Route 9 := (fun mask => (mask,id))

def c7885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7885 : Upper (D 8) (R 8) [6,72,288,33,160] 13 := by
  apply FastRouting.sound _ _ [6,72,288,33,160] 13 (by decide) (choices 1) [1,16,64,128] r7885 c7885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1428
  · exact u1429
  · exact u1430
  · exact u1431

def r7886 : Route 9 := (fun mask => (mask,id))

def c7886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7886 : Upper (D 8) (R 8) [6,72,288,33,192] 13 := by
  apply FastRouting.sound _ _ [6,72,288,33,192] 13 (by decide) (choices 1) [1,16,128] r7886 c7886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1432
  · exact u1433
  · exact u1434

def b7887 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 292 56 49 225 193 193 449), lower := (rows 7 74 292 56 49 32 64 128 256), losses := [] }

theorem u7887 : Upper (D 8) (R 8) [6,72,288,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7888 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 56 81 161 225 161 417), lower := (rows 7 74 292 56 81 32 64 128 256), losses := [] }

theorem u7888 : Upper (D 8) (R 8) [6,72,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7889 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 56 112 161 193 129 385), lower := (rows 7 74 292 56 112 32 64 128 256), losses := [] }

theorem u7889 : Upper (D 8) (R 8) [6,72,288,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7890 : Route 9 := (fun mask => (mask,id))

def c7890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7890 : Upper (D 8) (R 8) [6,72,288,48,129] 13 := by
  apply FastRouting.sound _ _ [6,72,288,48,129] 13 (by decide) (choices 1) [1,64,128] r7890 c7890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1435
  · exact u1436
  · exact u1437

def b7891 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 292 56 176 225 193 193 449), lower := (rows 7 74 292 56 176 32 64 128 256), losses := [] }

theorem u7891 : Upper (D 8) (R 8) [6,72,288,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7892 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 56 208 161 225 161 417), lower := (rows 7 74 292 56 208 32 64 128 256), losses := [] }

theorem u7892 : Upper (D 8) (R 8) [6,72,288,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7893 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 137 49 240 240 240 496), lower := (rows 7 74 292 137 49 32 64 128 256), losses := [] }

theorem u7893 : Upper (D 8) (R 8) [6,72,288,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7894 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 292 137 81 176 240 176 432), lower := (rows 7 74 292 137 81 32 64 128 256), losses := [] }

theorem u7894 : Upper (D 8) (R 8) [6,72,288,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7895 : Route 9 := (fun mask => (mask,id))

def c7895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7895 : Upper (D 8) (R 8) [6,72,288,129,96] 13 := by
  apply FastRouting.sound _ _ [6,72,288,129,96] 13 (by decide) (choices 1) [1,16,128] r7895 c7895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1438
  · exact u1439
  · exact u1440

def b7896 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 74 292 137 145 112 112 240 368), lower := (rows 7 74 292 137 145 32 64 128 256), losses := [] }

theorem u7896 : Upper (D 8) (R 8) [6,72,288,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7897 : Route 9 := (fun mask => (mask,id))

def c7897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7897 : Upper (D 8) (R 8) [6,72,288,129,160] 13 := by
  apply FastRouting.sound _ _ [6,72,288,129,160] 13 (by decide) (choices 1) [1,16,64] r7897 c7897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1441
  · exact u1442
  · exact u1443

def r7898 : Route 9 := (fun mask => (mask,id))

def c7898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7898 : Upper (D 8) (R 8) [6,72,288,129,192] 13 := by
  apply FastRouting.sound _ _ [6,72,288,129,192] 13 (by decide) (choices 1) [1,16] r7898 c7898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1444
  · exact u1445

def r7899 : Route 9 := (fun mask => (mask,id))

def c7899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7899 : Upper (D 8) (R 8) [6,72,288,144,33] 13 := by
  apply FastRouting.sound _ _ [6,72,288,144,33] 13 (by decide) (choices 1) [1,64,128] r7899 c7899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1446
  · exact u1447
  · exact u1448

def b7900 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 152 81 161 225 161 417), lower := (rows 7 74 292 152 81 32 64 128 256), losses := [] }

theorem u7900 : Upper (D 8) (R 8) [6,72,288,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7901 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 152 112 161 225 161 417), lower := (rows 7 74 292 152 112 32 64 128 256), losses := [] }

theorem u7901 : Upper (D 8) (R 8) [6,72,288,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7902 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 152 145 97 97 225 353), lower := (rows 7 74 292 152 145 32 64 128 256), losses := [] }

theorem u7902 : Upper (D 8) (R 8) [6,72,288,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7903 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 152 176 97 97 225 353), lower := (rows 7 74 292 152 176 32 64 128 256), losses := [] }

theorem u7903 : Upper (D 8) (R 8) [6,72,288,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7904 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 152 208 33 97 161 289), lower := (rows 7 74 292 152 208 32 64 128 256), losses := [] }

theorem u7904 : Upper (D 8) (R 8) [6,72,288,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7905 : Route 9 := (fun mask => (mask,id))

def c7905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7905 : Upper (D 8) (R 8) [6,72,288,160,33] 13 := by
  apply FastRouting.sound _ _ [6,72,288,160,33] 13 (by decide) (choices 1) [1,16,64,128] r7905 c7905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1449
  · exact u1450
  · exact u1451
  · exact u1452

def b7906 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 292 168 81 177 241 177 433), lower := (rows 7 74 292 168 81 32 64 128 256), losses := [] }

theorem u7906 : Upper (D 8) (R 8) [6,72,288,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7907 : Route 9 := (fun mask => (mask,id))

def c7907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7907 : Upper (D 8) (R 8) [6,72,288,160,96] 13 := by
  apply FastRouting.sound _ _ [6,72,288,160,96] 13 (by decide) (choices 1) [1,16,128] r7907 c7907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1453
  · exact u1454
  · exact u1455

def b7908 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 7 74 292 168 145 113 113 241 369), lower := (rows 7 74 292 168 145 32 64 128 256), losses := [] }

theorem u7908 : Upper (D 8) (R 8) [6,72,288,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7909 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 292 168 176 113 81 209 337), lower := (rows 7 74 292 168 176 32 64 128 256), losses := [] }

theorem u7909 : Upper (D 8) (R 8) [6,72,288,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7910 : Route 9 := (fun mask => (mask,id))

def c7910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7910 : Upper (D 8) (R 8) [6,72,288,160,192] 13 := by
  apply FastRouting.sound _ _ [6,72,288,160,192] 13 (by decide) (choices 1) [1,16] r7910 c7910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1456
  · exact u1457

def b7911 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 74 388 25 49 224 224 224 480), lower := (rows 7 74 388 25 49 32 64 128 256), losses := [] }

theorem u7911 : Upper (D 8) (R 8) [6,72,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7912 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 74 388 25 81 160 224 160 416), lower := (rows 7 74 388 25 81 32 64 128 256), losses := [] }

theorem u7912 : Upper (D 8) (R 8) [6,72,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7913 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 388 25 112 161 225 161 417), lower := (rows 7 74 388 25 112 32 64 128 256), losses := [] }

theorem u7913 : Upper (D 8) (R 8) [6,72,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7914 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 388 25 145 96 96 224 352), lower := (rows 7 74 388 25 145 32 64 128 256), losses := [] }

theorem u7914 : Upper (D 8) (R 8) [6,72,384,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7915 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 388 25 176 97 97 225 353), lower := (rows 7 74 388 25 176 32 64 128 256), losses := [] }

theorem u7915 : Upper (D 8) (R 8) [6,72,384,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7916 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 388 25 208 33 97 161 289), lower := (rows 7 74 388 25 208 32 64 128 256), losses := [] }

theorem u7916 : Upper (D 8) (R 8) [6,72,384,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7917 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 388 41 49 240 240 240 496), lower := (rows 7 74 388 41 49 32 64 128 256), losses := [] }

theorem u7917 : Upper (D 8) (R 8) [6,72,384,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7918 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 388 41 81 176 240 176 432), lower := (rows 7 74 388 41 81 32 64 128 256), losses := [] }

theorem u7918 : Upper (D 8) (R 8) [6,72,384,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7919 : Route 9 := (fun mask => (mask,id))

def c7919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7919 : Upper (D 8) (R 8) [6,72,384,33,96] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,96] 13 (by decide) (choices 1) [1,16,128] r7919 c7919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1458
  · exact u1459
  · exact u1460

#print axioms u7919
end Delivery.IrregularNine14.P08
