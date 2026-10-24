import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0134

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25860 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 28 336 33 70 134 262), lower := (rows 41 98 133 28 336 33 64 128 256), losses := [] }

theorem u25860 : Upper (D 6) (R 6) [40,96,129,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25861 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 28 336 34 71 135 263), lower := (rows 41 98 133 28 336 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 122 64 128 256), good := (rows 41 98 129 59 370 34 98 128 256) }] }

theorem u25861 : Upper (D 6) (R 6) [40,96,129,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25862 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 28 336 36 67 131 259), lower := (rows 41 98 133 28 336 36 64 128 256), losses := [] }

theorem u25862 : Upper (D 6) (R 6) [40,96,129,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25863 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 76 22 33 338 402 274), lower := (rows 41 98 133 76 22 33 64 128 256), losses := [] }

theorem u25863 : Upper (D 6) (R 6) [40,96,129,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25864 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 41 98 133 76 22 34 337 401 273), lower := (rows 41 98 133 76 22 34 64 128 256), losses := [] }

theorem u25864 : Upper (D 6) (R 6) [40,96,129,68,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25865 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 98 133 76 22 48 323 387 259), lower := (rows 41 98 133 76 22 48 64 128 256), losses := [] }

theorem u25865 : Upper (D 6) (R 6) [40,96,129,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25865 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25866 : Route 9 := (fun mask => (mask,id))

def c25866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25866 : Upper (D 6) (R 6) [40,96,129,68,6,256] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68,6,256] 13 (by decide) (choices 1) [1,2,16] r25866 c25866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8042
  · exact u8043
  · exact u8044

def b25867 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 76 273 34 86 150 278), lower := (rows 41 98 133 76 273 34 64 128 256), losses := [] }

theorem u25867 : Upper (D 6) (R 6) [40,96,129,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25868 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 76 273 36 82 146 274), lower := (rows 41 98 133 76 273 36 64 128 256), losses := [] }

theorem u25868 : Upper (D 6) (R 6) [40,96,129,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25869 : Route 9 := (fun mask => (mask,id))

def c25869 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25869 : Upper (D 6) (R 6) [40,96,129,68,257,16] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68,257,16] 13 (by decide) (choices 1) [2,4] r25869 c25869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8045
  · exact u8046

def b25870 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 76 274 33 86 150 278), lower := (rows 41 98 133 76 274 33 64 128 256), losses := [] }

theorem u25870 : Upper (D 6) (R 6) [40,96,129,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25871 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 76 274 34 85 149 277), lower := (rows 41 98 133 76 274 34 64 128 256), losses := [] }

theorem u25871 : Upper (D 6) (R 6) [40,96,129,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25872 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 76 274 36 83 147 275), lower := (rows 41 98 133 76 274 36 64 128 256), losses := [] }

theorem u25872 : Upper (D 6) (R 6) [40,96,129,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25873 : Route 9 := (fun mask => (mask,id))

def c25873 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25873 : Upper (D 6) (R 6) [40,96,129,68,258,16] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68,258,16] 13 (by decide) (choices 1) [1,2,4] r25873 c25873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8047
  · exact u8048
  · exact u8049

def b25874 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 76 276 33 82 146 274), lower := (rows 41 98 133 76 276 33 64 128 256), losses := [] }

theorem u25874 : Upper (D 6) (R 6) [40,96,129,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25875 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 76 276 34 83 147 275), lower := (rows 41 98 133 76 276 34 64 128 256), losses := [] }

theorem u25875 : Upper (D 6) (R 6) [40,96,129,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25876 : Route 9 := (fun mask => (mask,id))

def c25876 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25876 : Upper (D 6) (R 6) [40,96,129,68,260,16] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68,260,16] 13 (by decide) (choices 1) [1,2] r25876 c25876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8050
  · exact u8051

def b25877 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 88 22 33 326 390 262), lower := (rows 41 98 133 88 22 33 64 128 256), losses := [] }

theorem u25877 : Upper (D 6) (R 6) [40,96,129,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25878 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 388, targets := 34 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,1),(2,5)], upper := (rows 41 98 133 88 22 34 325 389 261), lower := (rows 41 98 133 88 22 34 64 128 256), losses := [] }

theorem u25878 : Upper (D 6) (R 6) [40,96,129,80,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25879 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 322, targets := 4 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 133 88 22 36 323 387 259), lower := (rows 41 98 133 88 22 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 52 64 128 256), good := (rows 42 98 164 122 54 36 64 128 256) },{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 165 121 52 36 64 128 256) }] }

theorem u25879 : Upper (D 6) (R 6) [40,96,129,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25880 : Route 9 := (fun mask => (mask,id))

def c25880 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25880 : Upper (D 6) (R 6) [40,96,129,80,6,256] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80,6,256] 13 (by decide) (choices 1) [1,2,4] r25880 c25880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8052
  · exact u8053
  · exact u8054

def b25881 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 2, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 88 273 34 70 134 262), lower := (rows 41 98 133 88 273 34 64 128 256), losses := [] }

theorem u25881 : Upper (D 6) (R 6) [40,96,129,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25882 : Route 9 := (fun mask => (mask,id))

def c25882 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25882 : Upper (D 6) (R 6) [40,96,129,80,257,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80,257,4] 13 (by decide) (choices 1) [2,4] r25882 c25882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8055
  · exact u8056

def b25883 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 88 274 33 70 134 262), lower := (rows 41 98 133 88 274 33 64 128 256), losses := [] }

theorem u25883 : Upper (D 6) (R 6) [40,96,129,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25884 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 34 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,1),(2,5)], upper := (rows 41 98 133 88 274 34 69 133 261), lower := (rows 41 98 133 88 274 34 64 128 256), losses := [] }

theorem u25884 : Upper (D 6) (R 6) [40,96,129,80,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25885 : Route 9 := (fun mask => (mask,id))

def c25885 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25885 : Upper (D 6) (R 6) [40,96,129,80,258,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80,258,4] 13 (by decide) (choices 1) [1,2,4] r25885 c25885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8057
  · exact u8058
  · exact u8059

def b25886 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 88 276 33 70 134 262), lower := (rows 41 98 133 88 276 33 64 128 256), losses := [] }

theorem u25886 : Upper (D 6) (R 6) [40,96,129,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25887 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 88 276 34 71 135 263), lower := (rows 41 98 133 88 276 34 64 128 256), losses := [] }

theorem u25887 : Upper (D 6) (R 6) [40,96,129,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25888 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 133 88 276 36 67 131 259), lower := (rows 41 98 133 88 276 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 52 64 128 256), good := (rows 42 98 164 122 308 36 64 128 256) },{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 165 121 308 36 64 128 256) }] }

theorem u25888 : Upper (D 6) (R 6) [40,96,129,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25889 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 265 22 34 84 212 340), lower := (rows 41 98 133 265 22 34 64 128 256), losses := [] }

theorem u25889 : Upper (D 6) (R 6) [40,96,129,257,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25890 : Route 9 := (fun mask => (mask,id))

def c25890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25890 : Upper (D 6) (R 6) [40,96,129,257,6,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,257,6,4] 13 (by decide) (choices 1) [2,16] r25890 c25890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8060
  · exact u8061

def b25891 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 98 133 265 22 48 70 198 326), lower := (rows 41 98 133 265 22 48 64 128 256), losses := [] }

theorem u25891 : Upper (D 6) (R 6) [40,96,129,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25891 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25892 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 265 22 96 86 150 278), lower := (rows 41 98 133 265 22 96 64 128 256), losses := [] }

theorem u25892 : Upper (D 6) (R 6) [40,96,129,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25893 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 265 84 34 86 150 278), lower := (rows 41 98 133 265 84 34 64 128 256), losses := [] }

theorem u25893 : Upper (D 6) (R 6) [40,96,129,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25894 : Route 9 := (fun mask => (mask,id))

def c25894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25894 : Upper (D 6) (R 6) [40,96,129,257,68,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,257,68,4] 13 (by decide) (choices 1) [2,16] r25894 c25894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8062
  · exact u8063

def b25895 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 265 84 48 70 134 262), lower := (rows 41 98 133 265 84 48 64 128 256), losses := [] }

theorem u25895 : Upper (D 6) (R 6) [40,96,129,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25895 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25896 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 266 22 33 84 212 340), lower := (rows 41 98 133 266 22 33 64 128 256), losses := [] }

theorem u25896 : Upper (D 6) (R 6) [40,96,129,258,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25897 : Route 9 := (fun mask => (mask,id))

def c25897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25897 : Upper (D 6) (R 6) [40,96,129,258,6,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,258,6,4] 13 (by decide) (choices 1) [1,16] r25897 c25897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8064
  · exact u8065

def b25898 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 41 98 133 266 22 48 69 197 325), lower := (rows 41 98 133 266 22 48 64 128 256), losses := [] }

theorem u25898 : Upper (D 6) (R 6) [40,96,129,258,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25898 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25899 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 266 22 96 85 149 277), lower := (rows 41 98 133 266 22 96 64 128 256), losses := [] }

theorem u25899 : Upper (D 6) (R 6) [40,96,129,258,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25900 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 266 81 34 84 148 276), lower := (rows 41 98 133 266 81 34 64 128 256), losses := [] }

theorem u25900 : Upper (D 6) (R 6) [40,96,129,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25901 : Route 9 := (fun mask => (mask,id))

def c25901 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25901 : Upper (D 6) (R 6) [40,96,129,258,65,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,258,65,4] 13 (by decide) (choices 1) [2,4,16] r25901 c25901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8066
  · exact u8067
  · exact u8068

def b25902 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 266 81 48 70 134 262), lower := (rows 41 98 133 266 81 48 64 128 256), losses := [] }

theorem u25902 : Upper (D 6) (R 6) [40,96,129,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25902 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25903 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 266 84 33 86 150 278), lower := (rows 41 98 133 266 84 33 64 128 256), losses := [] }

theorem u25903 : Upper (D 6) (R 6) [40,96,129,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25904 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 266 84 34 85 149 277), lower := (rows 41 98 133 266 84 34 64 128 256), losses := [] }

theorem u25904 : Upper (D 6) (R 6) [40,96,129,258,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25905 : Route 9 := (fun mask => (mask,id))

def c25905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25905 : Upper (D 6) (R 6) [40,96,129,258,68,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,258,68,4] 13 (by decide) (choices 1) [1,2,16] r25905 c25905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8069
  · exact u8070
  · exact u8071

def b25906 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 266 84 48 71 135 263), lower := (rows 41 98 133 266 84 48 64 128 256), losses := [] }

theorem u25906 : Upper (D 6) (R 6) [40,96,129,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25906 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25907 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 98 133 268 19 34 84 212 340), lower := (rows 41 98 133 268 19 34 64 128 256), losses := [] }

theorem u25907 : Upper (D 6) (R 6) [40,96,129,260,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25908 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 268 19 36 82 210 338), lower := (rows 41 98 133 268 19 36 64 128 256), losses := [] }

theorem u25908 : Upper (D 6) (R 6) [40,96,129,260,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25909 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 41 98 133 268 19 48 70 198 326), lower := (rows 41 98 133 268 19 48 64 128 256), losses := [] }

theorem u25909 : Upper (D 6) (R 6) [40,96,129,260,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25909 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25910 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 268 19 96 86 150 278), lower := (rows 41 98 133 268 19 96 64 128 256), losses := [] }

theorem u25910 : Upper (D 6) (R 6) [40,96,129,260,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25911 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 268 22 33 82 210 338), lower := (rows 41 98 133 268 22 33 64 128 256), losses := [] }

theorem u25911 : Upper (D 6) (R 6) [40,96,129,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25912 : Route 9 := (fun mask => (mask,id))

def c25912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25912 : Upper (D 6) (R 6) [40,96,129,260,6,2] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260,6,2] 13 (by decide) (choices 1) [1,16] r25912 c25912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8072
  · exact u8073

def r25913 : Route 9 := (fun mask => (mask,id))

def c25913 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25913 : Upper (D 6) (R 6) [40,96,129,260,6,16] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260,6,16] 13 (by decide) (choices 1) [1,2] r25913 c25913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8074
  · exact u8075

def b25914 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 268 22 96 83 147 275), lower := (rows 41 98 133 268 22 96 64 128 256), losses := [] }

theorem u25914 : Upper (D 6) (R 6) [40,96,129,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25915 : Route 9 := (fun mask => (mask,id))

def c25915 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25915 : Upper (D 6) (R 6) [40,96,129,260,65,2] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260,65,2] 13 (by decide) (choices 1) [2,4,16] r25915 c25915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8076
  · exact u8077
  · exact u8078

def b25916 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 268 81 36 82 146 274), lower := (rows 41 98 133 268 81 36 64 128 256), losses := [] }

theorem u25916 : Upper (D 6) (R 6) [40,96,129,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25917 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 268 81 48 70 134 262), lower := (rows 41 98 133 268 81 48 64 128 256), losses := [] }

theorem u25917 : Upper (D 6) (R 6) [40,96,129,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25917 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25918 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 268 84 33 82 146 274), lower := (rows 41 98 133 268 84 33 64 128 256), losses := [] }

theorem u25918 : Upper (D 6) (R 6) [40,96,129,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25919 : Route 9 := (fun mask => (mask,id))

def c25919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25919 : Upper (D 6) (R 6) [40,96,129,260,68,2] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260,68,2] 13 (by decide) (choices 1) [1,2,16] r25919 c25919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8079
  · exact u8080
  · exact u8081

#print axioms u25919
end Delivery.IrregularNine14.P06
