import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0122

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r23880 : Route 9 := (fun mask => (mask,id))

def c23880 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23880 : Upper (D 6) (R 6) [34,136,80,257,5,64] 13 := by
  apply FastRouting.sound _ _ [34,136,80,257,5,64] 13 (by decide) (choices 1) [2,4,32] r23880 c23880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7342
  · exact u7343
  · exact u7344

def b23881 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 265 22 33 100 228 356), lower := (rows 35 138 84 265 22 33 64 128 256), losses := [] }

theorem u23881 : Upper (D 6) (R 6) [34,136,80,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23882 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 265 22 36 97 225 353), lower := (rows 35 138 84 265 22 36 64 128 256), losses := [] }

theorem u23882 : Upper (D 6) (R 6) [34,136,80,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23883 : Route 9 := (fun mask => (mask,id))

def c23883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23883 : Upper (D 6) (R 6) [34,136,80,257,6,64] 13 := by
  apply FastRouting.sound _ _ [34,136,80,257,6,64] 13 (by decide) (choices 1) [1,4,32] r23883 c23883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7345
  · exact u7346
  · exact u7347

def b23884 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 265 52 33 70 198 326), lower := (rows 35 138 84 265 52 33 64 128 256), losses := [] }

theorem u23884 : Upper (D 6) (R 6) [34,136,80,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23885 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 265 52 34 69 197 325), lower := (rows 35 138 84 265 52 34 64 128 256), losses := [] }

theorem u23885 : Upper (D 6) (R 6) [34,136,80,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23886 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 84 265 52 36 67 195 323), lower := (rows 35 138 84 265 52 36 64 128 256), losses := [] }

theorem u23886 : Upper (D 6) (R 6) [34,136,80,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23887 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 84 265 52 96 71 135 263), lower := (rows 35 138 84 265 52 96 64 128 256), losses := [] }

theorem u23887 : Upper (D 6) (R 6) [34,136,80,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23888 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 266 21 33 100 228 356), lower := (rows 35 138 84 266 21 33 64 128 256), losses := [] }

theorem u23888 : Upper (D 6) (R 6) [34,136,80,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23889 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 266 21 36 97 225 353), lower := (rows 35 138 84 266 21 36 64 128 256), losses := [] }

theorem u23889 : Upper (D 6) (R 6) [34,136,80,258,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23890 : Route 9 := (fun mask => (mask,id))

def c23890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23890 : Upper (D 6) (R 6) [34,136,80,258,5,64] 13 := by
  apply FastRouting.sound _ _ [34,136,80,258,5,64] 13 (by decide) (choices 1) [1,4,32] r23890 c23890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7348
  · exact u7349
  · exact u7350

def b23891 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 266 52 33 69 197 325), lower := (rows 35 138 84 266 52 33 64 128 256), losses := [] }

theorem u23891 : Upper (D 6) (R 6) [34,136,80,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23892 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 84 266 52 36 65 193 321), lower := (rows 35 138 84 266 52 36 64 128 256), losses := [] }

theorem u23892 : Upper (D 6) (R 6) [34,136,80,258,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23893 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 84 266 52 96 69 133 261), lower := (rows 35 138 84 266 52 96 64 128 256), losses := [] }

theorem u23893 : Upper (D 6) (R 6) [34,136,80,258,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23894 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 268 21 33 98 226 354), lower := (rows 35 138 84 268 21 33 64 128 256), losses := [] }

theorem u23894 : Upper (D 6) (R 6) [34,136,80,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23895 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 268 21 34 97 225 353), lower := (rows 35 138 84 268 21 34 64 128 256), losses := [] }

theorem u23895 : Upper (D 6) (R 6) [34,136,80,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23896 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(1,6)], upper := (rows 35 138 84 268 21 96 99 163 291), lower := (rows 35 138 84 268 21 96 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 32 0 129 257), good := (rows 419 138 30 268 415 32 0 128 256) }] }

theorem u23896 : Upper (D 6) (R 6) [34,136,80,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23897 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 268 22 33 97 225 353), lower := (rows 35 138 84 268 22 33 64 128 256), losses := [] }

theorem u23897 : Upper (D 6) (R 6) [34,136,80,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23898 : Route 9 := (fun mask => (mask,id))

def c23898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23898 : Upper (D 6) (R 6) [34,136,80,260,6,64] 13 := by
  apply FastRouting.sound _ _ [34,136,80,260,6,64] 13 (by decide) (choices 1) [1,32] r23898 c23898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7351
  · exact u7352

def b23899 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 268 52 33 67 195 323), lower := (rows 35 138 84 268 52 33 64 128 256), losses := [] }

theorem u23899 : Upper (D 6) (R 6) [34,136,80,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23900 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 268 52 34 65 193 321), lower := (rows 35 138 84 268 52 34 64 128 256), losses := [] }

theorem u23900 : Upper (D 6) (R 6) [34,136,80,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23901 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 84 268 52 96 67 131 259), lower := (rows 35 138 84 268 52 96 64 128 256), losses := [] }

theorem u23901 : Upper (D 6) (R 6) [34,136,80,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23902 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 296 21 33 70 198 326), lower := (rows 35 138 84 296 21 33 64 128 256), losses := [] }

theorem u23902 : Upper (D 6) (R 6) [34,136,80,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23903 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 296 21 34 69 197 325), lower := (rows 35 138 84 296 21 34 64 128 256), losses := [] }

theorem u23903 : Upper (D 6) (R 6) [34,136,80,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23904 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 296 21 36 67 195 323), lower := (rows 35 138 84 296 21 36 64 128 256), losses := [] }

theorem u23904 : Upper (D 6) (R 6) [34,136,80,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23905 : Route 9 := (fun mask => (mask,id))

def c23905 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23905 : Upper (D 6) (R 6) [34,136,80,288,5,64] 13 := by
  apply FastRouting.sound _ _ [34,136,80,288,5,64] 13 (by decide) (choices 1) [1,2,4] r23905 c23905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7353
  · exact u7354
  · exact u7355

def b23906 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 296 22 33 69 197 325), lower := (rows 35 138 84 296 22 33 64 128 256), losses := [] }

theorem u23906 : Upper (D 6) (R 6) [34,136,80,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23907 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 296 22 36 65 193 321), lower := (rows 35 138 84 296 22 36 64 128 256), losses := [] }

theorem u23907 : Upper (D 6) (R 6) [34,136,80,288,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23908 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 296 22 96 69 133 261), lower := (rows 35 138 84 296 22 96 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 8 16 100 64 128 256), good := (rows 35 138 113 296 51 96 96 128 256) }] }

theorem u23908 : Upper (D 6) (R 6) [34,136,80,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23909 : Route 9 := (fun mask => (mask,id))

def c23909 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23909 : Upper (D 6) (R 6) [34,136,80,320,5,1] 13 := by
  apply FastRouting.sound _ _ [34,136,80,320,5,1] 13 (by decide) (choices 1) [2,4,32] r23909 c23909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7356
  · exact u7357
  · exact u7358

def b23910 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 328 21 34 101 165 293), lower := (rows 35 138 84 328 21 34 64 128 256), losses := [] }

theorem u23910 : Upper (D 6) (R 6) [34,136,80,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23911 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 328 21 36 99 163 291), lower := (rows 35 138 84 328 21 36 64 128 256), losses := [] }

theorem u23911 : Upper (D 6) (R 6) [34,136,80,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23912 : Route 9 := (fun mask => (mask,id))

def c23912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23912 : Upper (D 6) (R 6) [34,136,80,320,6,1] 13 := by
  apply FastRouting.sound _ _ [34,136,80,320,6,1] 13 (by decide) (choices 1) [1,4,32] r23912 c23912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7359
  · exact u7360
  · exact u7361

def b23913 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 328 22 36 97 161 289), lower := (rows 35 138 84 328 22 36 64 128 256), losses := [] }

theorem u23913 : Upper (D 6) (R 6) [34,136,80,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23914 : Route 9 := (fun mask => (mask,id))

def c23914 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23914 : Upper (D 6) (R 6) [34,136,80,320,36,1] 13 := by
  apply FastRouting.sound _ _ [34,136,80,320,36,1] 13 (by decide) (choices 1) [1,2,4] r23914 c23914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7362
  · exact u7363
  · exact u7364

def b23915 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 328 52 34 69 133 261), lower := (rows 35 138 84 328 52 34 64 128 256), losses := [] }

theorem u23915 : Upper (D 6) (R 6) [34,136,80,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23916 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 84 328 52 36 67 131 259), lower := (rows 35 138 84 328 52 36 64 128 256), losses := [] }

theorem u23916 : Upper (D 6) (R 6) [34,136,80,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23917 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 13 81 34 340 404 276), lower := (rows 35 138 100 13 81 34 64 128 256), losses := [] }

theorem u23917 : Upper (D 6) (R 6) [34,136,96,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23918 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 100 13 81 36 338 402 274), lower := (rows 35 138 100 13 81 36 64 128 256), losses := [] }

theorem u23918 : Upper (D 6) (R 6) [34,136,96,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23919 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 13 81 48 326 390 262), lower := (rows 35 138 100 13 81 48 64 128 256), losses := [] }

theorem u23919 : Upper (D 6) (R 6) [34,136,96,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23919 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23920 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 138 100 13 81 288 86 150 278), lower := (rows 35 138 100 13 81 288 64 128 256), losses := [] }

theorem u23920 : Upper (D 6) (R 6) [34,136,96,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23920 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23921 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 100 13 82 33 340 404 276), lower := (rows 35 138 100 13 82 33 64 128 256), losses := [] }

theorem u23921 : Upper (D 6) (R 6) [34,136,96,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23922 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 100 13 82 36 337 401 273), lower := (rows 35 138 100 13 82 36 64 128 256), losses := [] }

theorem u23922 : Upper (D 6) (R 6) [34,136,96,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23923 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 13 82 48 325 389 261), lower := (rows 35 138 100 13 82 48 64 128 256), losses := [] }

theorem u23923 : Upper (D 6) (R 6) [34,136,96,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23923 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23924 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 138 100 13 82 288 85 149 277), lower := (rows 35 138 100 13 82 288 64 128 256), losses := [] }

theorem u23924 : Upper (D 6) (R 6) [34,136,96,5,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23924 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23925 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 13 273 34 84 212 340), lower := (rows 35 138 100 13 273 34 64 128 256), losses := [] }

theorem u23925 : Upper (D 6) (R 6) [34,136,96,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23926 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 100 13 273 36 82 210 338), lower := (rows 35 138 100 13 273 36 64 128 256), losses := [] }

theorem u23926 : Upper (D 6) (R 6) [34,136,96,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23927 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 138 100 13 273 48 70 198 326), lower := (rows 35 138 100 13 273 48 64 128 256), losses := [] }

theorem u23927 : Upper (D 6) (R 6) [34,136,96,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23927 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23928 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 13 273 96 86 150 278), lower := (rows 35 138 100 13 273 96 64 128 256), losses := [] }

theorem u23928 : Upper (D 6) (R 6) [34,136,96,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23929 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 100 13 274 33 84 212 340), lower := (rows 35 138 100 13 274 33 64 128 256), losses := [] }

theorem u23929 : Upper (D 6) (R 6) [34,136,96,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23930 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 100 13 274 36 81 209 337), lower := (rows 35 138 100 13 274 36 64 128 256), losses := [] }

theorem u23930 : Upper (D 6) (R 6) [34,136,96,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23931 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 100 13 274 48 69 197 325), lower := (rows 35 138 100 13 274 48 64 128 256), losses := [] }

theorem u23931 : Upper (D 6) (R 6) [34,136,96,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23931 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23932 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 13 274 96 85 149 277), lower := (rows 35 138 100 13 274 96 64 128 256), losses := [] }

theorem u23932 : Upper (D 6) (R 6) [34,136,96,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23933 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 100 13 276 33 82 210 338), lower := (rows 35 138 100 13 276 33 64 128 256), losses := [] }

theorem u23933 : Upper (D 6) (R 6) [34,136,96,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23934 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 13 276 34 81 209 337), lower := (rows 35 138 100 13 276 34 64 128 256), losses := [] }

theorem u23934 : Upper (D 6) (R 6) [34,136,96,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23935 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 138 100 13 276 48 67 195 323), lower := (rows 35 138 100 13 276 48 64 128 256), losses := [] }

theorem u23935 : Upper (D 6) (R 6) [34,136,96,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23935 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23936 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 13 276 96 83 147 275), lower := (rows 35 138 100 13 276 96 64 128 256), losses := [] }

theorem u23936 : Upper (D 6) (R 6) [34,136,96,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23937 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 100 13 336 33 86 150 278), lower := (rows 35 138 100 13 336 33 64 128 256), losses := [] }

theorem u23937 : Upper (D 6) (R 6) [34,136,96,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23938 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 13 336 34 85 149 277), lower := (rows 35 138 100 13 336 34 64 128 256), losses := [] }

theorem u23938 : Upper (D 6) (R 6) [34,136,96,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23939 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 100 13 336 36 83 147 275), lower := (rows 35 138 100 13 336 36 64 128 256), losses := [] }

theorem u23939 : Upper (D 6) (R 6) [34,136,96,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23939
end Delivery.IrregularNine14.P06
