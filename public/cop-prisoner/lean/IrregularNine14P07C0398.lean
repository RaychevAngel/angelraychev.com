import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0128
import IrregularNine14P07C0129

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23880 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 76 138 19 48 449 385 385), lower := (rows 37 98 76 138 19 48 64 128 256), losses := [] }

theorem u23880 : Upper (D 7) (R 7) [36,96,72,130,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23880 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23881 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 98 76 138 19 160 337 401 273), lower := (rows 37 98 76 138 19 160 64 128 256), losses := [] }

theorem u23881 : Upper (D 7) (R 7) [36,96,72,130,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23882 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 204, targets := 32 },{ cop := 4, region := 136, targets := 64 }], pairs := [(2,5),(3,5),(3,6)], upper := (rows 37 98 76 138 19 288 209 145 401), lower := (rows 37 98 76 138 19 288 64 128 256), losses := [] }

theorem u23882 : Upper (D 7) (R 7) [36,96,72,130,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23882 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23883 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 138 145 33 338 402 274), lower := (rows 37 98 76 138 145 33 64 128 256), losses := [] }

theorem u23883 : Upper (D 7) (R 7) [36,96,72,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23884 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 76 138 145 34 337 401 273), lower := (rows 37 98 76 138 145 34 64 128 256), losses := [] }

theorem u23884 : Upper (D 7) (R 7) [36,96,72,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23885 : Route 9 := (fun mask => (mask,id))

def c23885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23885 : Upper (D 7) (R 7) [36,96,72,130,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,129,16] 13 (by decide) (choices 1) [1,2,256] r23885 c23885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7738
  · exact u7739
  · exact u7740

def r23886 : Route 9 := (fun mask => (mask,id))

def c23886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23886 : Upper (D 7) (R 7) [36,96,72,130,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,129,256] 13 (by decide) (choices 1) [1,2,16] r23886 c23886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7741
  · exact u7742
  · exact u7743

def b23887 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 138 273 33 210 146 402), lower := (rows 37 98 76 138 273 33 64 128 256), losses := [] }

theorem u23887 : Upper (D 7) (R 7) [36,96,72,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23888 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 76 138 273 34 209 145 401), lower := (rows 37 98 76 138 273 34 64 128 256), losses := [] }

theorem u23888 : Upper (D 7) (R 7) [36,96,72,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23889 : Route 9 := (fun mask => (mask,id))

def c23889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23889 : Upper (D 7) (R 7) [36,96,72,130,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,257,16] 13 (by decide) (choices 1) [1,2,128] r23889 c23889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7744
  · exact u7745
  · exact u7746

def b23890 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 138 273 160 83 147 275), lower := (rows 37 98 76 138 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 38 98 110 170 272 160 64 160 256) },{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 109 168 273 160 64 160 256) }] }

theorem u23890 : Upper (D 7) (R 7) [36,96,72,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23891 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 138 274 33 209 145 401), lower := (rows 37 98 76 138 274 33 64 128 256), losses := [] }

theorem u23891 : Upper (D 7) (R 7) [36,96,72,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23892 : Route 9 := (fun mask => (mask,id))

def c23892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23892 : Upper (D 7) (R 7) [36,96,72,130,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,258,16] 13 (by decide) (choices 1) [1,128] r23892 c23892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7747
  · exact u7748

def b23893 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 138 274 160 81 145 273), lower := (rows 37 98 76 138 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 38 98 110 170 274 160 64 160 256) },{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 109 168 272 160 64 160 256) }] }

theorem u23893 : Upper (D 7) (R 7) [36,96,72,130,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23894 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 138 400 33 83 147 275), lower := (rows 37 98 76 138 400 33 64 128 256), losses := [] }

theorem u23894 : Upper (D 7) (R 7) [36,96,72,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23895 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 76 138 400 34 81 145 273), lower := (rows 37 98 76 138 400 34 64 128 256), losses := [] }

theorem u23895 : Upper (D 7) (R 7) [36,96,72,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23896 : Route 9 := (fun mask => (mask,id))

def c23896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23896 : Upper (D 7) (R 7) [36,96,72,130,384,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,384,16] 13 (by decide) (choices 1) [1,2] r23896 c23896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7749
  · exact u7750

def b23897 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 76 152 19 33 450 386 386), lower := (rows 37 98 76 152 19 33 64 128 256), losses := [] }

theorem u23897 : Upper (D 7) (R 7) [36,96,72,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23898 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 76 152 19 34 449 385 385), lower := (rows 37 98 76 152 19 34 64 128 256), losses := [] }

theorem u23898 : Upper (D 7) (R 7) [36,96,72,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23899 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 98 76 152 19 160 323 387 259), lower := (rows 37 98 76 152 19 160 64 128 256), losses := [] }

theorem u23899 : Upper (D 7) (R 7) [36,96,72,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23900 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 204, targets := 32 },{ cop := 4, region := 136, targets := 64 }], pairs := [(2,5),(3,5),(3,6)], upper := (rows 37 98 76 152 19 288 195 131 387), lower := (rows 37 98 76 152 19 288 64 128 256), losses := [] }

theorem u23900 : Upper (D 7) (R 7) [36,96,72,144,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23900 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23901 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 152 273 33 194 130 386), lower := (rows 37 98 76 152 273 33 64 128 256), losses := [] }

theorem u23901 : Upper (D 7) (R 7) [36,96,72,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23902 : Route 9 := (fun mask => (mask,id))

def c23902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23902 : Upper (D 7) (R 7) [36,96,72,144,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,144,257,2] 13 (by decide) (choices 1) [1,2,128] r23902 c23902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7751
  · exact u7752
  · exact u7753

def b23903 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 152 273 160 67 131 259), lower := (rows 37 98 76 152 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 38 98 110 184 272 160 64 160 256) },{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 109 184 273 160 64 160 256) }] }

theorem u23903 : Upper (D 7) (R 7) [36,96,72,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23904 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 152 274 33 195 131 387), lower := (rows 37 98 76 152 274 33 64 128 256), losses := [] }

theorem u23904 : Upper (D 7) (R 7) [36,96,72,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23905 : Route 9 := (fun mask => (mask,id))

def c23905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23905 : Upper (D 7) (R 7) [36,96,72,144,258,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,144,258,2] 13 (by decide) (choices 1) [1,128] r23905 c23905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7754
  · exact u7755

def b23906 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 152 274 160 67 131 259), lower := (rows 37 98 76 152 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 38 98 110 184 274 160 64 160 256) },{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 109 184 272 160 64 160 256) }] }

theorem u23906 : Upper (D 7) (R 7) [36,96,72,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23907 : Route 9 := (fun mask => (mask,id))

def c23907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23907 : Upper (D 7) (R 7) [36,96,72,257,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,129,2] 13 (by decide) (choices 1) [2,16,128] r23907 c23907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7756
  · exact u7757
  · exact u7758

def r23908 : Route 9 := (fun mask => (mask,id))

def c23908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23908 : Upper (D 7) (R 7) [36,96,72,257,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,129,16] 13 (by decide) (choices 1) [2,128] r23908 c23908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7759
  · exact u7760

def r23909 : Route 9 := (fun mask => (mask,id))

def c23909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23909 : Upper (D 7) (R 7) [36,96,72,257,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,129,128] 13 (by decide) (choices 1) [2,16] r23909 c23909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7761
  · exact u7762

def b23910 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 265 146 33 210 146 402), lower := (rows 37 98 76 265 146 33 64 128 256), losses := [] }

theorem u23910 : Upper (D 7) (R 7) [36,96,72,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23911 : Route 9 := (fun mask => (mask,id))

def c23911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23911 : Upper (D 7) (R 7) [36,96,72,257,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,130,2] 13 (by decide) (choices 1) [1,16,128] r23911 c23911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7763
  · exact u7764
  · exact u7765

def r23912 : Route 9 := (fun mask => (mask,id))

def c23912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23912 : Upper (D 7) (R 7) [36,96,72,257,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,130,16] 13 (by decide) (choices 1) [1,2,128] r23912 c23912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7766
  · exact u7767
  · exact u7768

def r23913 : Route 9 := (fun mask => (mask,id))

def c23913 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23913 : Upper (D 7) (R 7) [36,96,72,257,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257,130,128] 13 (by decide) (choices 1) [1,2,16] r23913 c23913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7769
  · exact u7770
  · exact u7771

def b23914 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 76 266 19 33 208 144 400), lower := (rows 37 98 76 266 19 33 64 128 256), losses := [] }

theorem u23914 : Upper (D 7) (R 7) [36,96,72,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23915 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 76 266 19 48 193 129 385), lower := (rows 37 98 76 266 19 48 64 128 256), losses := [] }

theorem u23915 : Upper (D 7) (R 7) [36,96,72,258,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23915 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23916 : Route 9 := (fun mask => (mask,id))

def c23916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23916 : Upper (D 7) (R 7) [36,96,72,258,3,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,3,128] 13 (by decide) (choices 1) [1,16,128] r23916 c23916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7772
  · exact u7773
  · exact u7774

def b23917 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 266 145 33 210 146 402), lower := (rows 37 98 76 266 145 33 64 128 256), losses := [] }

theorem u23917 : Upper (D 7) (R 7) [36,96,72,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23918 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 76 266 145 34 209 145 401), lower := (rows 37 98 76 266 145 34 64 128 256), losses := [] }

theorem u23918 : Upper (D 7) (R 7) [36,96,72,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23919 : Route 9 := (fun mask => (mask,id))

def c23919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23919 : Upper (D 7) (R 7) [36,96,72,258,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,129,16] 13 (by decide) (choices 1) [1,2,128] r23919 c23919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7775
  · exact u7776
  · exact u7777

def r23920 : Route 9 := (fun mask => (mask,id))

def c23920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23920 : Upper (D 7) (R 7) [36,96,72,258,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,129,128] 13 (by decide) (choices 1) [1,2,16] r23920 c23920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7778
  · exact u7779
  · exact u7780

def b23921 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 266 146 33 209 145 401), lower := (rows 37 98 76 266 146 33 64 128 256), losses := [] }

theorem u23921 : Upper (D 7) (R 7) [36,96,72,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23922 : Route 9 := (fun mask => (mask,id))

def c23922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23922 : Upper (D 7) (R 7) [36,96,72,258,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,130,16] 13 (by decide) (choices 1) [1,128] r23922 c23922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7781
  · exact u7782

def r23923 : Route 9 := (fun mask => (mask,id))

def c23923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23923 : Upper (D 7) (R 7) [36,96,72,258,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258,130,128] 13 (by decide) (choices 1) [1,16] r23923 c23923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7783
  · exact u7784

def b23924 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 76 280 19 33 194 130 386), lower := (rows 37 98 76 280 19 33 64 128 256), losses := [] }

theorem u23924 : Upper (D 7) (R 7) [36,96,72,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23925 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 76 280 19 34 193 129 385), lower := (rows 37 98 76 280 19 34 64 128 256), losses := [] }

theorem u23925 : Upper (D 7) (R 7) [36,96,72,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23926 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 392, targets := 64 }], pairs := [(0,6),(2,5),(3,5),(3,6)], upper := (rows 37 98 76 280 19 160 195 131 387), lower := (rows 37 98 76 280 19 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 24 16 184 0 144 272), good := (rows 37 34 45 440 443 160 0 160 256) }] }

theorem u23926 : Upper (D 7) (R 7) [36,96,72,272,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23927 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 280 145 33 194 130 386), lower := (rows 37 98 76 280 145 33 64 128 256), losses := [] }

theorem u23927 : Upper (D 7) (R 7) [36,96,72,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23928 : Route 9 := (fun mask => (mask,id))

def c23928 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23928 : Upper (D 7) (R 7) [36,96,72,272,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272,129,2] 13 (by decide) (choices 1) [1,2,128] r23928 c23928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7785
  · exact u7786
  · exact u7787

def r23929 : Route 9 := (fun mask => (mask,id))

def c23929 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23929 : Upper (D 7) (R 7) [36,96,72,272,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272,129,128] 13 (by decide) (choices 1) [1,2] r23929 c23929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7788
  · exact u7789

def b23930 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 280 146 33 195 131 387), lower := (rows 37 98 76 280 146 33 64 128 256), losses := [] }

theorem u23930 : Upper (D 7) (R 7) [36,96,72,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23931 : Route 9 := (fun mask => (mask,id))

def c23931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23931 : Upper (D 7) (R 7) [36,96,72,272,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272,130,2] 13 (by decide) (choices 1) [1,128] r23931 c23931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7790
  · exact u7791

def r23932 : Route 9 := (fun mask => (mask,id))

def c23932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23932 : Upper (D 7) (R 7) [36,96,72,272,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272,130,128] 13 (by decide) (choices 1) [1,2] r23932 c23932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7792
  · exact u7793

def b23933 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 76 392 19 33 210 146 402), lower := (rows 37 98 76 392 19 33 64 128 256), losses := [] }

theorem u23933 : Upper (D 7) (R 7) [36,96,72,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23934 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 76 392 19 34 209 145 401), lower := (rows 37 98 76 392 19 34 64 128 256), losses := [] }

theorem u23934 : Upper (D 7) (R 7) [36,96,72,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23935 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 76 392 19 48 195 131 387), lower := (rows 37 98 76 392 19 48 64 128 256), losses := [] }

theorem u23935 : Upper (D 7) (R 7) [36,96,72,384,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23935 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23936 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 98 76 392 19 160 83 147 275), lower := (rows 37 98 76 392 19 160 64 128 256), losses := [] }

theorem u23936 : Upper (D 7) (R 7) [36,96,72,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23937 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 392 145 33 82 146 274), lower := (rows 37 98 76 392 145 33 64 128 256), losses := [] }

theorem u23937 : Upper (D 7) (R 7) [36,96,72,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23938 : Route 9 := (fun mask => (mask,id))

def c23938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23938 : Upper (D 7) (R 7) [36,96,72,384,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,129,2] 13 (by decide) (choices 1) [1,2,16] r23938 c23938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7794
  · exact u7795
  · exact u7796

def r23939 : Route 9 := (fun mask => (mask,id))

def c23939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23939 : Upper (D 7) (R 7) [36,96,72,384,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,129,16] 13 (by decide) (choices 1) [1,2] r23939 c23939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7797
  · exact u7798

#print axioms u23939
end Delivery.IrregularNine14.P07
