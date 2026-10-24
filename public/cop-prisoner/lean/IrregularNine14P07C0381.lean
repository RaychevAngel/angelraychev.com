import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0117
import IrregularNine14P07C0118

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22860 : Route 9 := (fun mask => (mask,id))

def c22860 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22860 : Upper (D 7) (R 7) [36,72,18,160,384,64] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,384,64] 13 (by decide) (choices 1) [1,2] r22860 c22860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7060
  · exact u7061

def b22861 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 392, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(4,7)], upper := (rows 37 74 22 265 81 34 224 160 416), lower := (rows 37 74 22 265 81 34 64 128 256), losses := [] }

theorem u22861 : Upper (D 7) (R 7) [36,72,18,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22862 : Route 9 := (fun mask => (mask,id))

def c22862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22862 : Upper (D 7) (R 7) [36,72,18,257,65,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,257,65,128] 13 (by decide) (choices 1) [2,32,128] r22862 c22862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7062
  · exact u7063
  · exact u7064

def b22863 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 22 265 145 34 224 224 480), lower := (rows 37 74 22 265 145 34 64 128 256), losses := [] }

theorem u22863 : Upper (D 7) (R 7) [36,72,18,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22864 : Route 9 := (fun mask => (mask,id))

def c22864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22864 : Upper (D 7) (R 7) [36,72,18,257,129,64] 13 := by
  apply FastRouting.sound _ _ [36,72,18,257,129,64] 13 (by decide) (choices 1) [2,32,128] r22864 c22864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7065
  · exact u7066
  · exact u7067

def b22865 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 74 22 265 145 160 98 226 354), lower := (rows 37 74 22 265 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 72 53 265 177 160 64 160 256) }] }

theorem u22865 : Upper (D 7) (R 7) [36,72,18,257,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22866 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 22 265 176 33 194 194 450), lower := (rows 37 74 22 265 176 33 64 128 256), losses := [] }

theorem u22866 : Upper (D 7) (R 7) [36,72,18,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22867 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,1),(3,5),(4,1)], upper := (rows 37 74 22 265 176 34 193 193 449), lower := (rows 37 74 22 265 176 34 64 128 256), losses := [] }

theorem u22867 : Upper (D 7) (R 7) [36,72,18,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22868 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(3,5)], upper := (rows 37 74 22 265 176 96 195 131 387), lower := (rows 37 74 22 265 176 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 104 53 265 176 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 16 98 64 0 256), good := (rows 37 106 55 265 48 96 96 0 256) }] }

theorem u22868 : Upper (D 7) (R 7) [36,72,18,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22869 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 22 265 176 160 67 195 323), lower := (rows 37 74 22 265 176 160 64 128 256), losses := [] }

theorem u22869 : Upper (D 7) (R 7) [36,72,18,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22870 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 74 22 265 208 33 226 162 418), lower := (rows 37 74 22 265 208 33 64 128 256), losses := [] }

theorem u22870 : Upper (D 7) (R 7) [36,72,18,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22871 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 22 265 208 34 225 161 417), lower := (rows 37 74 22 265 208 34 64 128 256), losses := [] }

theorem u22871 : Upper (D 7) (R 7) [36,72,18,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22872 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(1,7),(3,6),(3,7)], upper := (rows 37 74 22 265 208 160 99 163 291), lower := (rows 37 74 22 265 208 160 64 128 256), losses := [] }

theorem u22872 : Upper (D 7) (R 7) [36,72,18,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22873 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 22 266 145 33 224 224 480), lower := (rows 37 74 22 266 145 33 64 128 256), losses := [] }

theorem u22873 : Upper (D 7) (R 7) [36,72,18,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22874 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,1),(0,7),(4,1),(4,6)], upper := (rows 37 74 22 266 145 96 225 161 417), lower := (rows 37 74 22 266 145 96 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 98 64 0 256), good := (rows 37 106 55 298 17 96 96 0 256) }] }

theorem u22874 : Upper (D 7) (R 7) [36,72,18,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22875 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 74 22 266 145 160 97 225 353), lower := (rows 37 74 22 266 145 160 64 128 256), losses := [] }

theorem u22875 : Upper (D 7) (R 7) [36,72,18,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22876 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 22 296 81 33 194 130 386), lower := (rows 37 74 22 296 81 33 64 128 256), losses := [] }

theorem u22876 : Upper (D 7) (R 7) [36,72,18,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22877 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 392, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(4,7)], upper := (rows 37 74 22 296 81 34 193 129 385), lower := (rows 37 74 22 296 81 34 64 128 256), losses := [] }

theorem u22877 : Upper (D 7) (R 7) [36,72,18,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22878 : Route 9 := (fun mask => (mask,id))

def c22878 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22878 : Upper (D 7) (R 7) [36,72,18,288,65,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,288,65,128] 13 (by decide) (choices 1) [1,2,128] r22878 c22878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7068
  · exact u7069
  · exact u7070

def b22879 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 22 296 145 33 194 194 450), lower := (rows 37 74 22 296 145 33 64 128 256), losses := [] }

theorem u22879 : Upper (D 7) (R 7) [36,72,18,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22880 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 22 296 145 34 193 193 449), lower := (rows 37 74 22 296 145 34 64 128 256), losses := [] }

theorem u22880 : Upper (D 7) (R 7) [36,72,18,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22881 : Route 9 := (fun mask => (mask,id))

def c22881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22881 : Upper (D 7) (R 7) [36,72,18,288,129,64] 13 := by
  apply FastRouting.sound _ _ [36,72,18,288,129,64] 13 (by decide) (choices 1) [1,2,128] r22881 c22881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7071
  · exact u7072
  · exact u7073

def b22882 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 74 22 296 145 160 67 195 323), lower := (rows 37 74 22 296 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 72 53 296 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 10 55 296 177 160 0 160 256) }] }

theorem u22882 : Upper (D 7) (R 7) [36,72,18,288,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22883 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 74 22 296 208 33 195 131 387), lower := (rows 37 74 22 296 208 33 64 128 256), losses := [] }

theorem u22883 : Upper (D 7) (R 7) [36,72,18,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22884 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 22 296 208 34 193 129 385), lower := (rows 37 74 22 296 208 34 64 128 256), losses := [] }

theorem u22884 : Upper (D 7) (R 7) [36,72,18,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22885 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(1,7),(3,6),(3,7)], upper := (rows 37 74 22 296 208 160 67 131 259), lower := (rows 37 74 22 296 208 160 64 128 256), losses := [] }

theorem u22885 : Upper (D 7) (R 7) [36,72,18,288,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22886 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 22 392 81 33 226 162 418), lower := (rows 37 74 22 392 81 33 64 128 256), losses := [] }

theorem u22886 : Upper (D 7) (R 7) [36,72,18,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22887 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 392, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(4,7)], upper := (rows 37 74 22 392 81 34 225 161 417), lower := (rows 37 74 22 392 81 34 64 128 256), losses := [] }

theorem u22887 : Upper (D 7) (R 7) [36,72,18,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22888 : Route 9 := (fun mask => (mask,id))

def c22888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22888 : Upper (D 7) (R 7) [36,72,18,384,65,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,384,65,128] 13 (by decide) (choices 1) [1,2,32] r22888 c22888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7074
  · exact u7075
  · exact u7076

def b22889 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(3,0)], upper := (rows 37 74 22 392 145 33 98 226 354), lower := (rows 37 74 22 392 145 33 64 128 256), losses := [] }

theorem u22889 : Upper (D 7) (R 7) [36,72,18,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22890 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 22 392 145 34 97 225 353), lower := (rows 37 74 22 392 145 34 64 128 256), losses := [] }

theorem u22890 : Upper (D 7) (R 7) [36,72,18,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22891 : Route 9 := (fun mask => (mask,id))

def c22891 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22891 : Upper (D 7) (R 7) [36,72,18,384,129,64] 13 := by
  apply FastRouting.sound _ _ [36,72,18,384,129,64] 13 (by decide) (choices 1) [1,2,32] r22891 c22891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7077
  · exact u7078
  · exact u7079

def b22892 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,5),(3,5)], upper := (rows 37 74 22 392 176 33 67 195 323), lower := (rows 37 74 22 392 176 33 64 128 256), losses := [] }

theorem u22892 : Upper (D 7) (R 7) [36,72,18,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22893 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,1),(3,5),(4,1)], upper := (rows 37 74 22 392 176 34 65 193 321), lower := (rows 37 74 22 392 176 34 64 128 256), losses := [] }

theorem u22893 : Upper (D 7) (R 7) [36,72,18,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22894 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(1,5),(3,5)], upper := (rows 37 74 22 392 176 96 67 131 259), lower := (rows 37 74 22 392 176 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 104 53 392 176 96 96 128 256) }] }

theorem u22894 : Upper (D 7) (R 7) [36,72,18,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22895 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 74 22 392 208 33 99 163 291), lower := (rows 37 74 22 392 208 33 64 128 256), losses := [] }

theorem u22895 : Upper (D 7) (R 7) [36,72,18,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22896 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 22 392 208 34 97 161 289), lower := (rows 37 74 22 392 208 34 64 128 256), losses := [] }

theorem u22896 : Upper (D 7) (R 7) [36,72,18,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22897 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 56 145 34 450 386 386), lower := (rows 37 74 69 56 145 34 64 128 256), losses := [] }

theorem u22897 : Upper (D 7) (R 7) [36,72,65,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22898 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 69 56 145 160 322 386 258), lower := (rows 37 74 69 56 145 160 64 128 256), losses := [] }

theorem u22898 : Upper (D 7) (R 7) [36,72,65,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22899 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 69 56 145 288 194 130 386), lower := (rows 37 74 69 56 145 288 64 128 256), losses := [] }

theorem u22899 : Upper (D 7) (R 7) [36,72,65,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22899 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22900 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 69 56 146 33 450 386 386), lower := (rows 37 74 69 56 146 33 64 128 256), losses := [] }

theorem u22900 : Upper (D 7) (R 7) [36,72,65,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22901 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(3,0),(3,6),(3,7)], upper := (rows 37 74 69 56 146 34 449 385 385), lower := (rows 37 74 69 56 146 34 64 128 256), losses := [] }

theorem u22901 : Upper (D 7) (R 7) [36,72,65,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22902 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 74 69 56 146 160 323 387 259), lower := (rows 37 74 69 56 146 160 64 128 256), losses := [] }

theorem u22902 : Upper (D 7) (R 7) [36,72,65,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22903 : Route 9 := (fun mask => (mask,id))

def c22903 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22903 : Upper (D 7) (R 7) [36,72,65,48,130,256] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,130,256] 13 (by decide) (choices 1) [1,2,128] r22903 c22903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7080
  · exact u7081
  · exact u7082

def b22904 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 56 273 34 194 130 386), lower := (rows 37 74 69 56 273 34 64 128 256), losses := [] }

theorem u22904 : Upper (D 7) (R 7) [36,72,65,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22905 : Route 9 := (fun mask => (mask,id))

def c22905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22905 : Upper (D 7) (R 7) [36,72,65,48,257,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,257,128] 13 (by decide) (choices 1) [2,128] r22905 c22905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7083
  · exact u7084

def b22906 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 69 56 274 33 194 130 386), lower := (rows 37 74 69 56 274 33 64 128 256), losses := [] }

theorem u22906 : Upper (D 7) (R 7) [36,72,65,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22907 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(3,6),(3,7)], upper := (rows 37 74 69 56 274 34 193 129 385), lower := (rows 37 74 69 56 274 34 64 128 256), losses := [] }

theorem u22907 : Upper (D 7) (R 7) [36,72,65,48,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22908 : Route 9 := (fun mask => (mask,id))

def c22908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22908 : Upper (D 7) (R 7) [36,72,65,48,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,258,128] 13 (by decide) (choices 1) [1,2,128] r22908 c22908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7085
  · exact u7086
  · exact u7087

def b22909 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 69 56 400 33 194 130 386), lower := (rows 37 74 69 56 400 33 64 128 256), losses := [] }

theorem u22909 : Upper (D 7) (R 7) [36,72,65,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22910 : Route 9 := (fun mask => (mask,id))

def c22910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22910 : Upper (D 7) (R 7) [36,72,65,48,384,2] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,384,2] 13 (by decide) (choices 1) [1,2,128] r22910 c22910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7088
  · exact u7089
  · exact u7090

def b22911 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 74 69 56 400 160 67 131 259), lower := (rows 37 74 69 56 400 160 64 128 256), losses := [] }

theorem u22911 : Upper (D 7) (R 7) [36,72,65,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22912 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 69 137 50 34 464 400 400), lower := (rows 37 74 69 137 50 34 64 128 256), losses := [] }

theorem u22912 : Upper (D 7) (R 7) [36,72,65,129,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22913 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 137 50 48 450 386 386), lower := (rows 37 74 69 137 50 48 64 128 256), losses := [] }

theorem u22913 : Upper (D 7) (R 7) [36,72,65,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22913 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22914 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 325, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 69 137 50 160 338 402 274), lower := (rows 37 74 69 137 50 160 64 128 256), losses := [] }

theorem u22914 : Upper (D 7) (R 7) [36,72,65,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22915 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 74 69 137 50 288 210 146 402), lower := (rows 37 74 69 137 50 288 64 128 256), losses := [] }

theorem u22915 : Upper (D 7) (R 7) [36,72,65,129,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22915 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22916 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 69 137 176 34 338 402 274), lower := (rows 37 74 69 137 176 34 64 128 256), losses := [] }

theorem u22916 : Upper (D 7) (R 7) [36,72,65,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22917 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 69 137 176 48 322 386 258), lower := (rows 37 74 69 137 176 48 64 128 256), losses := [] }

theorem u22917 : Upper (D 7) (R 7) [36,72,65,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22917 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22918 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 432, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 74 69 137 176 288 82 146 274), lower := (rows 37 74 69 137 176 288 64 128 256), losses := [] }

theorem u22918 : Upper (D 7) (R 7) [36,72,65,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22918 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22919 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 69 137 274 34 240 176 432), lower := (rows 37 74 69 137 274 34 64 128 256), losses := [] }

theorem u22919 : Upper (D 7) (R 7) [36,72,65,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22919
end Delivery.IrregularNine14.P07
