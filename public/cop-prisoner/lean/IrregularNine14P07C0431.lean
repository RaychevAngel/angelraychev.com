import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0152

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r25860 : Route 9 := (fun mask => (mask,id))

def c25860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25860 : Upper (D 7) (R 7) [36,257,66,34,136,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,136,128] 13 (by decide) (choices 1) [1,16] r25860 c25860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9126
  · exact u9127

def b25861 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 259 70 42 208 33 216 152 408), lower := (rows 37 259 70 42 208 33 64 128 256), losses := [] }

theorem u25861 : Upper (D 7) (R 7) [36,257,66,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25862 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 259 70 42 208 40 209 145 401), lower := (rows 37 259 70 42 208 40 64 128 256), losses := [] }

theorem u25862 : Upper (D 7) (R 7) [36,257,66,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25862 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25863 : Route 9 := (fun mask => (mask,id))

def c25863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25863 : Upper (D 7) (R 7) [36,257,66,34,192,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,192,16] 13 (by decide) (choices 1) [1,8,128] r25863 c25863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9128
  · exact u9129
  · exact u9130

def r25864 : Route 9 := (fun mask => (mask,id))

def c25864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25864 : Upper (D 7) (R 7) [36,257,66,34,192,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,192,128] 13 (by decide) (choices 1) [1,8,16] r25864 c25864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9131
  · exact u9132
  · exact u9133

def b25865 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(3,1),(3,7),(4,7)], upper := (rows 37 259 70 56 81 34 200 136 392), lower := (rows 37 259 70 56 81 34 64 128 256), losses := [] }

theorem u25865 : Upper (D 7) (R 7) [36,257,66,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25866 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 70 56 81 40 194 130 386), lower := (rows 37 259 70 56 81 40 64 128 256), losses := [] }

theorem u25866 : Upper (D 7) (R 7) [36,257,66,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25866 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25867 : Route 9 := (fun mask => (mask,id))

def c25867 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25867 : Upper (D 7) (R 7) [36,257,66,48,65,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,48,65,128] 13 (by decide) (choices 1) [2,8,128] r25867 c25867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9134
  · exact u9135
  · exact u9136

def b25868 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 56 145 34 200 200 456), lower := (rows 37 259 70 56 145 34 64 128 256), losses := [] }

theorem u25868 : Upper (D 7) (R 7) [36,257,66,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25869 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 259 70 56 145 40 194 194 450), lower := (rows 37 259 70 56 145 40 64 128 256), losses := [] }

theorem u25869 : Upper (D 7) (R 7) [36,257,66,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25869 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25870 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 56 145 96 202 138 394), lower := (rows 37 259 70 56 145 96 64 128 256), losses := [] }

theorem u25870 : Upper (D 7) (R 7) [36,257,66,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25871 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 70 56 145 160 74 202 330), lower := (rows 37 259 70 56 145 160 64 128 256), losses := [] }

theorem u25871 : Upper (D 7) (R 7) [36,257,66,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25872 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 70 56 146 33 200 200 456), lower := (rows 37 259 70 56 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 22 9 22 32 107 171 299), good := (rows 508 478 470 508 470 488 64 128 256) }] }

theorem u25872 : Upper (D 7) (R 7) [36,257,66,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25873 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 259 70 56 146 40 193 193 449), lower := (rows 37 259 70 56 146 40 64 128 256), losses := [] }

theorem u25873 : Upper (D 7) (R 7) [36,257,66,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25873 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25874 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 56 146 96 201 137 393), lower := (rows 37 259 70 56 146 96 64 128 256), losses := [] }

theorem u25874 : Upper (D 7) (R 7) [36,257,66,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25875 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 70 56 146 160 73 201 329), lower := (rows 37 259 70 56 146 160 64 128 256), losses := [] }

theorem u25875 : Upper (D 7) (R 7) [36,257,66,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25876 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 70 56 152 33 194 194 450), lower := (rows 37 259 70 56 152 33 64 128 256), losses := [] }

theorem u25876 : Upper (D 7) (R 7) [36,257,66,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25877 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 37 259 70 56 152 34 193 193 449), lower := (rows 37 259 70 56 152 34 64 128 256), losses := [] }

theorem u25877 : Upper (D 7) (R 7) [36,257,66,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25878 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 56 152 96 195 131 387), lower := (rows 37 259 70 56 152 96 64 128 256), losses := [] }

theorem u25878 : Upper (D 7) (R 7) [36,257,66,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25879 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 37 259 70 56 152 160 67 195 323), lower := (rows 37 259 70 56 152 160 64 128 256), losses := [] }

theorem u25879 : Upper (D 7) (R 7) [36,257,66,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25880 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 70 56 208 33 202 138 394), lower := (rows 37 259 70 56 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 9 22 32 66 130 258), good := (rows 60 478 470 56 208 40 64 128 256) }] }

theorem u25880 : Upper (D 7) (R 7) [36,257,66,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25881 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 56 208 34 201 137 393), lower := (rows 37 259 70 56 208 34 64 128 256), losses := [] }

theorem u25881 : Upper (D 7) (R 7) [36,257,66,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25882 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 259 70 56 208 40 195 131 387), lower := (rows 37 259 70 56 208 40 64 128 256), losses := [] }

theorem u25882 : Upper (D 7) (R 7) [36,257,66,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25882 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25883 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 70 56 208 160 75 139 267), lower := (rows 37 259 70 56 208 160 64 128 256), losses := [] }

theorem u25883 : Upper (D 7) (R 7) [36,257,66,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25884 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 70 73 146 40 240 176 432), lower := (rows 37 259 70 73 146 40 64 128 256), losses := [] }

theorem u25884 : Upper (D 7) (R 7) [36,257,66,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25884 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25885 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 37 259 70 73 146 48 232 168 424), lower := (rows 37 259 70 73 146 48 64 128 256), losses := [] }

theorem u25885 : Upper (D 7) (R 7) [36,257,66,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25885 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25886 : Route 9 := (fun mask => (mask,id))

def c25886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25886 : Upper (D 7) (R 7) [36,257,66,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,65,130,128] 13 (by decide) (choices 1) [8,16,32] r25886 c25886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9137
  · exact u9138
  · exact u9139

def b25887 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 37 259 70 73 152 34 240 176 432), lower := (rows 37 259 70 73 152 34 64 128 256), losses := [] }

theorem u25887 : Upper (D 7) (R 7) [36,257,66,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25888 : Route 9 := (fun mask => (mask,id))

def c25888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25888 : Upper (D 7) (R 7) [36,257,66,65,136,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,65,136,16] 13 (by decide) (choices 1) [2,32,128] r25888 c25888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9140
  · exact u9141
  · exact u9142

def r25889 : Route 9 := (fun mask => (mask,id))

def c25889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25889 : Upper (D 7) (R 7) [36,257,66,65,136,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,65,136,128] 13 (by decide) (choices 1) [2,16,32] r25889 c25889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9143
  · exact u9144
  · exact u9145

def b25890 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 37 259 70 73 176 34 216 152 408), lower := (rows 37 259 70 73 176 34 64 128 256), losses := [] }

theorem u25890 : Upper (D 7) (R 7) [36,257,66,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25891 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 70 73 176 40 210 146 402), lower := (rows 37 259 70 73 176 40 64 128 256), losses := [] }

theorem u25891 : Upper (D 7) (R 7) [36,257,66,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25891 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25892 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 70 73 176 48 202 138 394), lower := (rows 37 259 70 73 176 48 64 128 256), losses := [] }

theorem u25892 : Upper (D 7) (R 7) [36,257,66,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25892 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25893 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 70 73 176 160 90 154 282), lower := (rows 37 259 70 73 176 160 64 128 256), losses := [] }

theorem u25893 : Upper (D 7) (R 7) [36,257,66,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25894 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 88 145 34 232 168 424), lower := (rows 37 259 70 88 145 34 64 128 256), losses := [] }

theorem u25894 : Upper (D 7) (R 7) [36,257,66,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25895 : Route 9 := (fun mask => (mask,id))

def c25895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25895 : Upper (D 7) (R 7) [36,257,66,80,129,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80,129,8] 13 (by decide) (choices 1) [2,32,128] r25895 c25895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9146
  · exact u9147
  · exact u9148

def r25896 : Route 9 := (fun mask => (mask,id))

def c25896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25896 : Upper (D 7) (R 7) [36,257,66,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80,129,128] 13 (by decide) (choices 1) [2,8,32] r25896 c25896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9149
  · exact u9150
  · exact u9151

def b25897 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 70 88 146 33 232 168 424), lower := (rows 37 259 70 88 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 14 18 32 65 129 257), good := (rows 492 478 94 88 158 480 64 128 256) }] }

theorem u25897 : Upper (D 7) (R 7) [36,257,66,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25898 : Route 9 := (fun mask => (mask,id))

def c25898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25898 : Upper (D 7) (R 7) [36,257,66,80,130,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80,130,8] 13 (by decide) (choices 1) [1,32,128] r25898 c25898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9152
  · exact u9153
  · exact u9154

def r25899 : Route 9 := (fun mask => (mask,id))

def c25899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25899 : Upper (D 7) (R 7) [36,257,66,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80,130,128] 13 (by decide) (choices 1) [1,8,32] r25899 c25899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9155
  · exact u9156
  · exact u9157

def b25900 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 259 70 88 152 33 226 162 418), lower := (rows 37 259 70 88 152 33 64 128 256), losses := [] }

theorem u25900 : Upper (D 7) (R 7) [36,257,66,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25901 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 37 259 70 88 152 34 225 161 417), lower := (rows 37 259 70 88 152 34 64 128 256), losses := [] }

theorem u25901 : Upper (D 7) (R 7) [36,257,66,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25902 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 259 70 88 152 160 99 163 291), lower := (rows 37 259 70 88 152 160 64 128 256), losses := [] }

theorem u25902 : Upper (D 7) (R 7) [36,257,66,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25903 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 70 88 176 33 202 138 394), lower := (rows 37 259 70 88 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 11 17 32 70 134 262), good := (rows 508 478 462 88 176 56 64 128 256) }] }

theorem u25903 : Upper (D 7) (R 7) [36,257,66,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25904 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 88 176 34 201 137 393), lower := (rows 37 259 70 88 176 34 64 128 256), losses := [] }

theorem u25904 : Upper (D 7) (R 7) [36,257,66,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25905 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 37 259 70 88 176 40 195 131 387), lower := (rows 37 259 70 88 176 40 64 128 256), losses := [] }

theorem u25905 : Upper (D 7) (R 7) [36,257,66,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25905 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25906 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 70 88 176 160 75 139 267), lower := (rows 37 259 70 88 176 160 64 128 256), losses := [] }

theorem u25906 : Upper (D 7) (R 7) [36,257,66,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25907 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 37 259 70 104 145 34 216 152 408), lower := (rows 37 259 70 104 145 34 64 128 256), losses := [] }

theorem u25907 : Upper (D 7) (R 7) [36,257,66,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25908 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 70 104 145 40 210 146 402), lower := (rows 37 259 70 104 145 40 64 128 256), losses := [] }

theorem u25908 : Upper (D 7) (R 7) [36,257,66,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25908 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25909 : Route 9 := (fun mask => (mask,id))

def c25909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25909 : Upper (D 7) (R 7) [36,257,66,96,129,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96,129,16] 13 (by decide) (choices 1) [2,8,128] r25909 c25909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9158
  · exact u9159
  · exact u9160

def r25910 : Route 9 := (fun mask => (mask,id))

def c25910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25910 : Upper (D 7) (R 7) [36,257,66,96,129,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96,129,128] 13 (by decide) (choices 1) [2,8,16] r25910 c25910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9161
  · exact u9162
  · exact u9163

def b25911 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 259 70 104 146 33 216 152 408), lower := (rows 37 259 70 104 146 33 64 128 256), losses := [] }

theorem u25911 : Upper (D 7) (R 7) [36,257,66,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25912 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 70 104 146 40 209 145 401), lower := (rows 37 259 70 104 146 40 64 128 256), losses := [] }

theorem u25912 : Upper (D 7) (R 7) [36,257,66,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25912 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25913 : Route 9 := (fun mask => (mask,id))

def c25913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25913 : Upper (D 7) (R 7) [36,257,66,96,130,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96,130,16] 13 (by decide) (choices 1) [1,8,128] r25913 c25913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9164
  · exact u9165
  · exact u9166

def r25914 : Route 9 := (fun mask => (mask,id))

def c25914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25914 : Upper (D 7) (R 7) [36,257,66,96,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96,130,128] 13 (by decide) (choices 1) [1,8,16] r25914 c25914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9167
  · exact u9168
  · exact u9169

def b25915 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 259 70 104 152 33 210 146 402), lower := (rows 37 259 70 104 152 33 64 128 256), losses := [] }

theorem u25915 : Upper (D 7) (R 7) [36,257,66,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25916 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(3,7),(4,1)], upper := (rows 37 259 70 104 152 34 209 145 401), lower := (rows 37 259 70 104 152 34 64 128 256), losses := [] }

theorem u25916 : Upper (D 7) (R 7) [36,257,66,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25917 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 37 259 70 104 152 48 195 131 387), lower := (rows 37 259 70 104 152 48 64 128 256), losses := [] }

theorem u25917 : Upper (D 7) (R 7) [36,257,66,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25917 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25918 : Route 9 := (fun mask => (mask,id))

def c25918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25918 : Upper (D 7) (R 7) [36,257,66,96,136,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96,136,128] 13 (by decide) (choices 1) [1,2,16] r25918 c25918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9170
  · exact u9171
  · exact u9172

def r25919 : Route 9 := (fun mask => (mask,id))

def c25919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25919 : Upper (D 7) (R 7) [36,257,66,129,130,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,129,130,8] 13 (by decide) (choices 1) [16,32] r25919 c25919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9173
  · exact u9174

#print axioms u25919
end Delivery.IrregularNine14.P07
