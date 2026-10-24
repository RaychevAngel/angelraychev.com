import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0130
import IrregularNine14P08C0131
import IrregularNine14P08C0132
import IrregularNine14P08C0133

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19080 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 392 113 113 113 241 369), lower := (rows 7 74 164 392 16 32 64 128 256), losses := [] }

theorem u19080 : Upper (D 8) (R 8) [6,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19081 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 25 240 224 224 224 480), lower := (rows 7 74 261 25 16 32 64 128 256), losses := [] }

theorem u19081 : Upper (D 8) (R 8) [6,72,257,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19082 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 41 240 240 240 240 496), lower := (rows 7 74 261 41 16 32 64 128 256), losses := [] }

theorem u19082 : Upper (D 8) (R 8) [6,72,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19083 : Route 9 := (fun mask => (mask,id))

def c19083 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19083 : Upper (D 8) (R 8) [6,72,257,48] 13 := by
  apply FastRouting.sound _ _ [6,72,257,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19083 c19083
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7839
  · exact u7840
  · exact u7841
  · exact u7842
  · exact u7843
  · exact u7844

def b19084 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 261 73 176 176 240 176 432), lower := (rows 7 74 261 73 16 32 64 128 256), losses := [] }

theorem u19084 : Upper (D 8) (R 8) [6,72,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19085 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 261 88 177 161 225 161 417), lower := (rows 7 74 261 88 16 32 64 128 256), losses := [] }

theorem u19085 : Upper (D 8) (R 8) [6,72,257,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19086 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 261 104 177 177 241 177 433), lower := (rows 7 74 261 104 16 32 64 128 256), losses := [] }

theorem u19086 : Upper (D 8) (R 8) [6,72,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19087 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 137 240 240 240 240 496), lower := (rows 7 74 261 137 16 32 64 128 256), losses := [] }

theorem u19087 : Upper (D 8) (R 8) [6,72,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19088 : Route 9 := (fun mask => (mask,id))

def c19088 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19088 : Upper (D 8) (R 8) [6,72,257,144] 13 := by
  apply FastRouting.sound _ _ [6,72,257,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19088 c19088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7845
  · exact u7846
  · exact u7847
  · exact u7848
  · exact u7849
  · exact u7850

def r19089 : Route 9 := (fun mask => (mask,id))

def c19089 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19089 : Upper (D 8) (R 8) [6,72,257,160] 13 := by
  apply FastRouting.sound _ _ [6,72,257,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19089 c19089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7851
  · exact u7852
  · exact u7853
  · exact u7854
  · exact u7855
  · exact u7856

def b19090 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 261 200 177 177 241 177 433), lower := (rows 7 74 261 200 16 32 64 128 256), losses := [] }

theorem u19090 : Upper (D 8) (R 8) [6,72,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19091 : Route 9 := (fun mask => (mask,id))

def c19091 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19091 : Upper (D 8) (R 8) [6,72,272,33] 13 := by
  apply FastRouting.sound _ _ [6,72,272,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19091 c19091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7857
  · exact u7858
  · exact u7859
  · exact u7860
  · exact u7861
  · exact u7862

def b19092 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 276 73 177 161 225 161 417), lower := (rows 7 74 276 73 16 32 64 128 256), losses := [] }

theorem u19092 : Upper (D 8) (R 8) [6,72,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19093 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 276 104 177 161 225 161 417), lower := (rows 7 74 276 104 16 32 64 128 256), losses := [] }

theorem u19093 : Upper (D 8) (R 8) [6,72,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19094 : Route 9 := (fun mask => (mask,id))

def c19094 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19094 : Upper (D 8) (R 8) [6,72,272,129] 13 := by
  apply FastRouting.sound _ _ [6,72,272,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19094 c19094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7863
  · exact u7864
  · exact u7865
  · exact u7866
  · exact u7867
  · exact u7868

def r19095 : Route 9 := (fun mask => (mask,id))

def c19095 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19095 : Upper (D 8) (R 8) [6,72,272,160] 13 := by
  apply FastRouting.sound _ _ [6,72,272,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19095 c19095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7869
  · exact u7870
  · exact u7871
  · exact u7872
  · exact u7873
  · exact u7874

def b19096 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 276 200 177 161 225 161 417), lower := (rows 7 74 276 200 16 32 64 128 256), losses := [] }

theorem u19096 : Upper (D 8) (R 8) [6,72,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19097 : Route 9 := (fun mask => (mask,id))

def c19097 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19097 : Upper (D 8) (R 8) [6,72,288,17] 13 := by
  apply FastRouting.sound _ _ [6,72,288,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19097 c19097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7875
  · exact u7876
  · exact u7877
  · exact u7878
  · exact u7879
  · exact u7880

def r19098 : Route 9 := (fun mask => (mask,id))

def c19098 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19098 : Upper (D 8) (R 8) [6,72,288,33] 13 := by
  apply FastRouting.sound _ _ [6,72,288,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19098 c19098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7881
  · exact u7882
  · exact u7883
  · exact u7884
  · exact u7885
  · exact u7886

def r19099 : Route 9 := (fun mask => (mask,id))

def c19099 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19099 : Upper (D 8) (R 8) [6,72,288,48] 13 := by
  apply FastRouting.sound _ _ [6,72,288,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19099 c19099
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7887
  · exact u7888
  · exact u7889
  · exact u7890
  · exact u7891
  · exact u7892

def b19100 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 73 177 177 241 177 433), lower := (rows 7 74 292 73 16 32 64 128 256), losses := [] }

theorem u19100 : Upper (D 8) (R 8) [6,72,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19101 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 88 177 161 225 161 417), lower := (rows 7 74 292 88 16 32 64 128 256), losses := [] }

theorem u19101 : Upper (D 8) (R 8) [6,72,288,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19102 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 104 177 177 241 177 433), lower := (rows 7 74 292 104 16 32 64 128 256), losses := [] }

theorem u19102 : Upper (D 8) (R 8) [6,72,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19103 : Route 9 := (fun mask => (mask,id))

def c19103 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19103 : Upper (D 8) (R 8) [6,72,288,129] 13 := by
  apply FastRouting.sound _ _ [6,72,288,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19103 c19103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7893
  · exact u7894
  · exact u7895
  · exact u7896
  · exact u7897
  · exact u7898

def r19104 : Route 9 := (fun mask => (mask,id))

def c19104 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19104 : Upper (D 8) (R 8) [6,72,288,144] 13 := by
  apply FastRouting.sound _ _ [6,72,288,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19104 c19104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7899
  · exact u7900
  · exact u7901
  · exact u7902
  · exact u7903
  · exact u7904

def r19105 : Route 9 := (fun mask => (mask,id))

def c19105 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19105 : Upper (D 8) (R 8) [6,72,288,160] 13 := by
  apply FastRouting.sound _ _ [6,72,288,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19105 c19105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7905
  · exact u7906
  · exact u7907
  · exact u7908
  · exact u7909
  · exact u7910

def b19106 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 292 200 177 177 241 177 433), lower := (rows 7 74 292 200 16 32 64 128 256), losses := [] }

theorem u19106 : Upper (D 8) (R 8) [6,72,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19107 : Route 9 := (fun mask => (mask,id))

def c19107 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19107 : Upper (D 8) (R 8) [6,72,384,17] 13 := by
  apply FastRouting.sound _ _ [6,72,384,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19107 c19107
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7911
  · exact u7912
  · exact u7913
  · exact u7914
  · exact u7915
  · exact u7916

def r19108 : Route 9 := (fun mask => (mask,id))

def c19108 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19108 : Upper (D 8) (R 8) [6,72,384,33] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19108 c19108
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7917
  · exact u7918
  · exact u7919
  · exact u7920
  · exact u7921
  · exact u7922

def r19109 : Route 9 := (fun mask => (mask,id))

def c19109 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19109 : Upper (D 8) (R 8) [6,72,384,48] 13 := by
  apply FastRouting.sound _ _ [6,72,384,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19109 c19109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7923
  · exact u7924
  · exact u7925
  · exact u7926
  · exact u7927
  · exact u7928

def b19110 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 388 73 177 177 241 177 433), lower := (rows 7 74 388 73 16 32 64 128 256), losses := [] }

theorem u19110 : Upper (D 8) (R 8) [6,72,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19111 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 388 88 177 161 225 161 417), lower := (rows 7 74 388 88 16 32 64 128 256), losses := [] }

theorem u19111 : Upper (D 8) (R 8) [6,72,384,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19112 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 388 104 177 177 241 177 433), lower := (rows 7 74 388 104 16 32 64 128 256), losses := [] }

theorem u19112 : Upper (D 8) (R 8) [6,72,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19113 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 388 137 113 113 113 241 369), lower := (rows 7 74 388 137 16 32 64 128 256), losses := [] }

theorem u19113 : Upper (D 8) (R 8) [6,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19114 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 388 152 113 97 97 225 353), lower := (rows 7 74 388 152 16 32 64 128 256), losses := [] }

theorem u19114 : Upper (D 8) (R 8) [6,72,384,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19115 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 388 168 113 113 113 241 369), lower := (rows 7 74 388 168 16 32 64 128 256), losses := [] }

theorem u19115 : Upper (D 8) (R 8) [6,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19116 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 388 200 49 49 113 177 305), lower := (rows 7 74 388 200 16 32 64 128 256), losses := [] }

theorem u19116 : Upper (D 8) (R 8) [6,72,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19117_129 : Upper (D 8) (R 8) [6,96,160,17,129] 13 :=
  permutation_upper _ _ _ [6,96,160,17,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7932

theorem m19117_136 : Upper (D 8) (R 8) [6,96,160,17,136] 13 :=
  permutation_upper _ _ _ [6,96,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7933

theorem m19117_160 : Upper (D 8) (R 8) [6,96,160,17,160] 13 :=
  permutation_upper _ _ _ [6,96,160,17,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7934

theorem m19117_384 : Upper (D 8) (R 8) [6,96,160,17,384] 13 :=
  permutation_upper _ _ _ [6,96,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7939

def r19117 : Route 9 := (fun mask => (mask,id))

def c19117 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u19117 : Upper (D 8) (R 8) [6,96,160,17] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r19117 c19117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7929
  · exact u7930
  · exact u7931
  · exact u7932
  · exact u7933
  · exact u7934
  · exact m19117_129
  · exact m19117_136
  · exact m19117_160
  · exact u7935
  · exact u7936
  · exact u7937
  · exact u7938
  · exact u7939
  · exact m19117_384

def b19118 : PairBound 9 := { available := 473, camps := [{ cop := 3, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 41 473 505 473 473 473), lower := (rows 7 98 164 41 16 32 64 128 256), losses := [] }

theorem u19118 : Upper (D 8) (R 8) [6,96,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19119_9 : Upper (D 8) (R 8) [6,96,160,48,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7931

theorem m19119_129 : Upper (D 8) (R 8) [6,96,160,48,129] 13 :=
  permutation_upper _ _ _ [6,96,160,48,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7945

theorem m19119_136 : Upper (D 8) (R 8) [6,96,160,48,136] 13 :=
  permutation_upper _ _ _ [6,96,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7946

theorem m19119_384 : Upper (D 8) (R 8) [6,96,160,48,384] 13 :=
  permutation_upper _ _ _ [6,96,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7950

def r19119 : Route 9 := (fun mask => (mask,id))

def c19119 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u19119 : Upper (D 8) (R 8) [6,96,160,48] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r19119 c19119
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19119_9
  · exact u7945
  · exact u7946
  · exact m19119_129
  · exact m19119_136
  · exact u7947
  · exact u7948
  · exact u7949
  · exact u7950
  · exact m19119_384

def b19120 : PairBound 9 := { available := 441, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 164 73 441 441 505 441 441), lower := (rows 7 98 164 73 16 32 64 128 256), losses := [] }

theorem u19120 : Upper (D 8) (R 8) [6,96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19121_9 : Upper (D 8) (R 8) [6,96,160,80,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7933

theorem m19121_33 : Upper (D 8) (R 8) [6,96,160,80,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7940

theorem m19121_40 : Upper (D 8) (R 8) [6,96,160,80,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7946

theorem m19121_129 : Upper (D 8) (R 8) [6,96,160,80,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7951

def r19121 : Route 9 := (fun mask => (mask,id))

def c19121 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19121 : Upper (D 8) (R 8) [6,96,160,80] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19121 c19121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19121_9
  · exact m19121_33
  · exact m19121_40
  · exact m19121_129
  · exact u7956
  · exact u7957
  · exact u7958
  · exact u7959
  · exact u7960
  · exact u7961

def b19122 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 164 104 409 441 473 409 409), lower := (rows 7 98 164 104 16 32 64 128 256), losses := [] }

theorem u19122 : Upper (D 8) (R 8) [6,96,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19123_9 : Upper (D 8) (R 8) [6,96,160,192,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7935

theorem m19123_33 : Upper (D 8) (R 8) [6,96,160,192,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7941

theorem m19123_40 : Upper (D 8) (R 8) [6,96,160,192,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7947

def r19123 : Route 9 := (fun mask => (mask,id))

def c19123 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19123 : Upper (D 8) (R 8) [6,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r19123 c19123
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19123_9
  · exact m19123_33
  · exact m19123_40
  · exact u7965
  · exact u7966
  · exact u7967

theorem m19124_9 : Upper (D 8) (R 8) [6,96,160,257,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7936

theorem m19124_33 : Upper (D 8) (R 8) [6,96,160,257,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7942

theorem m19124_40 : Upper (D 8) (R 8) [6,96,160,257,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7948

theorem m19124_65 : Upper (D 8) (R 8) [6,96,160,257,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7952

theorem m19124_72 : Upper (D 8) (R 8) [6,96,160,257,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7958

theorem m19124_96 : Upper (D 8) (R 8) [6,96,160,257,96] 13 :=
  permutation_upper _ _ _ [6,96,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7962

theorem m19124_129 : Upper (D 8) (R 8) [6,96,160,257,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7952

theorem m19124_136 : Upper (D 8) (R 8) [6,96,160,257,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7958

theorem m19124_160 : Upper (D 8) (R 8) [6,96,160,257,160] 13 :=
  permutation_upper _ _ _ [6,96,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7962

theorem m19124_192 : Upper (D 8) (R 8) [6,96,160,257,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7965

def r19124 : Route 9 := (fun mask => (mask,id))

def c19124 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19124 : Upper (D 8) (R 8) [6,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19124 c19124
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19124_9
  · exact m19124_33
  · exact m19124_40
  · exact m19124_65
  · exact m19124_72
  · exact m19124_96
  · exact m19124_129
  · exact m19124_136
  · exact m19124_160
  · exact m19124_192

theorem m19125_9 : Upper (D 8) (R 8) [6,96,160,272,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7937

theorem m19125_33 : Upper (D 8) (R 8) [6,96,160,272,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7943

theorem m19125_40 : Upper (D 8) (R 8) [6,96,160,272,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7949

theorem m19125_65 : Upper (D 8) (R 8) [6,96,160,272,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7953

theorem m19125_72 : Upper (D 8) (R 8) [6,96,160,272,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7959

theorem m19125_96 : Upper (D 8) (R 8) [6,96,160,272,96] 13 :=
  permutation_upper _ _ _ [6,96,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7963

theorem m19125_129 : Upper (D 8) (R 8) [6,96,160,272,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7953

theorem m19125_136 : Upper (D 8) (R 8) [6,96,160,272,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7959

theorem m19125_160 : Upper (D 8) (R 8) [6,96,160,272,160] 13 :=
  permutation_upper _ _ _ [6,96,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7963

theorem m19125_192 : Upper (D 8) (R 8) [6,96,160,272,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7966

def r19125 : Route 9 := (fun mask => (mask,id))

def c19125 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19125 : Upper (D 8) (R 8) [6,96,160,272] 13 := by
  apply FastRouting.sound _ _ [6,96,160,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19125 c19125
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19125_9
  · exact m19125_33
  · exact m19125_40
  · exact m19125_65
  · exact m19125_72
  · exact m19125_96
  · exact m19125_129
  · exact m19125_136
  · exact m19125_160
  · exact m19125_192

theorem m19126_9 : Upper (D 8) (R 8) [6,96,160,288,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7938

theorem m19126_65 : Upper (D 8) (R 8) [6,96,160,288,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7954

theorem m19126_72 : Upper (D 8) (R 8) [6,96,160,288,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7960

theorem m19126_129 : Upper (D 8) (R 8) [6,96,160,288,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7954

theorem m19126_136 : Upper (D 8) (R 8) [6,96,160,288,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7960

theorem m19126_192 : Upper (D 8) (R 8) [6,96,160,288,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7967

def r19126 : Route 9 := (fun mask => (mask,id))

def c19126 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19126 : Upper (D 8) (R 8) [6,96,160,288] 13 := by
  apply FastRouting.sound _ _ [6,96,160,288] 13 (by decide) (choices 2) [9,65,72,129,136,192] r19126 c19126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19126_9
  · exact m19126_65
  · exact m19126_72
  · exact m19126_129
  · exact m19126_136
  · exact m19126_192

theorem m19127_9 : Upper (D 8) (R 8) [6,96,160,320,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7939

theorem m19127_33 : Upper (D 8) (R 8) [6,96,160,320,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7944

theorem m19127_40 : Upper (D 8) (R 8) [6,96,160,320,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7950

theorem m19127_129 : Upper (D 8) (R 8) [6,96,160,320,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7955

theorem m19127_136 : Upper (D 8) (R 8) [6,96,160,320,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7961

theorem m19127_160 : Upper (D 8) (R 8) [6,96,160,320,160] 13 :=
  permutation_upper _ _ _ [6,96,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7964

def r19127 : Route 9 := (fun mask => (mask,id))

def c19127 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19127 : Upper (D 8) (R 8) [6,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19127 c19127
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19127_9
  · exact m19127_33
  · exact m19127_40
  · exact m19127_129
  · exact m19127_136
  · exact m19127_160

def b19128 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 25 248 232 232 232 488), lower := (rows 7 98 261 25 16 32 64 128 256), losses := [] }

theorem u19128 : Upper (D 8) (R 8) [6,96,257,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19129 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 41 248 248 248 248 504), lower := (rows 7 98 261 41 16 32 64 128 256), losses := [] }

theorem u19129 : Upper (D 8) (R 8) [6,96,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19130_9 : Upper (D 8) (R 8) [6,96,257,48,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7968

theorem m19130_33 : Upper (D 8) (R 8) [6,96,257,48,33] 13 :=
  permutation_upper _ _ _ [6,96,257,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7973

def r19130 : Route 9 := (fun mask => (mask,id))

def c19130 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19130 : Upper (D 8) (R 8) [6,96,257,48] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19130 c19130
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19130_9
  · exact m19130_33
  · exact u7978
  · exact u7979
  · exact u7980
  · exact u7981
  · exact u7982
  · exact u7983
  · exact u7984
  · exact u7985

def b19131 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 73 184 184 248 184 440), lower := (rows 7 98 261 73 16 32 64 128 256), losses := [] }

theorem u19131 : Upper (D 8) (R 8) [6,96,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19132_9 : Upper (D 8) (R 8) [6,96,257,80,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7969

theorem m19132_33 : Upper (D 8) (R 8) [6,96,257,80,33] 13 :=
  permutation_upper _ _ _ [6,96,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7974

theorem m19132_40 : Upper (D 8) (R 8) [6,96,257,80,40] 13 :=
  permutation_upper _ _ _ [6,96,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7980

def r19132 : Route 9 := (fun mask => (mask,id))

def c19132 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19132 : Upper (D 8) (R 8) [6,96,257,80] 13 := by
  apply FastRouting.sound _ _ [6,96,257,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19132 c19132
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19132_9
  · exact m19132_33
  · exact m19132_40
  · exact u7988
  · exact u7989
  · exact u7990

def b19133 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 104 185 185 249 185 441), lower := (rows 7 98 261 104 16 32 64 128 256), losses := [] }

theorem u19133 : Upper (D 8) (R 8) [6,96,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19134 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 137 248 248 248 248 504), lower := (rows 7 98 261 137 16 32 64 128 256), losses := [] }

theorem u19134 : Upper (D 8) (R 8) [6,96,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19135_9 : Upper (D 8) (R 8) [6,96,257,144,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7970

theorem m19135_33 : Upper (D 8) (R 8) [6,96,257,144,33] 13 :=
  permutation_upper _ _ _ [6,96,257,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7975

theorem m19135_40 : Upper (D 8) (R 8) [6,96,257,144,40] 13 :=
  permutation_upper _ _ _ [6,96,257,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7983

theorem m19135_65 : Upper (D 8) (R 8) [6,96,257,144,65] 13 :=
  permutation_upper _ _ _ [6,96,257,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7986

theorem m19135_72 : Upper (D 8) (R 8) [6,96,257,144,72] 13 :=
  permutation_upper _ _ _ [6,96,257,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7989

theorem m19135_96 : Upper (D 8) (R 8) [6,96,257,144,96] 13 :=
  permutation_upper _ _ _ [6,96,257,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7991

theorem m19135_129 : Upper (D 8) (R 8) [6,96,257,144,129] 13 :=
  permutation_upper _ _ _ [6,96,257,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7993

def r19135 : Route 9 := (fun mask => (mask,id))

def c19135 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19135 : Upper (D 8) (R 8) [6,96,257,144] 13 := by
  apply FastRouting.sound _ _ [6,96,257,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19135 c19135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19135_9
  · exact m19135_33
  · exact m19135_40
  · exact m19135_65
  · exact m19135_72
  · exact m19135_96
  · exact m19135_129
  · exact u7996
  · exact u7997
  · exact u7998

theorem m19136_9 : Upper (D 8) (R 8) [6,96,257,160,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7971

theorem m19136_33 : Upper (D 8) (R 8) [6,96,257,160,33] 13 :=
  permutation_upper _ _ _ [6,96,257,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7976

theorem m19136_40 : Upper (D 8) (R 8) [6,96,257,160,40] 13 :=
  permutation_upper _ _ _ [6,96,257,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7984

theorem m19136_65 : Upper (D 8) (R 8) [6,96,257,160,65] 13 :=
  permutation_upper _ _ _ [6,96,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7987

theorem m19136_72 : Upper (D 8) (R 8) [6,96,257,160,72] 13 :=
  permutation_upper _ _ _ [6,96,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7990

theorem m19136_96 : Upper (D 8) (R 8) [6,96,257,160,96] 13 :=
  permutation_upper _ _ _ [6,96,257,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7992

theorem m19136_129 : Upper (D 8) (R 8) [6,96,257,160,129] 13 :=
  permutation_upper _ _ _ [6,96,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7994

theorem m19136_136 : Upper (D 8) (R 8) [6,96,257,160,136] 13 :=
  permutation_upper _ _ _ [6,96,257,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7997

def r19136 : Route 9 := (fun mask => (mask,id))

def c19136 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19136 : Upper (D 8) (R 8) [6,96,257,160] 13 := by
  apply FastRouting.sound _ _ [6,96,257,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19136 c19136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19136_9
  · exact m19136_33
  · exact m19136_40
  · exact m19136_65
  · exact m19136_72
  · exact m19136_96
  · exact m19136_129
  · exact m19136_136
  · exact u7999
  · exact u8000

theorem m19137_9 : Upper (D 8) (R 8) [6,96,257,192,9] 13 :=
  permutation_upper _ _ _ [6,96,257,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7972

theorem m19137_33 : Upper (D 8) (R 8) [6,96,257,192,33] 13 :=
  permutation_upper _ _ _ [6,96,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7977

theorem m19137_40 : Upper (D 8) (R 8) [6,96,257,192,40] 13 :=
  permutation_upper _ _ _ [6,96,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7985

theorem m19137_129 : Upper (D 8) (R 8) [6,96,257,192,129] 13 :=
  permutation_upper _ _ _ [6,96,257,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7995

theorem m19137_136 : Upper (D 8) (R 8) [6,96,257,192,136] 13 :=
  permutation_upper _ _ _ [6,96,257,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7998

theorem m19137_160 : Upper (D 8) (R 8) [6,96,257,192,160] 13 :=
  permutation_upper _ _ _ [6,96,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8000

def r19137 : Route 9 := (fun mask => (mask,id))

def c19137 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19137 : Upper (D 8) (R 8) [6,96,257,192] 13 := by
  apply FastRouting.sound _ _ [6,96,257,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19137 c19137
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19137_9
  · exact m19137_33
  · exact m19137_40
  · exact m19137_129
  · exact m19137_136
  · exact m19137_160

def r19138 : Route 9 := (fun mask => (mask,id))

def c19138 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19138 : Upper (D 8) (R 8) [6,96,264,17] 13 := by
  apply FastRouting.sound _ _ [6,96,264,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19138 c19138
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8001
  · exact u8002
  · exact u8003
  · exact u8004
  · exact u8005
  · exact u8006

def r19139 : Route 9 := (fun mask => (mask,id))

def c19139 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19139 : Upper (D 8) (R 8) [6,96,264,33] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19139 c19139
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8007
  · exact u8008
  · exact u8009
  · exact u8010
  · exact u8011
  · exact u8012

#print axioms u19139
end Delivery.IrregularNine14.P08
