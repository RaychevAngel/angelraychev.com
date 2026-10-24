import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0099
import IrregularNine14P07C0100

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r20880 : Route 9 := (fun mask => (mask,id))

def c20880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20880 : Upper (D 7) (R 7) [34,257,40,65,66,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,66,128] 13 (by decide) (choices 1) [4,16,128] r20880 c20880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5968
  · exact u5969
  · exact u5970

def b20881 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 73 84 34 208 144 400), lower := (rows 35 259 44 73 84 34 64 128 256), losses := [] }

theorem u20881 : Upper (D 7) (R 7) [34,257,40,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20882 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 52, targets := 131 }], pairs := [(2,0),(2,1),(2,7)], upper := (rows 35 259 44 73 84 48 194 130 386), lower := (rows 35 259 44 73 84 48 64 128 256), losses := [] }

theorem u20882 : Upper (D 7) (R 7) [34,257,40,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20882 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20883 : Route 9 := (fun mask => (mask,id))

def c20883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20883 : Upper (D 7) (R 7) [34,257,40,65,68,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,68,128] 13 (by decide) (choices 1) [2,16,128] r20883 c20883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5971
  · exact u5972
  · exact u5973

def b20884 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 259 44 73 146 36 208 208 464), lower := (rows 35 259 44 73 146 36 64 128 256), losses := [] }

theorem u20884 : Upper (D 7) (R 7) [34,257,40,65,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20884 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20885 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 259 44 73 146 48 196 196 452), lower := (rows 35 259 44 73 146 48 64 128 256), losses := [] }

theorem u20885 : Upper (D 7) (R 7) [34,257,40,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20885 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20886 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 259 44 73 146 96 212 148 404), lower := (rows 35 259 44 73 146 96 64 128 256), losses := [] }

theorem u20886 : Upper (D 7) (R 7) [34,257,40,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20887 : Route 9 := (fun mask => (mask,id))

def c20887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20887 : Upper (D 7) (R 7) [34,257,40,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,130,128] 13 (by decide) (choices 1) [4,16] r20887 c20887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5974
  · exact u5975

def b20888 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 73 148 34 208 208 464), lower := (rows 35 259 44 73 148 34 64 128 256), losses := [] }

theorem u20888 : Upper (D 7) (R 7) [34,257,40,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20889 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(2,0),(3,5)], upper := (rows 35 259 44 73 148 48 194 194 450), lower := (rows 35 259 44 73 148 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 67 131 259), good := (rows 482 450 60 508 180 48 64 128 256) }] }

theorem u20889 : Upper (D 7) (R 7) [34,257,40,65,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20889 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20890 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 259 44 73 148 96 210 146 402), lower := (rows 35 259 44 73 148 96 64 128 256), losses := [] }

theorem u20890 : Upper (D 7) (R 7) [34,257,40,65,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20891 : Route 9 := (fun mask => (mask,id))

def c20891 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20891 : Upper (D 7) (R 7) [34,257,40,65,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,132,128] 13 (by decide) (choices 1) [2,16] r20891 c20891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5976
  · exact u5977

def b20892 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 73 208 34 212 148 404), lower := (rows 35 259 44 73 208 34 64 128 256), losses := [] }

theorem u20892 : Upper (D 7) (R 7) [34,257,40,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20893 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 259 44 73 208 36 210 146 402), lower := (rows 35 259 44 73 208 36 64 128 256), losses := [] }

theorem u20893 : Upper (D 7) (R 7) [34,257,40,65,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20893 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20894 : Route 9 := (fun mask => (mask,id))

def c20894 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20894 : Upper (D 7) (R 7) [34,257,40,65,192,16] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,192,16] 13 (by decide) (choices 1) [2,4,128] r20894 c20894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5978
  · exact u5979
  · exact u5980

def r20895 : Route 9 := (fun mask => (mask,id))

def c20895 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20895 : Upper (D 7) (R 7) [34,257,40,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,192,128] 13 (by decide) (choices 1) [2,4,16] r20895 c20895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5981
  · exact u5982
  · exact u5983

def b20896 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 44 74 81 36 208 144 400), lower := (rows 35 259 44 74 81 36 64 128 256), losses := [] }

theorem u20896 : Upper (D 7) (R 7) [34,257,40,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20896 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20897 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 259 44 74 81 48 196 132 388), lower := (rows 35 259 44 74 81 48 64 128 256), losses := [] }

theorem u20897 : Upper (D 7) (R 7) [34,257,40,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20897 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20898 : Route 9 := (fun mask => (mask,id))

def c20898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20898 : Upper (D 7) (R 7) [34,257,40,66,65,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,65,128] 13 (by decide) (choices 1) [4,16,128] r20898 c20898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5984
  · exact u5985
  · exact u5986

def b20899 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 74 84 33 208 144 400), lower := (rows 35 259 44 74 84 33 64 128 256), losses := [] }

theorem u20899 : Upper (D 7) (R 7) [34,257,40,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20900 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 259 44 74 84 48 193 129 385), lower := (rows 35 259 44 74 84 48 64 128 256), losses := [] }

theorem u20900 : Upper (D 7) (R 7) [34,257,40,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20900 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20901 : Route 9 := (fun mask => (mask,id))

def c20901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20901 : Upper (D 7) (R 7) [34,257,40,66,68,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,68,128] 13 (by decide) (choices 1) [1,16,128] r20901 c20901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5987
  · exact u5988
  · exact u5989

def b20902 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 259 44 74 145 36 208 208 464), lower := (rows 35 259 44 74 145 36 64 128 256), losses := [] }

theorem u20902 : Upper (D 7) (R 7) [34,257,40,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20902 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20903 : Route 9 := (fun mask => (mask,id))

def c20903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20903 : Upper (D 7) (R 7) [34,257,40,66,129,16] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,129,16] 13 (by decide) (choices 1) [4,128] r20903 c20903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5990
  · exact u5991

def b20904 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 259 44 74 145 96 212 148 404), lower := (rows 35 259 44 74 145 96 64 128 256), losses := [] }

theorem u20904 : Upper (D 7) (R 7) [34,257,40,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20905 : Route 9 := (fun mask => (mask,id))

def c20905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20905 : Upper (D 7) (R 7) [34,257,40,66,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,129,128] 13 (by decide) (choices 1) [4,16] r20905 c20905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5992
  · exact u5993

def b20906 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 44 74 148 33 208 208 464), lower := (rows 35 259 44 74 148 33 64 128 256), losses := [] }

theorem u20906 : Upper (D 7) (R 7) [34,257,40,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20907 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(3,5)], upper := (rows 35 259 44 74 148 48 193 193 449), lower := (rows 35 259 44 74 148 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 60 67 131 259), good := (rows 481 449 60 508 180 48 64 128 256) }] }

theorem u20907 : Upper (D 7) (R 7) [34,257,40,66,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20907 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20908 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 259 44 74 148 96 209 145 401), lower := (rows 35 259 44 74 148 96 64 128 256), losses := [] }

theorem u20908 : Upper (D 7) (R 7) [34,257,40,66,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20909 : Route 9 := (fun mask => (mask,id))

def c20909 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20909 : Upper (D 7) (R 7) [34,257,40,66,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,132,128] 13 (by decide) (choices 1) [1,16] r20909 c20909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5994
  · exact u5995

def b20910 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 259 44 74 208 33 212 148 404), lower := (rows 35 259 44 74 208 33 64 128 256), losses := [] }

theorem u20910 : Upper (D 7) (R 7) [34,257,40,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20911 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 259 44 74 208 36 209 145 401), lower := (rows 35 259 44 74 208 36 64 128 256), losses := [] }

theorem u20911 : Upper (D 7) (R 7) [34,257,40,66,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20911 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20912 : Route 9 := (fun mask => (mask,id))

def c20912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20912 : Upper (D 7) (R 7) [34,257,40,66,192,16] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,192,16] 13 (by decide) (choices 1) [1,4,128] r20912 c20912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5996
  · exact u5997
  · exact u5998

def r20913 : Route 9 := (fun mask => (mask,id))

def c20913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20913 : Upper (D 7) (R 7) [34,257,40,66,192,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,192,128] 13 (by decide) (choices 1) [1,4,16] r20913 c20913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5999
  · exact u6000
  · exact u6001

def b20914 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 76 145 34 208 208 464), lower := (rows 35 259 44 76 145 34 64 128 256), losses := [] }

theorem u20914 : Upper (D 7) (R 7) [34,257,40,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20915 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 204, targets := 1 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 35 259 44 76 145 48 194 194 450), lower := (rows 35 259 44 76 145 48 64 128 256), losses := [] }

theorem u20915 : Upper (D 7) (R 7) [34,257,40,68,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20915 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20916 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 12, targets := 131 }], pairs := [(2,0),(2,1),(2,7),(3,0)], upper := (rows 35 259 44 76 145 96 210 146 402), lower := (rows 35 259 44 76 145 96 64 128 256), losses := [] }

theorem u20916 : Upper (D 7) (R 7) [34,257,40,68,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20917 : Route 9 := (fun mask => (mask,id))

def c20917 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20917 : Upper (D 7) (R 7) [34,257,40,68,129,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,68,129,128] 13 (by decide) (choices 1) [2,16] r20917 c20917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6002
  · exact u6003

def b20918 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 76 146 33 208 208 464), lower := (rows 35 259 44 76 146 33 64 128 256), losses := [] }

theorem u20918 : Upper (D 7) (R 7) [34,257,40,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20919 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 259 44 76 146 48 193 193 449), lower := (rows 35 259 44 76 146 48 64 128 256), losses := [] }

theorem u20919 : Upper (D 7) (R 7) [34,257,40,68,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20919 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20920 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 12, targets := 131 }], pairs := [(2,0),(2,1),(2,7),(3,0)], upper := (rows 35 259 44 76 146 96 209 145 401), lower := (rows 35 259 44 76 146 96 64 128 256), losses := [] }

theorem u20920 : Upper (D 7) (R 7) [34,257,40,68,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20921 : Route 9 := (fun mask => (mask,id))

def c20921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20921 : Upper (D 7) (R 7) [34,257,40,68,130,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,68,130,128] 13 (by decide) (choices 1) [1,16] r20921 c20921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6004
  · exact u6005

def b20922 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 88 145 34 196 196 452), lower := (rows 35 259 44 88 145 34 64 128 256), losses := [] }

theorem u20922 : Upper (D 7) (R 7) [34,257,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20923 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 259 44 88 145 36 194 194 450), lower := (rows 35 259 44 88 145 36 64 128 256), losses := [] }

theorem u20923 : Upper (D 7) (R 7) [34,257,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20923 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20924 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 259 44 88 145 96 198 134 390), lower := (rows 35 259 44 88 145 96 64 128 256), losses := [] }

theorem u20924 : Upper (D 7) (R 7) [34,257,40,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20925 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 35 259 44 88 145 160 70 198 326), lower := (rows 35 259 44 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 258 44 124 176 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 33 257 44 124 177 160 64 160 256) }] }

theorem u20925 : Upper (D 7) (R 7) [34,257,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20926 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 88 146 33 196 196 452), lower := (rows 35 259 44 88 146 33 64 128 256), losses := [] }

theorem u20926 : Upper (D 7) (R 7) [34,257,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20927 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 259 44 88 146 36 193 193 449), lower := (rows 35 259 44 88 146 36 64 128 256), losses := [] }

theorem u20927 : Upper (D 7) (R 7) [34,257,40,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20927 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20928 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 259 44 88 146 96 197 133 389), lower := (rows 35 259 44 88 146 96 64 128 256), losses := [] }

theorem u20928 : Upper (D 7) (R 7) [34,257,40,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20929 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,0)], upper := (rows 35 259 44 88 146 160 69 197 325), lower := (rows 35 259 44 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 258 44 124 178 160 64 160 256) }] }

theorem u20929 : Upper (D 7) (R 7) [34,257,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20930 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 88 148 33 194 194 450), lower := (rows 35 259 44 88 148 33 64 128 256), losses := [] }

theorem u20930 : Upper (D 7) (R 7) [34,257,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20931 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 88 148 34 193 193 449), lower := (rows 35 259 44 88 148 34 64 128 256), losses := [] }

theorem u20931 : Upper (D 7) (R 7) [34,257,40,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20932 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 259 44 88 148 96 195 131 387), lower := (rows 35 259 44 88 148 96 64 128 256), losses := [] }

theorem u20932 : Upper (D 7) (R 7) [34,257,40,80,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20933 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,0)], upper := (rows 35 259 44 88 148 160 67 195 323), lower := (rows 35 259 44 88 148 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 258 44 124 180 160 64 160 256) }] }

theorem u20933 : Upper (D 7) (R 7) [34,257,40,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20934 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 200 81 34 212 148 404), lower := (rows 35 259 44 200 81 34 64 128 256), losses := [] }

theorem u20934 : Upper (D 7) (R 7) [34,257,40,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20935 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 259 44 200 81 36 210 146 402), lower := (rows 35 259 44 200 81 36 64 128 256), losses := [] }

theorem u20935 : Upper (D 7) (R 7) [34,257,40,192,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20935 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20936 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 204, targets := 1 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(2,0),(3,0)], upper := (rows 35 259 44 200 81 48 198 134 390), lower := (rows 35 259 44 200 81 48 64 128 256), losses := [] }

theorem u20936 : Upper (D 7) (R 7) [34,257,40,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20936 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20937 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 259 44 200 81 160 86 150 278), lower := (rows 35 259 44 200 81 160 64 128 256), losses := [] }

theorem u20937 : Upper (D 7) (R 7) [34,257,40,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20938 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 44 200 82 33 212 148 404), lower := (rows 35 259 44 200 82 33 64 128 256), losses := [] }

theorem u20938 : Upper (D 7) (R 7) [34,257,40,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20939 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 259 44 200 82 36 209 145 401), lower := (rows 35 259 44 200 82 36 64 128 256), losses := [] }

theorem u20939 : Upper (D 7) (R 7) [34,257,40,192,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20939 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20939
end Delivery.IrregularNine14.P07
