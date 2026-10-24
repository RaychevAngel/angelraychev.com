import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0247
import IrregularNine14P07C0248

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31920 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 7 266 37 56 81 226 194 194 450), lower := (rows 7 266 37 56 81 32 64 128 256), losses := [] }

theorem u31920 : Upper (D 7) (R 7) [6,264,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31921 : Route 9 := (fun mask => (mask,id))

def c31921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31921 : Upper (D 7) (R 7) [6,264,33,48,66] 13 := by
  apply FastRouting.sound _ _ [6,264,33,48,66] 13 (by decide) (choices 1) [1,64,128] r31921 c31921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14831
  · exact u14832
  · exact u14833

def r31922 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31922 : Upper (D 7) (R 7) [6,264,33,48,192] 13 := by
  apply FastRouting.sound _ _ [6,264,33,48,192] 13 (by decide) (choices 1) [1,2,64] r31922 c31922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14834
  · exact u14835
  · exact u14836

def b31923 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 73 50 240 208 208 464), lower := (rows 7 266 37 73 50 32 64 128 256), losses := [] }

theorem u31923 : Upper (D 7) (R 7) [6,264,33,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31924 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 7 266 37 73 82 176 240 176 432), lower := (rows 7 266 37 73 82 32 64 128 256), losses := [] }

theorem u31924 : Upper (D 7) (R 7) [6,264,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31925 : Route 9 := (fun mask => (mask,id))

def c31925 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31925 : Upper (D 7) (R 7) [6,264,33,65,96] 13 := by
  apply FastRouting.sound _ _ [6,264,33,65,96] 13 (by decide) (choices 1) [2,16,128] r31925 c31925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14837
  · exact u14838
  · exact u14839

def r31926 : Route 9 := (fun mask => (mask,id))

def c31926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31926 : Upper (D 7) (R 7) [6,264,33,65,130] 13 := by
  apply FastRouting.sound _ _ [6,264,33,65,130] 13 (by decide) (choices 1) [16,64,128] r31926 c31926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14840
  · exact u14841
  · exact u14842

def r31927 : Route 9 := (fun mask => (mask,id))

def c31927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31927 : Upper (D 7) (R 7) [6,264,33,65,160] 13 := by
  apply FastRouting.sound _ _ [6,264,33,65,160] 13 (by decide) (choices 1) [2,16,64,128] r31927 c31927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14843
  · exact u14844
  · exact u14845
  · exact u14846

def r31928 : Route 9 := (fun mask => (mask,id))

def c31928 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31928 : Upper (D 7) (R 7) [6,264,33,65,192] 13 := by
  apply FastRouting.sound _ _ [6,264,33,65,192] 13 (by decide) (choices 1) [2,16,128] r31928 c31928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14847
  · exact u14848
  · exact u14849

def b31929 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 2, region := 16, targets := 192 }], pairs := [(2,1),(4,1),(4,6),(4,7)], upper := (rows 7 266 37 74 49 240 208 208 464), lower := (rows 7 266 37 74 49 32 64 128 256), losses := [] }

theorem u31929 : Upper (D 7) (R 7) [6,264,33,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31930 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 266 37 74 81 176 240 176 432), lower := (rows 7 266 37 74 81 32 64 128 256), losses := [] }

theorem u31930 : Upper (D 7) (R 7) [6,264,33,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31931 : Route 9 := (fun mask => (mask,id))

def c31931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31931 : Upper (D 7) (R 7) [6,264,33,66,96] 13 := by
  apply FastRouting.sound _ _ [6,264,33,66,96] 13 (by decide) (choices 1) [1,16,128] r31931 c31931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14850
  · exact u14851
  · exact u14852

def b31932 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 266 37 74 145 240 240 240 496), lower := (rows 7 266 37 74 145 32 64 128 256), losses := [] }

theorem u31932 : Upper (D 7) (R 7) [6,264,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31933 : Route 9 := (fun mask => (mask,id))

def c31933 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31933 : Upper (D 7) (R 7) [6,264,33,66,160] 13 := by
  apply FastRouting.sound _ _ [6,264,33,66,160] 13 (by decide) (choices 1) [1,16,64,128] r31933 c31933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14853
  · exact u14854
  · exact u14855
  · exact u14856

def r31934 : Route 9 := (fun mask => (mask,id))

def c31934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31934 : Upper (D 7) (R 7) [6,264,33,66,192] 13 := by
  apply FastRouting.sound _ _ [6,264,33,66,192] 13 (by decide) (choices 1) [1,16,128] r31934 c31934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14857
  · exact u14858
  · exact u14859

def b31935 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 266 37 88 19 224 224 224 480), lower := (rows 7 266 37 88 19 32 64 128 256), losses := [] }

theorem u31935 : Upper (D 7) (R 7) [6,264,33,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31936 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 16, targets := 194 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6),(4,7)], upper := (rows 7 266 37 88 49 226 194 194 450), lower := (rows 7 266 37 88 49 32 64 128 256), losses := [] }

theorem u31936 : Upper (D 7) (R 7) [6,264,33,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31937 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 88 50 225 193 193 449), lower := (rows 7 266 37 88 50 32 64 128 256), losses := [] }

theorem u31937 : Upper (D 7) (R 7) [6,264,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31938 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 7 266 37 88 81 162 226 162 418), lower := (rows 7 266 37 88 81 32 64 128 256), losses := [] }

theorem u31938 : Upper (D 7) (R 7) [6,264,33,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31939 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 266 37 88 82 161 225 161 417), lower := (rows 7 266 37 88 82 32 64 128 256), losses := [] }

theorem u31939 : Upper (D 7) (R 7) [6,264,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31940 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 266 37 88 112 163 195 131 387), lower := (rows 7 266 37 88 112 32 64 128 256), losses := [] }

theorem u31940 : Upper (D 7) (R 7) [6,264,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31941 : Route 9 := (fun mask => (mask,id))

def c31941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31941 : Upper (D 7) (R 7) [6,264,33,80,129] 13 := by
  apply FastRouting.sound _ _ [6,264,33,80,129] 13 (by decide) (choices 1) [2,64,128] r31941 c31941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14860
  · exact u14861
  · exact u14862

def r31942 : Route 9 := (fun mask => (mask,id))

def c31942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31942 : Upper (D 7) (R 7) [6,264,33,80,130] 13 := by
  apply FastRouting.sound _ _ [6,264,33,80,130] 13 (by decide) (choices 1) [1,64,128] r31942 c31942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14863
  · exact u14864
  · exact u14865

def r31943 : Route 9 := (fun mask => (mask,id))

def c31943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31943 : Upper (D 7) (R 7) [6,264,33,80,160] 13 := by
  apply FastRouting.sound _ _ [6,264,33,80,160] 13 (by decide) (choices 1) [1,2,64,128] r31943 c31943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14866
  · exact u14867
  · exact u14868
  · exact u14869

def b31944 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 266 37 88 208 163 227 163 419), lower := (rows 7 266 37 88 208 32 64 128 256), losses := [] }

theorem u31944 : Upper (D 7) (R 7) [6,264,33,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31945 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 7 266 37 104 19 240 208 208 464), lower := (rows 7 266 37 104 19 32 64 128 256), losses := [] }

theorem u31945 : Upper (D 7) (R 7) [6,264,33,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31946 : Route 9 := (fun mask => (mask,id))

def c31946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31946 : Upper (D 7) (R 7) [6,264,33,96,65] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,65] 13 (by decide) (choices 1) [2,16,128] r31946 c31946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14870
  · exact u14871
  · exact u14872

def r31947 : Route 9 := (fun mask => (mask,id))

def c31947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31947 : Upper (D 7) (R 7) [6,264,33,96,66] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,66] 13 (by decide) (choices 1) [1,16,128] r31947 c31947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14873
  · exact u14874
  · exact u14875

def r31948 : Route 9 := (fun mask => (mask,id))

def c31948 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31948 : Upper (D 7) (R 7) [6,264,33,96,129] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,129] 13 (by decide) (choices 1) [2,16,64,128] r31948 c31948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14876
  · exact u14877
  · exact u14878
  · exact u14879

def r31949 : Route 9 := (fun mask => (mask,id))

def c31949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31949 : Upper (D 7) (R 7) [6,264,33,96,130] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,130] 13 (by decide) (choices 1) [1,16,64,128] r31949 c31949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14880
  · exact u14881
  · exact u14882
  · exact u14883

def r31950 : Route 9 := (fun mask => (mask,id))

def c31950 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31950 : Upper (D 7) (R 7) [6,264,33,96,192] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,192] 13 (by decide) (choices 1) [1,2,16,128] r31950 c31950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14884
  · exact u14885
  · exact u14886
  · exact u14887

def b31951 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 266 37 200 19 240 240 240 496), lower := (rows 7 266 37 200 19 32 64 128 256), losses := [] }

theorem u31951 : Upper (D 7) (R 7) [6,264,33,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31952 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 16, targets := 194 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6),(4,7)], upper := (rows 7 266 37 200 49 242 210 210 466), lower := (rows 7 266 37 200 49 32 64 128 256), losses := [] }

theorem u31952 : Upper (D 7) (R 7) [6,264,33,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31953 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 200 50 241 209 209 465), lower := (rows 7 266 37 200 50 32 64 128 256), losses := [] }

theorem u31953 : Upper (D 7) (R 7) [6,264,33,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31954 : Route 9 := (fun mask => (mask,id))

def c31954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31954 : Upper (D 7) (R 7) [6,264,33,192,65] 13 := by
  apply FastRouting.sound _ _ [6,264,33,192,65] 13 (by decide) (choices 1) [2,16,128] r31954 c31954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14888
  · exact u14889
  · exact u14890

def r31955 : Route 9 := (fun mask => (mask,id))

def c31955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31955 : Upper (D 7) (R 7) [6,264,33,192,66] 13 := by
  apply FastRouting.sound _ _ [6,264,33,192,66] 13 (by decide) (choices 1) [1,16,128] r31955 c31955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14891
  · exact u14892
  · exact u14893

def r31956 : Route 9 := (fun mask => (mask,id))

def c31956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31956 : Upper (D 7) (R 7) [6,264,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,264,33,192,96] 13 (by decide) (choices 1) [1,2,16,128] r31956 c31956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14894
  · exact u14895
  · exact u14896
  · exact u14897

def b31957 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 266 37 200 208 51 115 179 307), lower := (rows 7 266 37 200 208 32 64 128 256), losses := [] }

theorem u31957 : Upper (D 7) (R 7) [6,264,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31958 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 7 266 52 41 19 224 192 192 448), lower := (rows 7 266 52 41 19 32 64 128 256), losses := [] }

theorem u31958 : Upper (D 7) (R 7) [6,264,48,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31959 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(2,0),(4,5)], upper := (rows 7 266 52 41 81 226 194 194 450), lower := (rows 7 266 52 41 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 52 490 500 32 64 128 256) }] }

theorem u31959 : Upper (D 7) (R 7) [6,264,48,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31960 : Route 9 := (fun mask => (mask,id))

def c31960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31960 : Upper (D 7) (R 7) [6,264,48,33,66] 13 := by
  apply FastRouting.sound _ _ [6,264,48,33,66] 13 (by decide) (choices 1) [1,64,128] r31960 c31960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14898
  · exact u14899
  · exact u14900

def r31961 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31961 : Upper (D 7) (R 7) [6,264,48,33,192] 13 := by
  apply FastRouting.sound _ _ [6,264,48,33,192] 13 (by decide) (choices 1) [1,2,64] r31961 c31961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14901
  · exact u14902
  · exact u14903

def r31962 : Route 9 := (fun mask => (mask,id))

def c31962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31962 : Upper (D 7) (R 7) [6,264,48,34,65] 13 := by
  apply FastRouting.sound _ _ [6,264,48,34,65] 13 (by decide) (choices 1) [1,64,128] r31962 c31962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14904
  · exact u14905
  · exact u14906

def r31963 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31963 : Upper (D 7) (R 7) [6,264,48,34,192] 13 := by
  apply FastRouting.sound _ _ [6,264,48,34,192] 13 (by decide) (choices 1) [1,64] r31963 c31963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14907
  · exact u14908

def b31964 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 266 52 73 19 224 224 224 480), lower := (rows 7 266 52 73 19 32 64 128 256), losses := [] }

theorem u31964 : Upper (D 7) (R 7) [6,264,48,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31965 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 73 49 226 194 194 450), lower := (rows 7 266 52 73 49 32 64 128 256), losses := [] }

theorem u31965 : Upper (D 7) (R 7) [6,264,48,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31966 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 52 73 50 225 193 193 449), lower := (rows 7 266 52 73 50 32 64 128 256), losses := [] }

theorem u31966 : Upper (D 7) (R 7) [6,264,48,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31967 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 7 266 52 73 81 162 226 162 418), lower := (rows 7 266 52 73 81 32 64 128 256), losses := [] }

theorem u31967 : Upper (D 7) (R 7) [6,264,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31968 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 0, region := 232, targets := 2 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 7 266 52 73 82 161 225 161 417), lower := (rows 7 266 52 73 82 32 64 128 256), losses := [] }

theorem u31968 : Upper (D 7) (R 7) [6,264,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31969 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 73 112 163 195 131 387), lower := (rows 7 266 52 73 112 32 64 128 256), losses := [] }

theorem u31969 : Upper (D 7) (R 7) [6,264,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31970 : Route 9 := (fun mask => (mask,id))

def c31970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31970 : Upper (D 7) (R 7) [6,264,48,65,129] 13 := by
  apply FastRouting.sound _ _ [6,264,48,65,129] 13 (by decide) (choices 1) [2,64,128] r31970 c31970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14909
  · exact u14910
  · exact u14911

def r31971 : Route 9 := (fun mask => (mask,id))

def c31971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31971 : Upper (D 7) (R 7) [6,264,48,65,130] 13 := by
  apply FastRouting.sound _ _ [6,264,48,65,130] 13 (by decide) (choices 1) [1,64,128] r31971 c31971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14912
  · exact u14913
  · exact u14914

def b31972 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 73 176 227 195 195 451), lower := (rows 7 266 52 73 176 32 64 128 256), losses := [] }

theorem u31972 : Upper (D 7) (R 7) [6,264,48,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31973 : Route 9 := (fun mask => (mask,id))

def c31973 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31973 : Upper (D 7) (R 7) [6,264,48,65,192] 13 := by
  apply FastRouting.sound _ _ [6,264,48,65,192] 13 (by decide) (choices 1) [1,2,128] r31973 c31973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14915
  · exact u14916
  · exact u14917

def b31974 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 459, targets := 32 },{ cop := 4, region := 4, targets := 1 }], pairs := [(0,5),(1,5),(2,0),(3,5)], upper := (rows 7 266 52 74 49 225 193 193 449), lower := (rows 7 266 52 74 49 32 64 128 256), losses := [] }

theorem u31974 : Upper (D 7) (R 7) [6,264,48,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31975 : Route 9 := (fun mask => (mask,id))

def c31975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31975 : Upper (D 7) (R 7) [6,264,48,66,65] 13 := by
  apply FastRouting.sound _ _ [6,264,48,66,65] 13 (by decide) (choices 1) [1,128] r31975 c31975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14918
  · exact u14919

def b31976 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 74 112 161 193 129 385), lower := (rows 7 266 52 74 112 32 64 128 256), losses := [] }

theorem u31976 : Upper (D 7) (R 7) [6,264,48,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31977 : Route 9 := (fun mask => (mask,id))

def c31977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31977 : Upper (D 7) (R 7) [6,264,48,66,129] 13 := by
  apply FastRouting.sound _ _ [6,264,48,66,129] 13 (by decide) (choices 1) [1,64,128] r31977 c31977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14920
  · exact u14921
  · exact u14922

def b31978 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 74 176 225 193 193 449), lower := (rows 7 266 52 74 176 32 64 128 256), losses := [] }

theorem u31978 : Upper (D 7) (R 7) [6,264,48,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31979 : Route 9 := (fun mask => (mask,id))

def c31979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31979 : Upper (D 7) (R 7) [6,264,48,66,192] 13 := by
  apply FastRouting.sound _ _ [6,264,48,66,192] 13 (by decide) (choices 1) [1,128] r31979 c31979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14923
  · exact u14924

#print axioms u31979
end Delivery.IrregularNine14.P07
