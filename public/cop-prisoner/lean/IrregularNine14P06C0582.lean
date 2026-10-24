import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0309
import IrregularNine14P06C0310

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34920 : Route 9 := (fun mask => (mask,id))

def c34920 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34920 : Upper (D 6) (R 6) [24,33,192,65,258] 13 := by
  apply FastRouting.sound _ _ [24,33,192,65,258] 13 (by decide) (choices 1) [2,4] r34920 c34920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18574
  · exact u18575

def r34921 : Route 9 := (fun mask => (mask,id))

def c34921 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34921 : Upper (D 6) (R 6) [24,33,192,65,260] 13 := by
  apply FastRouting.sound _ _ [24,33,192,65,260] 13 (by decide) (choices 1) [2,4] r34921 c34921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18576
  · exact u18577

def b34922 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 196 73 304 38 70 134 262), lower := (rows 25 35 196 73 304 32 64 128 256), losses := [] }

theorem u34922 : Upper (D 6) (R 6) [24,33,192,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34923 : Route 9 := (fun mask => (mask,id))

def c34923 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34923 : Upper (D 6) (R 6) [24,33,192,66,257] 13 := by
  apply FastRouting.sound _ _ [24,33,192,66,257] 13 (by decide) (choices 1) [2,4] r34923 c34923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18578
  · exact u18579

def r34924 : Route 9 := (fun mask => (mask,id))

def c34924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34924 : Upper (D 6) (R 6) [24,33,192,66,258] 13 := by
  apply FastRouting.sound _ _ [24,33,192,66,258] 13 (by decide) (choices 1) [1,4] r34924 c34924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18580
  · exact u18581

def r34925 : Route 9 := (fun mask => (mask,id))

def c34925 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34925 : Upper (D 6) (R 6) [24,33,192,66,260] 13 := by
  apply FastRouting.sound _ _ [24,33,192,66,260] 13 (by decide) (choices 1) [1,2,4] r34925 c34925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18582
  · exact u18583
  · exact u18584

def r34926 : Route 9 := (fun mask => (mask,id))

def c34926 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34926 : Upper (D 6) (R 6) [24,33,192,66,288] 13 := by
  apply FastRouting.sound _ _ [24,33,192,66,288] 13 (by decide) (choices 1) [1,2,4] r34926 c34926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18585
  · exact u18586
  · exact u18587

def b34927 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 196 76 273 38 102 166 294), lower := (rows 25 35 196 76 273 32 64 128 256), losses := [] }

theorem u34927 : Upper (D 6) (R 6) [24,33,192,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34928 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 196 76 274 39 103 167 295), lower := (rows 25 35 196 76 274 32 64 128 256), losses := [] }

theorem u34928 : Upper (D 6) (R 6) [24,33,192,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34929 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 196 76 276 35 99 163 291), lower := (rows 25 35 196 76 276 32 64 128 256), losses := [] }

theorem u34929 : Upper (D 6) (R 6) [24,33,192,68,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34930 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 196 76 304 39 71 135 263), lower := (rows 25 35 196 76 304 32 64 128 256), losses := [] }

theorem u34930 : Upper (D 6) (R 6) [24,33,192,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34931 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 196 104 273 38 70 134 262), lower := (rows 25 35 196 104 273 32 64 128 256), losses := [] }

theorem u34931 : Upper (D 6) (R 6) [24,33,192,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34932 : Route 9 := (fun mask => (mask,id))

def c34932 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34932 : Upper (D 6) (R 6) [24,33,192,96,258] 13 := by
  apply FastRouting.sound _ _ [24,33,192,96,258] 13 (by decide) (choices 1) [1,2,4] r34932 c34932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18588
  · exact u18589
  · exact u18590

def r34933 : Route 9 := (fun mask => (mask,id))

def c34933 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34933 : Upper (D 6) (R 6) [24,33,192,96,260] 13 := by
  apply FastRouting.sound _ _ [24,33,192,96,260] 13 (by decide) (choices 1) [1,2,4] r34933 c34933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18591
  · exact u18592
  · exact u18593

def b34934 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 388 11 22 100 100 228 356), lower := (rows 25 35 388 11 22 32 64 128 256), losses := [] }

theorem u34934 : Upper (D 6) (R 6) [24,33,384,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34935 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 388 11 52 102 70 198 326), lower := (rows 25 35 388 11 52 32 64 128 256), losses := [] }

theorem u34935 : Upper (D 6) (R 6) [24,33,384,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34936 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 388 11 82 100 100 228 356), lower := (rows 25 35 388 11 82 32 64 128 256), losses := [] }

theorem u34936 : Upper (D 6) (R 6) [24,33,384,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34937 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 388 11 84 102 102 230 358), lower := (rows 25 35 388 11 84 32 64 128 256), losses := [] }

theorem u34937 : Upper (D 6) (R 6) [24,33,384,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34938 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 388 11 112 102 70 198 326), lower := (rows 25 35 388 11 112 32 64 128 256), losses := [] }

theorem u34938 : Upper (D 6) (R 6) [24,33,384,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34939 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 388 13 22 98 98 226 354), lower := (rows 25 35 388 13 22 32 64 128 256), losses := [] }

theorem u34939 : Upper (D 6) (R 6) [24,33,384,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34940 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 35 388 13 50 102 70 198 326), lower := (rows 25 35 388 13 50 32 64 128 256), losses := [] }

theorem u34940 : Upper (D 6) (R 6) [24,33,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34941 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 388 13 52 98 66 194 322), lower := (rows 25 35 388 13 52 32 64 128 256), losses := [] }

theorem u34941 : Upper (D 6) (R 6) [24,33,384,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34942 : Route 9 := (fun mask => (mask,id))

def c34942 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34942 : Upper (D 6) (R 6) [24,33,384,5,66] 13 := by
  apply FastRouting.sound _ _ [24,33,384,5,66] 13 (by decide) (choices 1) [2,4,64] r34942 c34942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18594
  · exact u18595
  · exact u18596

def b34943 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 388 13 84 98 98 226 354), lower := (rows 25 35 388 13 84 32 64 128 256), losses := [] }

theorem u34943 : Upper (D 6) (R 6) [24,33,384,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34944 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 388 13 112 102 70 198 326), lower := (rows 25 35 388 13 112 32 64 128 256), losses := [] }

theorem u34944 : Upper (D 6) (R 6) [24,33,384,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34945 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 35 388 14 22 97 97 225 353), lower := (rows 25 35 388 14 22 32 64 128 256), losses := [] }

theorem u34945 : Upper (D 6) (R 6) [24,33,384,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34946 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 16, targets := 4 }], pairs := [(2,0),(3,0),(4,2)], upper := (rows 25 35 388 14 49 102 70 198 326), lower := (rows 25 35 388 14 49 32 64 128 256), losses := [] }

theorem u34946 : Upper (D 6) (R 6) [24,33,384,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34947 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 35 388 14 50 101 69 197 325), lower := (rows 25 35 388 14 50 32 64 128 256), losses := [] }

theorem u34947 : Upper (D 6) (R 6) [24,33,384,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34948 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 388 14 52 99 67 195 323), lower := (rows 25 35 388 14 52 32 64 128 256), losses := [] }

theorem u34948 : Upper (D 6) (R 6) [24,33,384,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34949 : Route 9 := (fun mask => (mask,id))

def c34949 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34949 : Upper (D 6) (R 6) [24,33,384,6,65] 13 := by
  apply FastRouting.sound _ _ [24,33,384,6,65] 13 (by decide) (choices 1) [2,4,64] r34949 c34949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18597
  · exact u18598
  · exact u18599

def r34950 : Route 9 := (fun mask => (mask,id))

def c34950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34950 : Upper (D 6) (R 6) [24,33,384,6,66] 13 := by
  apply FastRouting.sound _ _ [24,33,384,6,66] 13 (by decide) (choices 1) [1,4,64] r34950 c34950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18600
  · exact u18601
  · exact u18602

def r34951 : Route 9 := (fun mask => (mask,id))

def c34951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34951 : Upper (D 6) (R 6) [24,33,384,6,68] 13 := by
  apply FastRouting.sound _ _ [24,33,384,6,68] 13 (by decide) (choices 1) [1,2,64] r34951 c34951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18603
  · exact u18604
  · exact u18605

def r34952 : Route 9 := (fun mask => (mask,id))

def c34952 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34952 : Upper (D 6) (R 6) [24,33,384,6,96] 13 := by
  apply FastRouting.sound _ _ [24,33,384,6,96] 13 (by decide) (choices 1) [1,2,4,64] r34952 c34952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18606
  · exact u18607
  · exact u18608
  · exact u18609

def b34953 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 388 41 82 102 70 198 326), lower := (rows 25 35 388 41 82 32 64 128 256), losses := [] }

theorem u34953 : Upper (D 6) (R 6) [24,33,384,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34954 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 388 41 84 102 70 198 326), lower := (rows 25 35 388 41 84 32 64 128 256), losses := [] }

theorem u34954 : Upper (D 6) (R 6) [24,33,384,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34955 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 388 42 81 102 70 198 326), lower := (rows 25 35 388 42 81 32 64 128 256), losses := [] }

theorem u34955 : Upper (D 6) (R 6) [24,33,384,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34956 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 388 42 82 101 69 197 325), lower := (rows 25 35 388 42 82 32 64 128 256), losses := [] }

theorem u34956 : Upper (D 6) (R 6) [24,33,384,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34957 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 388 42 84 103 71 199 327), lower := (rows 25 35 388 42 84 32 64 128 256), losses := [] }

theorem u34957 : Upper (D 6) (R 6) [24,33,384,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34958 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 388 44 81 102 70 198 326), lower := (rows 25 35 388 44 81 32 64 128 256), losses := [] }

theorem u34958 : Upper (D 6) (R 6) [24,33,384,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34959 : Route 9 := (fun mask => (mask,id))

def c34959 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34959 : Upper (D 6) (R 6) [24,33,384,36,66] 13 := by
  apply FastRouting.sound _ _ [24,33,384,36,66] 13 (by decide) (choices 1) [1,2,4,64] r34959 c34959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18610
  · exact u18611
  · exact u18612
  · exact u18613

def b34960 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 388 44 84 99 67 195 323), lower := (rows 25 35 388 44 84 32 64 128 256), losses := [] }

theorem u34960 : Upper (D 6) (R 6) [24,33,384,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34961 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 35 388 73 82 38 102 166 294), lower := (rows 25 35 388 73 82 32 64 128 256), losses := [] }

theorem u34961 : Upper (D 6) (R 6) [24,33,384,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34962 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 35 388 73 84 38 102 166 294), lower := (rows 25 35 388 73 84 32 64 128 256), losses := [] }

theorem u34962 : Upper (D 6) (R 6) [24,33,384,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34963 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 388 73 112 38 70 134 262), lower := (rows 25 35 388 73 112 32 64 128 256), losses := [] }

theorem u34963 : Upper (D 6) (R 6) [24,33,384,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34964 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 388 74 82 37 101 165 293), lower := (rows 25 35 388 74 82 32 64 128 256), losses := [] }

theorem u34964 : Upper (D 6) (R 6) [24,33,384,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34965 : Route 9 := (fun mask => (mask,id))

def c34965 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34965 : Upper (D 6) (R 6) [24,33,384,66,68] 13 := by
  apply FastRouting.sound _ _ [24,33,384,66,68] 13 (by decide) (choices 1) [1,2,4] r34965 c34965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18614
  · exact u18615
  · exact u18616

def b34966 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 388 74 112 39 71 135 263), lower := (rows 25 35 388 74 112 32 64 128 256), losses := [] }

theorem u34966 : Upper (D 6) (R 6) [24,33,384,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34967 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 17, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 388 76 84 35 99 163 291), lower := (rows 25 35 388 76 84 32 64 128 256), losses := [] }

theorem u34967 : Upper (D 6) (R 6) [24,33,384,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34968 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 1, region := 388, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 25 35 388 76 112 39 71 135 263), lower := (rows 25 35 388 76 112 32 64 128 256), losses := [] }

theorem u34968 : Upper (D 6) (R 6) [24,33,384,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34969 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 70 11 21 480 480 480 480), lower := (rows 25 38 70 11 21 32 64 128 256), losses := [] }

theorem u34969 : Upper (D 6) (R 6) [24,36,66,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34970 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 70 11 49 484 452 452 452), lower := (rows 25 38 70 11 49 32 64 128 256), losses := [] }

theorem u34970 : Upper (D 6) (R 6) [24,36,66,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34971 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 11 52 481 449 449 449), lower := (rows 25 38 70 11 52 32 64 128 256), losses := [] }

theorem u34971 : Upper (D 6) (R 6) [24,36,66,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34972 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 11 81 420 484 420 420), lower := (rows 25 38 70 11 81 32 64 128 256), losses := [] }

theorem u34972 : Upper (D 6) (R 6) [24,36,66,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34973 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 70 11 84 417 481 417 417), lower := (rows 25 38 70 11 84 32 64 128 256), losses := [] }

theorem u34973 : Upper (D 6) (R 6) [24,36,66,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34974 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 6, targets := 1 },{ cop := 3, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 70 11 112 421 453 389 389), lower := (rows 25 38 70 11 112 32 64 128 256), losses := [] }

theorem u34974 : Upper (D 6) (R 6) [24,36,66,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34975 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 358, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 70 11 145 356 356 484 356), lower := (rows 25 38 70 11 145 32 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 38 70 134 262), good := (rows 25 484 484 505 145 32 64 128 256) }] }

theorem u34975 : Upper (D 6) (R 6) [24,36,66,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34976 : Route 9 := (fun mask => (mask,id))

def c34976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34976 : Upper (D 6) (R 6) [24,36,66,3,132] 13 := by
  apply FastRouting.sound _ _ [24,36,66,3,132] 13 (by decide) (choices 1) [1,64,256] r34976 c34976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18617
  · exact u18618
  · exact u18619

def r34977 : Route 9 := (fun mask => (mask,id))

def c34977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34977 : Upper (D 6) (R 6) [24,36,66,3,160] 13 := by
  apply FastRouting.sound _ _ [24,36,66,3,160] 13 (by decide) (choices 1) [1,4,64,256] r34977 c34977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18620
  · exact u18621
  · exact u18622
  · exact u18623

def r34978 : Route 9 := (fun mask => (mask,id))

def c34978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34978 : Upper (D 6) (R 6) [24,36,66,3,192] 13 := by
  apply FastRouting.sound _ _ [24,36,66,3,192] 13 (by decide) (choices 1) [1,4,256] r34978 c34978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18624
  · exact u18625
  · exact u18626

def r34979 : Route 9 := (fun mask => (mask,id))

def c34979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34979 : Upper (D 6) (R 6) [24,36,66,3,384] 13 := by
  apply FastRouting.sound _ _ [24,36,66,3,384] 13 (by decide) (choices 1) [1,4,64] r34979 c34979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18627
  · exact u18628
  · exact u18629

#print axioms u34979
end Delivery.IrregularNine14.P06
