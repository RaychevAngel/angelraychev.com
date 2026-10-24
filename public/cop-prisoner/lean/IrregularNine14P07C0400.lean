import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0130
import IrregularNine14P07C0131

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24000 : Route 9 := (fun mask => (mask,id))

def c24000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24000 : Upper (D 7) (R 7) [36,96,129,65,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,258,16] 13 (by decide) (choices 1) [2,8,128] r24000 c24000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7833
  · exact u7834
  · exact u7835

def b24001 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 73 274 160 90 154 282), lower := (rows 37 98 133 73 274 160 64 128 256), losses := [] }

theorem u24001 : Upper (D 7) (R 7) [36,96,129,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24002 : Route 9 := (fun mask => (mask,id))

def c24002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24002 : Upper (D 7) (R 7) [36,96,129,65,264,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,264,2] 13 (by decide) (choices 1) [2,16,128] r24002 c24002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7836
  · exact u7837
  · exact u7838

def b24003 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 133 73 280 48 194 130 386), lower := (rows 37 98 133 73 280 48 64 128 256), losses := [] }

theorem u24003 : Upper (D 7) (R 7) [36,96,129,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24003 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24004 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 73 280 160 82 146 274), lower := (rows 37 98 133 73 280 160 64 128 256), losses := [] }

theorem u24004 : Upper (D 7) (R 7) [36,96,129,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24005 : Route 9 := (fun mask => (mask,id))

def c24005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24005 : Upper (D 7) (R 7) [36,96,129,65,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,384,2] 13 (by decide) (choices 1) [2,8,16] r24005 c24005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7839
  · exact u7840
  · exact u7841

def b24006 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 73 400 40 82 146 274), lower := (rows 37 98 133 73 400 40 64 128 256), losses := [] }

theorem u24006 : Upper (D 7) (R 7) [36,96,129,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24006 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24007 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 73 400 48 74 138 266), lower := (rows 37 98 133 73 400 48 64 128 256), losses := [] }

theorem u24007 : Upper (D 7) (R 7) [36,96,129,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24007 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24008 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 88 146 33 330 394 266), lower := (rows 37 98 133 88 146 33 64 128 256), losses := [] }

theorem u24008 : Upper (D 7) (R 7) [36,96,129,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24009 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 133 88 146 34 329 393 265), lower := (rows 37 98 133 88 146 34 64 128 256), losses := [] }

theorem u24009 : Upper (D 7) (R 7) [36,96,129,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24010 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 88 146 40 323 387 259), lower := (rows 37 98 133 88 146 40 64 128 256), losses := [] }

theorem u24010 : Upper (D 7) (R 7) [36,96,129,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24010 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24011 : Route 9 := (fun mask => (mask,id))

def c24011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24011 : Upper (D 7) (R 7) [36,96,129,80,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,130,256] 13 (by decide) (choices 1) [1,2,8] r24011 c24011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7842
  · exact u7843
  · exact u7844

def r24012 : Route 9 := (fun mask => (mask,id))

def c24012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24012 : Upper (D 7) (R 7) [36,96,129,80,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,257,2] 13 (by decide) (choices 1) [2,8,128] r24012 c24012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7845
  · exact u7846
  · exact u7847

def b24013 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 88 273 40 194 130 386), lower := (rows 37 98 133 88 273 40 64 128 256), losses := [] }

theorem u24013 : Upper (D 7) (R 7) [36,96,129,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24013 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24014 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 88 273 160 74 138 266), lower := (rows 37 98 133 88 273 160 64 128 256), losses := [] }

theorem u24014 : Upper (D 7) (R 7) [36,96,129,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24015 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 88 274 33 202 138 394), lower := (rows 37 98 133 88 274 33 64 128 256), losses := [] }

theorem u24015 : Upper (D 7) (R 7) [36,96,129,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24016 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 133 88 274 34 201 137 393), lower := (rows 37 98 133 88 274 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 136 264), good := (rows 37 34 133 445 306 34 0 128 256) }] }

theorem u24016 : Upper (D 7) (R 7) [36,96,129,80,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24017 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 88 274 40 195 131 387), lower := (rows 37 98 133 88 274 40 64 128 256), losses := [] }

theorem u24017 : Upper (D 7) (R 7) [36,96,129,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24017 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24018 : PairBound 9 := { available := 11, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 88 274 160 75 139 267), lower := (rows 37 98 133 88 274 160 64 128 256), losses := [] }

theorem u24018 : Upper (D 7) (R 7) [36,96,129,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24019 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 88 280 33 194 130 386), lower := (rows 37 98 133 88 280 33 64 128 256), losses := [] }

theorem u24019 : Upper (D 7) (R 7) [36,96,129,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24020 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 3, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 133 88 280 34 195 131 387), lower := (rows 37 98 133 88 280 34 64 128 256), losses := [] }

theorem u24020 : Upper (D 7) (R 7) [36,96,129,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24021 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 88 280 160 67 131 259), lower := (rows 37 98 133 88 280 160 64 128 256), losses := [] }

theorem u24021 : Upper (D 7) (R 7) [36,96,129,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24022 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 88 400 33 74 138 266), lower := (rows 37 98 133 88 400 33 64 128 256), losses := [] }

theorem u24022 : Upper (D 7) (R 7) [36,96,129,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24023 : Route 9 := (fun mask => (mask,id))

def c24023 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24023 : Upper (D 7) (R 7) [36,96,129,80,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80,384,2] 13 (by decide) (choices 1) [1,2,8] r24023 c24023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7848
  · exact u7849
  · exact u7850

def b24024 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 88 400 40 67 131 259), lower := (rows 37 98 133 88 400 40 64 128 256), losses := [] }

theorem u24024 : Upper (D 7) (R 7) [36,96,129,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24024 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24025 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 98 133 138 273 34 88 216 344), lower := (rows 37 98 133 138 273 34 64 128 256), losses := [] }

theorem u24025 : Upper (D 7) (R 7) [36,96,129,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24026 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 138 273 40 82 210 338), lower := (rows 37 98 133 138 273 40 64 128 256), losses := [] }

theorem u24026 : Upper (D 7) (R 7) [36,96,129,130,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24026 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24027 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 133 138 273 48 74 202 330), lower := (rows 37 98 133 138 273 48 64 128 256), losses := [] }

theorem u24027 : Upper (D 7) (R 7) [36,96,129,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24027 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24028 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 138 273 96 90 154 282), lower := (rows 37 98 133 138 273 96 64 128 256), losses := [] }

theorem u24028 : Upper (D 7) (R 7) [36,96,129,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24029 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 138 274 33 88 216 344), lower := (rows 37 98 133 138 274 33 64 128 256), losses := [] }

theorem u24029 : Upper (D 7) (R 7) [36,96,129,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24030 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 138 274 40 81 209 337), lower := (rows 37 98 133 138 274 40 64 128 256), losses := [] }

theorem u24030 : Upper (D 7) (R 7) [36,96,129,130,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24030 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24031 : Route 9 := (fun mask => (mask,id))

def c24031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24031 : Upper (D 7) (R 7) [36,96,129,130,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,129,130,258,16] 13 (by decide) (choices 1) [1,8] r24031 c24031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7851
  · exact u7852

def b24032 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 138 274 96 89 153 281), lower := (rows 37 98 133 138 274 96 64 128 256), losses := [] }

theorem u24032 : Upper (D 7) (R 7) [36,96,129,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24033 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 138 280 33 82 210 338), lower := (rows 37 98 133 138 280 33 64 128 256), losses := [] }

theorem u24033 : Upper (D 7) (R 7) [36,96,129,130,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24034 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 6, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 133 138 280 34 81 209 337), lower := (rows 37 98 133 138 280 34 64 128 256), losses := [] }

theorem u24034 : Upper (D 7) (R 7) [36,96,129,130,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24035 : Route 9 := (fun mask => (mask,id))

def c24035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24035 : Upper (D 7) (R 7) [36,96,129,130,264,16] 13 := by
  apply FastRouting.sound _ _ [36,96,129,130,264,16] 13 (by decide) (choices 1) [1,2] r24035 c24035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7853
  · exact u7854

def b24036 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 138 280 96 83 147 275), lower := (rows 37 98 133 138 280 96 64 128 256), losses := [] }

theorem u24036 : Upper (D 7) (R 7) [36,96,129,130,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24037 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 138 336 33 90 154 282), lower := (rows 37 98 133 138 336 33 64 128 256), losses := [] }

theorem u24037 : Upper (D 7) (R 7) [36,96,129,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24038 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 4, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 133 138 336 34 89 153 281), lower := (rows 37 98 133 138 336 34 64 128 256), losses := [] }

theorem u24038 : Upper (D 7) (R 7) [36,96,129,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24039 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 138 336 40 83 147 275), lower := (rows 37 98 133 138 336 40 64 128 256), losses := [] }

theorem u24039 : Upper (D 7) (R 7) [36,96,129,130,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24039 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24040 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 133 138 336 48 75 139 267), lower := (rows 37 98 133 138 336 48 64 128 256), losses := [] }

theorem u24040 : Upper (D 7) (R 7) [36,96,129,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24040 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24041 : Route 9 := (fun mask => (mask,id))

def c24041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24041 : Upper (D 7) (R 7) [36,96,129,144,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,144,257,2] 13 (by decide) (choices 1) [2,8] r24041 c24041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7855
  · exact u7856

def b24042 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 152 273 40 66 194 322), lower := (rows 37 98 133 152 273 40 64 128 256), losses := [] }

theorem u24042 : Upper (D 7) (R 7) [36,96,129,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24042 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24043 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 152 273 96 74 138 266), lower := (rows 37 98 133 152 273 96 64 128 256), losses := [] }

theorem u24043 : Upper (D 7) (R 7) [36,96,129,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24044 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 152 274 33 74 202 330), lower := (rows 37 98 133 152 274 33 64 128 256), losses := [] }

theorem u24044 : Upper (D 7) (R 7) [36,96,129,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24045 : PairBound 9 := { available := 73, camps := [{ cop := 6, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 133 152 274 34 73 201 329), lower := (rows 37 98 133 152 274 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 128 256), good := (rows 37 34 133 189 306 34 0 128 256) }] }

theorem u24045 : Upper (D 7) (R 7) [36,96,129,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24046 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 152 274 40 67 195 323), lower := (rows 37 98 133 152 274 40 64 128 256), losses := [] }

theorem u24046 : Upper (D 7) (R 7) [36,96,129,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24046 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24047 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 152 274 96 75 139 267), lower := (rows 37 98 133 152 274 96 64 128 256), losses := [] }

theorem u24047 : Upper (D 7) (R 7) [36,96,129,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24048 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 152 280 33 66 194 322), lower := (rows 37 98 133 152 280 33 64 128 256), losses := [] }

theorem u24048 : Upper (D 7) (R 7) [36,96,129,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24049 : Route 9 := (fun mask => (mask,id))

def c24049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24049 : Upper (D 7) (R 7) [36,96,129,144,264,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,144,264,2] 13 (by decide) (choices 1) [1,2] r24049 c24049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7857
  · exact u7858

def b24050 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 152 280 96 67 131 259), lower := (rows 37 98 133 152 280 96 64 128 256), losses := [] }

theorem u24050 : Upper (D 7) (R 7) [36,96,129,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24051 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 152 336 33 74 138 266), lower := (rows 37 98 133 152 336 33 64 128 256), losses := [] }

theorem u24051 : Upper (D 7) (R 7) [36,96,129,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24052 : Route 9 := (fun mask => (mask,id))

def c24052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24052 : Upper (D 7) (R 7) [36,96,129,144,320,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,144,320,2] 13 (by decide) (choices 1) [1,2,8] r24052 c24052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7859
  · exact u7860
  · exact u7861

def b24053 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 152 336 40 67 131 259), lower := (rows 37 98 133 152 336 40 64 128 256), losses := [] }

theorem u24053 : Upper (D 7) (R 7) [36,96,129,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24053 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24054 : Route 9 := (fun mask => (mask,id))

def c24054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24054 : Upper (D 7) (R 7) [36,96,129,192,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,192,257,2] 13 (by decide) (choices 1) [2,8,16] r24054 c24054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7862
  · exact u7863
  · exact u7864

def b24055 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 200 273 40 82 146 274), lower := (rows 37 98 133 200 273 40 64 128 256), losses := [] }

theorem u24055 : Upper (D 7) (R 7) [36,96,129,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24055 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24056 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 133 200 273 48 74 138 266), lower := (rows 37 98 133 200 273 48 64 128 256), losses := [] }

theorem u24056 : Upper (D 7) (R 7) [36,96,129,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24056 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24057 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 200 274 33 90 154 282), lower := (rows 37 98 133 200 274 33 64 128 256), losses := [] }

theorem u24057 : Upper (D 7) (R 7) [36,96,129,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24058 : Route 9 := (fun mask => (mask,id))

def c24058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24058 : Upper (D 7) (R 7) [36,96,129,192,258,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,192,258,2] 13 (by decide) (choices 1) [1,8,16] r24058 c24058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7865
  · exact u7866
  · exact u7867

def b24059 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 200 274 40 83 147 275), lower := (rows 37 98 133 200 274 40 64 128 256), losses := [] }

theorem u24059 : Upper (D 7) (R 7) [36,96,129,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24059 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24059
end Delivery.IrregularNine14.P07
