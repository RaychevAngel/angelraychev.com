import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0142

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27120 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 162 324 28 81 36 67 131 259), lower := (rows 41 162 324 28 81 36 64 128 256), losses := [] }

theorem u27120 : Upper (D 6) (R 6) [40,160,320,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27121 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 28 82 33 71 135 263), lower := (rows 41 162 324 28 82 33 64 128 256), losses := [] }

theorem u27121 : Upper (D 6) (R 6) [40,160,320,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27122 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 162 324 28 82 34 69 133 261), lower := (rows 41 162 324 28 82 34 64 128 256), losses := [] }

theorem u27122 : Upper (D 6) (R 6) [40,160,320,20,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27123 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 41 162 324 28 82 36 67 131 259), lower := (rows 41 162 324 28 82 36 64 128 256), losses := [] }

theorem u27123 : Upper (D 6) (R 6) [40,160,320,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27124 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 162 324 73 22 33 86 150 278), lower := (rows 41 162 324 73 22 33 64 128 256), losses := [] }

theorem u27124 : Upper (D 6) (R 6) [40,160,320,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27125 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 162 324 73 22 34 85 149 277), lower := (rows 41 162 324 73 22 34 64 128 256), losses := [] }

theorem u27125 : Upper (D 6) (R 6) [40,160,320,65,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27126 : Route 9 := (fun mask => (mask,id))

def c27126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27126 : Upper (D 6) (R 6) [40,160,320,65,6,4] 13 := by
  apply FastRouting.sound _ _ [40,160,320,65,6,4] 13 (by decide) (choices 1) [1,2,16] r27126 c27126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8532
  · exact u8533
  · exact u8534

def r27127 : Route 9 := (fun mask => (mask,id))

def c27127 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27127 : Upper (D 6) (R 6) [40,160,320,65,6,16] 13 := by
  apply FastRouting.sound _ _ [40,160,320,65,6,16] 13 (by decide) (choices 1) [1,2,4] r27127 c27127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8535
  · exact u8536
  · exact u8537

def b27128 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 74 21 33 86 150 278), lower := (rows 41 162 324 74 21 33 64 128 256), losses := [] }

theorem u27128 : Upper (D 6) (R 6) [40,160,320,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27129 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 162 324 74 21 34 85 149 277), lower := (rows 41 162 324 74 21 34 64 128 256), losses := [] }

theorem u27129 : Upper (D 6) (R 6) [40,160,320,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27130 : Route 9 := (fun mask => (mask,id))

def c27130 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27130 : Upper (D 6) (R 6) [40,160,320,66,5,4] 13 := by
  apply FastRouting.sound _ _ [40,160,320,66,5,4] 13 (by decide) (choices 1) [1,2,16] r27130 c27130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8538
  · exact u8539
  · exact u8540

def r27131 : Route 9 := (fun mask => (mask,id))

def c27131 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27131 : Upper (D 6) (R 6) [40,160,320,66,5,16] 13 := by
  apply FastRouting.sound _ _ [40,160,320,66,5,16] 13 (by decide) (choices 1) [1,2,4] r27131 c27131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8541
  · exact u8542
  · exact u8543

def b27132 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 74 22 33 85 149 277), lower := (rows 41 162 324 74 22 33 64 128 256), losses := [] }

theorem u27132 : Upper (D 6) (R 6) [40,160,320,66,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27133 : Route 9 := (fun mask => (mask,id))

def c27133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27133 : Upper (D 6) (R 6) [40,160,320,66,6,4] 13 := by
  apply FastRouting.sound _ _ [40,160,320,66,6,4] 13 (by decide) (choices 1) [1,16] r27133 c27133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8544
  · exact u8545

def b27134 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 41 162 324 74 22 48 69 133 261), lower := (rows 41 162 324 74 22 48 64 128 256), losses := [] }

theorem u27134 : Upper (D 6) (R 6) [40,160,320,66,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27134 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27135 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 162 324 88 19 33 70 134 262), lower := (rows 41 162 324 88 19 33 64 128 256), losses := [] }

theorem u27135 : Upper (D 6) (R 6) [40,160,320,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27136 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 162 324 88 19 34 69 133 261), lower := (rows 41 162 324 88 19 34 64 128 256), losses := [] }

theorem u27136 : Upper (D 6) (R 6) [40,160,320,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27137 : Route 9 := (fun mask => (mask,id))

def c27137 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27137 : Upper (D 6) (R 6) [40,160,320,80,3,4] 13 := by
  apply FastRouting.sound _ _ [40,160,320,80,3,4] 13 (by decide) (choices 1) [1,2,4] r27137 c27137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8546
  · exact u8547
  · exact u8548

def b27138 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 162 324 88 21 33 70 134 262), lower := (rows 41 162 324 88 21 33 64 128 256), losses := [] }

theorem u27138 : Upper (D 6) (R 6) [40,160,320,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27139 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 162 324 88 21 34 71 135 263), lower := (rows 41 162 324 88 21 34 64 128 256), losses := [] }

theorem u27139 : Upper (D 6) (R 6) [40,160,320,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27140 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 162 324 88 21 36 67 131 259), lower := (rows 41 162 324 88 21 36 64 128 256), losses := [] }

theorem u27140 : Upper (D 6) (R 6) [40,160,320,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27141 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 88 22 33 71 135 263), lower := (rows 41 162 324 88 22 33 64 128 256), losses := [] }

theorem u27141 : Upper (D 6) (R 6) [40,160,320,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27142 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 162 324 88 22 34 69 133 261), lower := (rows 41 162 324 88 22 34 64 128 256), losses := [] }

theorem u27142 : Upper (D 6) (R 6) [40,160,320,80,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27143 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 4 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,1),(1,2),(1,6)], upper := (rows 41 162 324 88 22 36 67 131 259), lower := (rows 41 162 324 88 22 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 160 356 121 52 36 64 128 256) }] }

theorem u27143 : Upper (D 6) (R 6) [40,160,320,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27144 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 194 324 11 21 34 116 180 308), lower := (rows 41 194 324 11 21 34 64 128 256), losses := [] }

theorem u27144 : Upper (D 6) (R 6) [40,192,320,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27145 : Route 9 := (fun mask => (mask,id))

def c27145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27145 : Upper (D 6) (R 6) [40,192,320,3,5,4] 13 := by
  apply FastRouting.sound _ _ [40,192,320,3,5,4] 13 (by decide) (choices 1) [2,16,32] r27145 c27145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8549
  · exact u8550
  · exact u8551

def b27146 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 194 324 11 21 48 102 166 294), lower := (rows 41 194 324 11 21 48 64 128 256), losses := [] }

theorem u27146 : Upper (D 6) (R 6) [40,192,320,3,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27146 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27147 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 194 324 11 22 33 116 180 308), lower := (rows 41 194 324 11 22 33 64 128 256), losses := [] }

theorem u27147 : Upper (D 6) (R 6) [40,192,320,3,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27148 : Route 9 := (fun mask => (mask,id))

def c27148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27148 : Upper (D 6) (R 6) [40,192,320,3,6,4] 13 := by
  apply FastRouting.sound _ _ [40,192,320,3,6,4] 13 (by decide) (choices 1) [1,16,32] r27148 c27148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8552
  · exact u8553
  · exact u8554

def b27149 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 194 324 11 22 48 101 165 293), lower := (rows 41 194 324 11 22 48 64 128 256), losses := [] }

theorem u27149 : Upper (D 6) (R 6) [40,192,320,3,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27149 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27150 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 194 324 11 52 33 86 150 278), lower := (rows 41 194 324 11 52 33 64 128 256), losses := [] }

theorem u27150 : Upper (D 6) (R 6) [40,192,320,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27151 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 194 324 11 52 34 85 149 277), lower := (rows 41 194 324 11 52 34 64 128 256), losses := [] }

theorem u27151 : Upper (D 6) (R 6) [40,192,320,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27152 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 194 324 11 52 36 83 147 275), lower := (rows 41 194 324 11 52 36 64 128 256), losses := [] }

theorem u27152 : Upper (D 6) (R 6) [40,192,320,3,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27153 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 194 324 11 52 48 71 135 263), lower := (rows 41 194 324 11 52 48 64 128 256), losses := [] }

theorem u27153 : Upper (D 6) (R 6) [40,192,320,3,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27153 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27154 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 49, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 194 324 14 50 33 85 149 277), lower := (rows 41 194 324 14 50 33 64 128 256), losses := [] }

theorem u27154 : Upper (D 6) (R 6) [40,192,320,6,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27155 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 41 194 324 14 50 36 81 145 273), lower := (rows 41 194 324 14 50 36 64 128 256), losses := [] }

theorem u27155 : Upper (D 6) (R 6) [40,192,320,6,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27156 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 194 324 14 50 48 69 133 261), lower := (rows 41 194 324 14 50 48 64 128 256), losses := [] }

theorem u27156 : Upper (D 6) (R 6) [40,192,320,6,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27156 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27157 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 194 324 25 22 33 102 166 294), lower := (rows 41 194 324 25 22 33 64 128 256), losses := [] }

theorem u27157 : Upper (D 6) (R 6) [40,192,320,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27158 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 194 324 25 22 34 101 165 293), lower := (rows 41 194 324 25 22 34 64 128 256), losses := [] }

theorem u27158 : Upper (D 6) (R 6) [40,192,320,17,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27159 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 194 324 26 21 33 102 166 294), lower := (rows 41 194 324 26 21 33 64 128 256), losses := [] }

theorem u27159 : Upper (D 6) (R 6) [40,192,320,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27160 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 194 324 26 21 34 101 165 293), lower := (rows 41 194 324 26 21 34 64 128 256), losses := [] }

theorem u27160 : Upper (D 6) (R 6) [40,192,320,18,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27161 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 194, targets := 4 }], pairs := [(0,1),(1,2),(3,2)], upper := (rows 41 194 324 26 21 36 99 163 291), lower := (rows 41 194 324 26 21 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 192 356 57 53 36 64 128 256) },{ target := 2, region := (rows 1 19 0 24 16 32 65 129 257), good := (rows 491 194 320 26 475 32 64 128 256) }] }

theorem u27161 : Upper (D 6) (R 6) [40,192,320,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27162 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 194 324 26 52 33 71 135 263), lower := (rows 41 194 324 26 52 33 64 128 256), losses := [] }

theorem u27162 : Upper (D 6) (R 6) [40,192,320,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27163 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 41 194 324 26 52 34 69 133 261), lower := (rows 41 194 324 26 52 34 64 128 256), losses := [] }

theorem u27163 : Upper (D 6) (R 6) [40,192,320,18,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27164 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 194 324 26 52 36 67 131 259), lower := (rows 41 194 324 26 52 36 64 128 256), losses := [] }

theorem u27164 : Upper (D 6) (R 6) [40,192,320,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27165 : Route 9 := (fun mask => (mask,id))

def c27165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27165 : Upper (D 6) (R 6) [96,129,257,6,34,4] 13 := by
  apply FastRouting.sound _ _ [96,129,257,6,34,4] 13 (by decide) (choices 1) [8,16] r27165 c27165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8555
  · exact u8556

def b27166 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 48, targets := 68 }], pairs := [(4,2),(4,6)], upper := (rows 97 131 261 14 50 40 84 212 340), lower := (rows 97 131 261 14 50 40 64 128 256), losses := [] }

theorem u27166 : Upper (D 6) (R 6) [96,129,257,6,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27166 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27167 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 261 14 50 48 76 204 332), lower := (rows 97 131 261 14 50 48 64 128 256), losses := [] }

theorem u27167 : Upper (D 6) (R 6) [96,129,257,6,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27167 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27168 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 261 14 50 96 92 156 284), lower := (rows 97 131 261 14 50 96 64 128 256), losses := [] }

theorem u27168 : Upper (D 6) (R 6) [96,129,257,6,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27169 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 48, targets := 68 },{ cop := 4, region := 325, targets := 2 }], pairs := [(0,1),(4,2),(4,6)], upper := (rows 97 131 261 14 56 34 84 212 340), lower := (rows 97 131 261 14 56 34 64 128 256), losses := [] }

theorem u27169 : Upper (D 6) (R 6) [96,129,257,6,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27170 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 261 14 56 48 70 198 326), lower := (rows 97 131 261 14 56 48 64 128 256), losses := [] }

theorem u27170 : Upper (D 6) (R 6) [96,129,257,6,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27170 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27171 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 261 14 56 96 86 150 278), lower := (rows 97 131 261 14 56 96 64 128 256), losses := [] }

theorem u27171 : Upper (D 6) (R 6) [96,129,257,6,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27172 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 325, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 131 261 26 28 34 100 228 356), lower := (rows 97 131 261 26 28 34 64 128 256), losses := [{ target := 1, region := (rows 33 0 39 8 24 32 97 161 289), good := (rows 485 453 453 28 28 485 64 128 256) }] }

theorem u27172 : Upper (D 6) (R 6) [96,129,257,18,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27173 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 261 26 28 96 102 166 294), lower := (rows 97 131 261 26 28 96 64 128 256), losses := [] }

theorem u27173 : Upper (D 6) (R 6) [96,129,257,18,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27174 : Route 9 := (fun mask => (mask,id))

def c27174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27174 : Upper (D 6) (R 6) [96,129,257,18,36,2] 13 := by
  apply FastRouting.sound _ _ [96,129,257,18,36,2] 13 (by decide) (choices 1) [4,8] r27174 c27174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8557
  · exact u8558

def b27175 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 97 131 261 26 52 36 74 202 330), lower := (rows 97 131 261 26 52 36 64 128 256), losses := [] }

theorem u27175 : Upper (D 6) (R 6) [96,129,257,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27176 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 261 26 52 40 70 198 326), lower := (rows 97 131 261 26 52 40 64 128 256), losses := [] }

theorem u27176 : Upper (D 6) (R 6) [96,129,257,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27176 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27177 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 261 26 52 96 78 142 270), lower := (rows 97 131 261 26 52 96 64 128 256), losses := [] }

theorem u27177 : Upper (D 6) (R 6) [96,129,257,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27178 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 56, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 131 261 26 56 34 68 196 324), lower := (rows 97 131 261 26 56 34 64 128 256), losses := [] }

theorem u27178 : Upper (D 6) (R 6) [96,129,257,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27179 : Route 9 := (fun mask => (mask,id))

def c27179 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27179 : Upper (D 6) (R 6) [96,129,257,18,40,4] 13 := by
  apply FastRouting.sound _ _ [96,129,257,18,40,4] 13 (by decide) (choices 1) [2,4] r27179 c27179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8559
  · exact u8560

#print axioms u27179
end Delivery.IrregularNine14.P06
