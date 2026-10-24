import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0080
import IrregularNine14P07C0081

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18120 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 268 176 160 82 210 338), lower := (rows 35 67 13 268 176 160 64 128 256), losses := [] }

theorem u18120 : Upper (D 7) (R 7) [34,65,9,260,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18121 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 268 208 34 240 176 432), lower := (rows 35 67 13 268 208 34 64 128 256), losses := [] }

theorem u18121 : Upper (D 7) (R 7) [34,65,9,260,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18122 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 13 268 208 48 226 162 418), lower := (rows 35 67 13 268 208 48 64 128 256), losses := [] }

theorem u18122 : Upper (D 7) (R 7) [34,65,9,260,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18122 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18123 : Route 9 := (fun mask => (mask,id))

def c18123 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18123 : Upper (D 7) (R 7) [34,65,9,260,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,192,128] 13 (by decide) (choices 1) [2,16,32] r18123 c18123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4821
  · exact u4822
  · exact u4823

def b18124 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 280 84 34 224 160 416), lower := (rows 35 67 13 280 84 34 64 128 256), losses := [] }

theorem u18124 : Upper (D 7) (R 7) [34,65,9,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18125 : Route 9 := (fun mask => (mask,id))

def c18125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18125 : Upper (D 7) (R 7) [34,65,9,272,68,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,68,128] 13 (by decide) (choices 1) [2,32,128] r18125 c18125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4824
  · exact u4825
  · exact u4826

def r18126 : Route 9 := (fun mask => (mask,id))

def c18126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18126 : Upper (D 7) (R 7) [34,65,9,272,130,4] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,130,4] 13 (by decide) (choices 1) [32,128] r18126 c18126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4827
  · exact u4828

def b18127 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 280 146 96 228 164 420), lower := (rows 35 67 13 280 146 96 64 128 256), losses := [] }

theorem u18127 : Upper (D 7) (R 7) [34,65,9,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18128 : Route 9 := (fun mask => (mask,id))

def c18128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18128 : Upper (D 7) (R 7) [34,65,9,272,130,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,130,128] 13 (by decide) (choices 1) [4,32] r18128 c18128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4829
  · exact u4830

def b18129 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 280 148 34 224 224 480), lower := (rows 35 67 13 280 148 34 64 128 256), losses := [] }

theorem u18129 : Upper (D 7) (R 7) [34,65,9,272,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18130 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 280 148 96 226 162 418), lower := (rows 35 67 13 280 148 96 64 128 256), losses := [] }

theorem u18130 : Upper (D 7) (R 7) [34,65,9,272,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18131 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 280 148 160 98 226 354), lower := (rows 35 67 13 280 148 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 183 67 131 259), good := (rows 482 482 508 312 188 160 64 160 256) }] }

theorem u18131 : Upper (D 7) (R 7) [34,65,9,272,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18132 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 280 176 34 196 196 452), lower := (rows 35 67 13 280 176 34 64 128 256), losses := [] }

theorem u18132 : Upper (D 7) (R 7) [34,65,9,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18133 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 280 176 36 194 194 450), lower := (rows 35 67 13 280 176 36 64 128 256), losses := [] }

theorem u18133 : Upper (D 7) (R 7) [34,65,9,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18133 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18134 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 280 176 96 198 134 390), lower := (rows 35 67 13 280 176 96 64 128 256), losses := [] }

theorem u18134 : Upper (D 7) (R 7) [34,65,9,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18135 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 280 176 160 70 198 326), lower := (rows 35 67 13 280 176 160 64 128 256), losses := [] }

theorem u18135 : Upper (D 7) (R 7) [34,65,9,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18136 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 280 208 34 228 164 420), lower := (rows 35 67 13 280 208 34 64 128 256), losses := [] }

theorem u18136 : Upper (D 7) (R 7) [34,65,9,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18137 : Route 9 := (fun mask => (mask,id))

def c18137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18137 : Upper (D 7) (R 7) [34,65,9,272,192,4] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,192,4] 13 (by decide) (choices 1) [2,32,128] r18137 c18137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4831
  · exact u4832
  · exact u4833

def r18138 : Route 9 := (fun mask => (mask,id))

def c18138 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18138 : Upper (D 7) (R 7) [34,65,9,272,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,192,128] 13 (by decide) (choices 1) [2,4,32] r18138 c18138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4834
  · exact u4835
  · exact u4836

def b18139 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 296 84 34 208 144 400), lower := (rows 35 67 13 296 84 34 64 128 256), losses := [] }

theorem u18139 : Upper (D 7) (R 7) [34,65,9,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18140 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6)], upper := (rows 35 67 13 296 84 48 194 130 386), lower := (rows 35 67 13 296 84 48 64 128 256), losses := [] }

theorem u18140 : Upper (D 7) (R 7) [34,65,9,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18140 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18141 : Route 9 := (fun mask => (mask,id))

def c18141 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18141 : Upper (D 7) (R 7) [34,65,9,288,68,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288,68,128] 13 (by decide) (choices 1) [2,16,128] r18141 c18141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4837
  · exact u4838
  · exact u4839

def b18142 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 296 146 36 208 208 464), lower := (rows 35 67 13 296 146 36 64 128 256), losses := [] }

theorem u18142 : Upper (D 7) (R 7) [34,65,9,288,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18142 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18143 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 67 13 296 146 48 196 196 452), lower := (rows 35 67 13 296 146 48 64 128 256), losses := [] }

theorem u18143 : Upper (D 7) (R 7) [34,65,9,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18143 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18144 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 296 146 96 212 148 404), lower := (rows 35 67 13 296 146 96 64 128 256), losses := [] }

theorem u18144 : Upper (D 7) (R 7) [34,65,9,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18145 : Route 9 := (fun mask => (mask,id))

def c18145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18145 : Upper (D 7) (R 7) [34,65,9,288,130,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288,130,128] 13 (by decide) (choices 1) [4,16] r18145 c18145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4840
  · exact u4841

def b18146 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 296 148 34 208 208 464), lower := (rows 35 67 13 296 148 34 64 128 256), losses := [] }

theorem u18146 : Upper (D 7) (R 7) [34,65,9,288,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18147 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 0, region := 456, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 67 13 296 148 48 194 194 450), lower := (rows 35 67 13 296 148 48 64 128 256), losses := [] }

theorem u18147 : Upper (D 7) (R 7) [34,65,9,288,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18147 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18148 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 296 148 96 210 146 402), lower := (rows 35 67 13 296 148 96 64 128 256), losses := [] }

theorem u18148 : Upper (D 7) (R 7) [34,65,9,288,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18149 : Route 9 := (fun mask => (mask,id))

def c18149 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18149 : Upper (D 7) (R 7) [34,65,9,288,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288,132,128] 13 (by decide) (choices 1) [2,16] r18149 c18149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4842
  · exact u4843

def b18150 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 296 208 34 212 148 404), lower := (rows 35 67 13 296 208 34 64 128 256), losses := [] }

theorem u18150 : Upper (D 7) (R 7) [34,65,9,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18151 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 296 208 36 210 146 402), lower := (rows 35 67 13 296 208 36 64 128 256), losses := [] }

theorem u18151 : Upper (D 7) (R 7) [34,65,9,288,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18151 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18152 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6)], upper := (rows 35 67 13 296 208 48 198 134 390), lower := (rows 35 67 13 296 208 48 64 128 256), losses := [] }

theorem u18152 : Upper (D 7) (R 7) [34,65,9,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18152 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18153 : Route 9 := (fun mask => (mask,id))

def c18153 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18153 : Upper (D 7) (R 7) [34,65,9,288,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288,192,128] 13 (by decide) (choices 1) [2,4,16] r18153 c18153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4844
  · exact u4845
  · exact u4846

def b18154 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 13 328 52 34 208 144 400), lower := (rows 35 67 13 328 52 34 64 128 256), losses := [] }

theorem u18154 : Upper (D 7) (R 7) [34,65,9,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18155 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 13 328 52 48 194 130 386), lower := (rows 35 67 13 328 52 48 64 128 256), losses := [] }

theorem u18155 : Upper (D 7) (R 7) [34,65,9,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18155 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18156 : Route 9 := (fun mask => (mask,id))

def c18156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18156 : Upper (D 7) (R 7) [34,65,9,320,36,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,320,36,128] 13 (by decide) (choices 1) [2,16,128] r18156 c18156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4847
  · exact u4848
  · exact u4849

def b18157 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 328 146 36 240 176 432), lower := (rows 35 67 13 328 146 36 64 128 256), losses := [] }

theorem u18157 : Upper (D 7) (R 7) [34,65,9,320,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18157 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18158 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 13 328 146 48 228 164 420), lower := (rows 35 67 13 328 146 48 64 128 256), losses := [] }

theorem u18158 : Upper (D 7) (R 7) [34,65,9,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18158 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18159 : Route 9 := (fun mask => (mask,id))

def c18159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18159 : Upper (D 7) (R 7) [34,65,9,320,130,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,320,130,128] 13 (by decide) (choices 1) [4,16,32] r18159 c18159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4850
  · exact u4851
  · exact u4852

def b18160 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 328 148 34 240 176 432), lower := (rows 35 67 13 328 148 34 64 128 256), losses := [] }

theorem u18160 : Upper (D 7) (R 7) [34,65,9,320,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18161 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0),(4,0),(4,6)], upper := (rows 35 67 13 328 148 48 226 162 418), lower := (rows 35 67 13 328 148 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 15 20 52 65 129 257), good := (rows 490 458 508 328 188 48 64 128 256) },{ target := 6, region := (rows 1 2 4 8 20 52 0 129 257), good := (rows 419 387 445 264 180 48 0 128 256) }] }

theorem u18161 : Upper (D 7) (R 7) [34,65,9,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18161 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18162 : Route 9 := (fun mask => (mask,id))

def c18162 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18162 : Upper (D 7) (R 7) [34,65,9,320,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,320,132,128] 13 (by decide) (choices 1) [2,16,32] r18162 c18162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4853
  · exact u4854
  · exact u4855

def b18163 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 328 176 34 212 148 404), lower := (rows 35 67 13 328 176 34 64 128 256), losses := [] }

theorem u18163 : Upper (D 7) (R 7) [34,65,9,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18164 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 328 176 36 210 146 402), lower := (rows 35 67 13 328 176 36 64 128 256), losses := [] }

theorem u18164 : Upper (D 7) (R 7) [34,65,9,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18164 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18165 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 13 328 176 48 198 134 390), lower := (rows 35 67 13 328 176 48 64 128 256), losses := [] }

theorem u18165 : Upper (D 7) (R 7) [34,65,9,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18165 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18166 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 328 176 160 86 150 278), lower := (rows 35 67 13 328 176 160 64 128 256), losses := [] }

theorem u18166 : Upper (D 7) (R 7) [34,65,9,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18167 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 392 52 34 208 208 464), lower := (rows 35 67 13 392 52 34 64 128 256), losses := [] }

theorem u18167 : Upper (D 7) (R 7) [34,65,9,384,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18168 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 13 392 52 48 194 194 450), lower := (rows 35 67 13 392 52 48 64 128 256), losses := [] }

theorem u18168 : Upper (D 7) (R 7) [34,65,9,384,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18168 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18169 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 392 52 96 210 146 402), lower := (rows 35 67 13 392 52 96 64 128 256), losses := [] }

theorem u18169 : Upper (D 7) (R 7) [34,65,9,384,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18170 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 67 13 392 52 160 82 210 338), lower := (rows 35 67 13 392 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 66 60 424 52 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 33 65 61 424 52 160 64 160 256) }] }

theorem u18170 : Upper (D 7) (R 7) [34,65,9,384,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18171 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 392 84 34 240 176 432), lower := (rows 35 67 13 392 84 34 64 128 256), losses := [] }

theorem u18171 : Upper (D 7) (R 7) [34,65,9,384,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18172 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 13 392 84 48 226 162 418), lower := (rows 35 67 13 392 84 48 64 128 256), losses := [] }

theorem u18172 : Upper (D 7) (R 7) [34,65,9,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18172 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18173 : Route 9 := (fun mask => (mask,id))

def c18173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18173 : Upper (D 7) (R 7) [34,65,9,384,68,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,68,128] 13 (by decide) (choices 1) [2,16,32] r18173 c18173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4856
  · exact u4857
  · exact u4858

def b18174 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 392 112 34 212 148 404), lower := (rows 35 67 13 392 112 34 64 128 256), losses := [] }

theorem u18174 : Upper (D 7) (R 7) [34,65,9,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18175 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7),(3,0),(4,0)], upper := (rows 35 67 13 392 112 36 210 146 402), lower := (rows 35 67 13 392 112 36 64 128 256), losses := [] }

theorem u18175 : Upper (D 7) (R 7) [34,65,9,384,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18175 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18176 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 13 392 112 48 198 134 390), lower := (rows 35 67 13 392 112 48 64 128 256), losses := [] }

theorem u18176 : Upper (D 7) (R 7) [34,65,9,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18176 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18177 : Route 9 := (fun mask => (mask,id))

def c18177 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18177 : Upper (D 7) (R 7) [34,65,9,384,96,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,96,128] 13 (by decide) (choices 1) [2,4,16] r18177 c18177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4859
  · exact u4860
  · exact u4861

def r18178 : Route 9 := (fun mask => (mask,id))

def c18178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18178 : Upper (D 7) (R 7) [34,65,9,384,130,4] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,130,4] 13 (by decide) (choices 1) [16,32] r18178 c18178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4862
  · exact u4863

def b18179 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 13 392 146 48 100 228 356), lower := (rows 35 67 13 392 146 48 64 128 256), losses := [] }

theorem u18179 : Upper (D 7) (R 7) [34,65,9,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18179 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18179
end Delivery.IrregularNine14.P07
