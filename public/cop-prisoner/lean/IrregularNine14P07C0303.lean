import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0081

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18180 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 392 146 96 116 180 308), lower := (rows 35 67 13 392 146 96 64 128 256), losses := [] }

theorem u18180 : Upper (D 7) (R 7) [34,65,9,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18181 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 392 148 34 112 240 368), lower := (rows 35 67 13 392 148 34 64 128 256), losses := [] }

theorem u18181 : Upper (D 7) (R 7) [34,65,9,384,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18182 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 99, targets := 128 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,7),(1,7),(3,0)], upper := (rows 35 67 13 392 148 48 98 226 354), lower := (rows 35 67 13 392 148 48 64 128 256), losses := [] }

theorem u18182 : Upper (D 7) (R 7) [34,65,9,384,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18182 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18183 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 392 148 96 114 178 306), lower := (rows 35 67 13 392 148 96 64 128 256), losses := [] }

theorem u18183 : Upper (D 7) (R 7) [34,65,9,384,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18184 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 392 176 34 84 212 340), lower := (rows 35 67 13 392 176 34 64 128 256), losses := [] }

theorem u18184 : Upper (D 7) (R 7) [34,65,9,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18185 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(3,0),(4,0)], upper := (rows 35 67 13 392 176 36 82 210 338), lower := (rows 35 67 13 392 176 36 64 128 256), losses := [] }

theorem u18185 : Upper (D 7) (R 7) [34,65,9,384,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18185 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18186 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 13 392 176 48 70 198 326), lower := (rows 35 67 13 392 176 48 64 128 256), losses := [] }

theorem u18186 : Upper (D 7) (R 7) [34,65,9,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18186 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18187 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 392 176 96 86 150 278), lower := (rows 35 67 13 392 176 96 64 128 256), losses := [] }

theorem u18187 : Upper (D 7) (R 7) [34,65,9,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18188 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 392 208 34 116 180 308), lower := (rows 35 67 13 392 208 34 64 128 256), losses := [] }

theorem u18188 : Upper (D 7) (R 7) [34,65,9,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18189 : Route 9 := (fun mask => (mask,id))

def c18189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18189 : Upper (D 7) (R 7) [34,65,9,384,192,4] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,192,4] 13 (by decide) (choices 1) [2,16,32] r18189 c18189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4864
  · exact u4865
  · exact u4866

def b18190 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 13 392 208 48 102 166 294), lower := (rows 35 67 13 392 208 48 64 128 256), losses := [] }

theorem u18190 : Upper (D 7) (R 7) [34,65,9,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18190 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18191 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 28 44 208 33 450 386 386), lower := (rows 35 67 28 44 208 33 64 128 256), losses := [] }

theorem u18191 : Upper (D 7) (R 7) [34,65,24,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18192 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 28 44 208 34 449 385 385), lower := (rows 35 67 28 44 208 34 64 128 256), losses := [] }

theorem u18192 : Upper (D 7) (R 7) [34,65,24,36,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18193 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 35 67 28 44 208 160 323 387 259), lower := (rows 35 67 28 44 208 160 64 128 256), losses := [] }

theorem u18193 : Upper (D 7) (R 7) [34,65,24,36,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18194 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 35 67 28 44 208 288 195 131 387), lower := (rows 35 67 28 44 208 288 64 128 256), losses := [] }

theorem u18194 : Upper (D 7) (R 7) [34,65,24,36,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18194 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18195 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 28 44 336 33 194 130 386), lower := (rows 35 67 28 44 336 33 64 128 256), losses := [] }

theorem u18195 : Upper (D 7) (R 7) [34,65,24,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18196 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 28 44 336 34 193 129 385), lower := (rows 35 67 28 44 336 34 64 128 256), losses := [] }

theorem u18196 : Upper (D 7) (R 7) [34,65,24,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18197 : Route 9 := (fun mask => (mask,id))

def c18197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18197 : Upper (D 7) (R 7) [34,65,24,36,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,320,128] 13 (by decide) (choices 1) [1,2,128] r18197 c18197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4867
  · exact u4868
  · exact u4869

def b18198 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 44 400 33 194 194 450), lower := (rows 35 67 28 44 400 33 64 128 256), losses := [] }

theorem u18198 : Upper (D 7) (R 7) [34,65,24,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18199 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 44 400 34 193 193 449), lower := (rows 35 67 28 44 400 34 64 128 256), losses := [] }

theorem u18199 : Upper (D 7) (R 7) [34,65,24,36,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18200 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 44 400 96 195 131 387), lower := (rows 35 67 28 44 400 96 64 128 256), losses := [] }

theorem u18200 : Upper (D 7) (R 7) [34,65,24,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18201 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 35 67 28 44 400 160 67 195 323), lower := (rows 35 67 28 44 400 160 64 128 256), losses := [] }

theorem u18201 : Upper (D 7) (R 7) [34,65,24,36,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18202 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 104 145 34 452 388 388), lower := (rows 35 67 28 104 145 34 64 128 256), losses := [] }

theorem u18202 : Upper (D 7) (R 7) [34,65,24,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18203 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 35 67 28 104 145 36 450 386 386), lower := (rows 35 67 28 104 145 36 64 128 256), losses := [] }

theorem u18203 : Upper (D 7) (R 7) [34,65,24,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18203 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18204 : Route 9 := (fun mask => (mask,id))

def c18204 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u18204 : Upper (D 7) (R 7) [34,65,24,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,129,128] 13 (by decide) (choices 1) [2,4,256] r18204 c18204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4870
  · exact u4871
  · exact u4872

def r18205 : Route 9 := (fun mask => (mask,id))

def c18205 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18205 : Upper (D 7) (R 7) [34,65,24,96,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,129,256] 13 (by decide) (choices 1) [2,4,128] r18205 c18205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4873
  · exact u4874
  · exact u4875

def b18206 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 104 273 34 196 132 388), lower := (rows 35 67 28 104 273 34 64 128 256), losses := [] }

theorem u18206 : Upper (D 7) (R 7) [34,65,24,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18207 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 35 67 28 104 273 36 194 130 386), lower := (rows 35 67 28 104 273 36 64 128 256), losses := [] }

theorem u18207 : Upper (D 7) (R 7) [34,65,24,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18207 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18208 : Route 9 := (fun mask => (mask,id))

def c18208 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18208 : Upper (D 7) (R 7) [34,65,24,96,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,257,128] 13 (by decide) (choices 1) [2,4,128] r18208 c18208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4876
  · exact u4877
  · exact u4878

def b18209 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 104 400 33 198 134 390), lower := (rows 35 67 28 104 400 33 64 128 256), losses := [] }

theorem u18209 : Upper (D 7) (R 7) [34,65,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18210 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 104 400 34 197 133 389), lower := (rows 35 67 28 104 400 34 64 128 256), losses := [] }

theorem u18210 : Upper (D 7) (R 7) [34,65,24,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18211 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 35 67 28 104 400 36 195 131 387), lower := (rows 35 67 28 104 400 36 64 128 256), losses := [] }

theorem u18211 : Upper (D 7) (R 7) [34,65,24,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18211 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m18212_1 : Upper (D 7) (R 7) [34,65,24,96,384,128,1] 13 :=
  permutation_upper _ _ _ [34,65,24,96,384,2,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4880

theorem m18212_2 : Upper (D 7) (R 7) [34,65,24,96,384,128,2] 13 :=
  permutation_upper _ _ _ [34,65,24,96,384,1,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4879

theorem m18212_4 : Upper (D 7) (R 7) [34,65,24,96,384,128,4] 13 :=
  permutation_upper _ _ _ [34,65,24,96,384,4,128] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4881

def r18212 : Route 9 := (fun mask => (mask,id))

def c18212 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18212 : Upper (D 7) (R 7) [34,65,24,96,384,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,384,128] 13 (by decide) (choices 1) [1,2,4] r18212 c18212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18212_1
  · exact m18212_2
  · exact m18212_4

def b18213 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 28 137 146 36 352 480 352), lower := (rows 35 67 28 137 146 36 64 128 256), losses := [] }

theorem u18213 : Upper (D 7) (R 7) [34,65,24,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18213 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18214 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 137 146 96 356 420 292), lower := (rows 35 67 28 137 146 96 64 128 256), losses := [] }

theorem u18214 : Upper (D 7) (R 7) [34,65,24,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m18215_4 : Upper (D 7) (R 7) [34,65,24,129,130,256,4] 13 :=
  permutation_upper _ _ _ [34,65,24,129,130,4,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4882

theorem m18215_32 : Upper (D 7) (R 7) [34,65,24,129,130,256,32] 13 :=
  permutation_upper _ _ _ [34,65,24,129,130,64,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4883

def r18215 : Route 9 := (fun mask => (mask,id))

def c18215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18215 : Upper (D 7) (R 7) [34,65,24,129,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,130,256] 13 (by decide) (choices 1) [4,32] r18215 c18215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m18215_4
  · exact m18215_32

def b18216 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 176 34 324 452 324), lower := (rows 35 67 28 137 176 34 64 128 256), losses := [] }

theorem u18216 : Upper (D 7) (R 7) [34,65,24,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18217 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 28 137 176 36 322 450 322), lower := (rows 35 67 28 137 176 36 64 128 256), losses := [] }

theorem u18217 : Upper (D 7) (R 7) [34,65,24,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18217 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18218 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 137 176 96 326 390 262), lower := (rows 35 67 28 137 176 96 64 128 256), losses := [] }

theorem u18218 : Upper (D 7) (R 7) [34,65,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18219 : Route 9 := (fun mask => (mask,id))

def c18219 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18219 : Upper (D 7) (R 7) [34,65,24,129,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,160,256] 13 (by decide) (choices 1) [2,4] r18219 c18219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4884
  · exact u4885

def b18220 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 208 34 356 420 292), lower := (rows 35 67 28 137 208 34 64 128 256), losses := [] }

theorem u18220 : Upper (D 7) (R 7) [34,65,24,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18221 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(4,0)], upper := (rows 35 67 28 137 208 36 354 418 290), lower := (rows 35 67 28 137 208 36 64 128 256), losses := [] }

theorem u18221 : Upper (D 7) (R 7) [34,65,24,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18221 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18222 : Route 9 := (fun mask => (mask,id))

def c18222 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18222 : Upper (D 7) (R 7) [34,65,24,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,192,256] 13 (by decide) (choices 1) [2,4,32] r18222 c18222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4886
  · exact u4887
  · exact u4888

def b18223 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 200, targets := 2 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 35 67 28 137 274 36 224 224 480), lower := (rows 35 67 28 137 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 44 109 173 301), good := (rows 498 466 508 508 274 484 64 128 256) }] }

theorem u18223 : Upper (D 7) (R 7) [34,65,24,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18223 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18224 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 137 274 96 228 164 420), lower := (rows 35 67 28 137 274 96 64 128 256), losses := [] }

theorem u18224 : Upper (D 7) (R 7) [34,65,24,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18225 : Route 9 := (fun mask => (mask,id))

def c18225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18225 : Upper (D 7) (R 7) [34,65,24,129,258,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,258,128] 13 (by decide) (choices 1) [4,32] r18225 c18225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4889
  · exact u4890

def b18226 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 276 34 224 224 480), lower := (rows 35 67 28 137 276 34 64 128 256), losses := [] }

theorem u18226 : Upper (D 7) (R 7) [34,65,24,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18227 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 137 276 96 226 162 418), lower := (rows 35 67 28 137 276 96 64 128 256), losses := [] }

theorem u18227 : Upper (D 7) (R 7) [34,65,24,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18228 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 67 28 137 276 160 98 226 354), lower := (rows 35 67 28 137 276 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 171 67 131 259), good := (rows 482 482 60 508 276 160 64 160 256) }] }

theorem u18228 : Upper (D 7) (R 7) [34,65,24,129,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18229 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 304 34 196 196 452), lower := (rows 35 67 28 137 304 34 64 128 256), losses := [] }

theorem u18229 : Upper (D 7) (R 7) [34,65,24,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18230 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 0, region := 464, targets := 1 }], pairs := [(1,5),(3,5),(4,0)], upper := (rows 35 67 28 137 304 36 194 194 450), lower := (rows 35 67 28 137 304 36 64 128 256), losses := [] }

theorem u18230 : Upper (D 7) (R 7) [34,65,24,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18230 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18231 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 137 304 96 198 134 390), lower := (rows 35 67 28 137 304 96 64 128 256), losses := [] }

theorem u18231 : Upper (D 7) (R 7) [34,65,24,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18232 : Route 9 := (fun mask => (mask,id))

def c18232 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18232 : Upper (D 7) (R 7) [34,65,24,129,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,288,128] 13 (by decide) (choices 1) [2,4] r18232 c18232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4891
  · exact u4892

def b18233 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 336 34 228 164 420), lower := (rows 35 67 28 137 336 34 64 128 256), losses := [] }

theorem u18233 : Upper (D 7) (R 7) [34,65,24,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18234 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 136, targets := 64 }], pairs := [(2,0),(3,6),(4,0)], upper := (rows 35 67 28 137 336 36 226 162 418), lower := (rows 35 67 28 137 336 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 44 65 129 257), good := (rows 498 466 60 508 336 36 64 128 256) }] }

theorem u18234 : Upper (D 7) (R 7) [34,65,24,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18234 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18235 : Route 9 := (fun mask => (mask,id))

def c18235 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18235 : Upper (D 7) (R 7) [34,65,24,129,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,320,128] 13 (by decide) (choices 1) [2,4,32] r18235 c18235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4893
  · exact u4894
  · exact u4895

def b18236 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 400 34 100 228 356), lower := (rows 35 67 28 137 400 34 64 128 256), losses := [] }

theorem u18236 : Upper (D 7) (R 7) [34,65,24,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18237 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(4,0)], upper := (rows 35 67 28 137 400 36 98 226 354), lower := (rows 35 67 28 137 400 36 64 128 256), losses := [] }

theorem u18237 : Upper (D 7) (R 7) [34,65,24,129,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18237 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18238 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 137 400 96 102 166 294), lower := (rows 35 67 28 137 400 96 64 128 256), losses := [] }

theorem u18238 : Upper (D 7) (R 7) [34,65,24,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18239 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 140 273 34 224 224 480), lower := (rows 35 67 28 140 273 34 64 128 256), losses := [] }

theorem u18239 : Upper (D 7) (R 7) [34,65,24,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18239
end Delivery.IrregularNine14.P07
