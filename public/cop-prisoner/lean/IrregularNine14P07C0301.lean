import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0079
import IrregularNine14P07C0080

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18060 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 168 276 34 208 208 464), lower := (rows 35 67 13 168 276 34 64 128 256), losses := [] }

theorem u18060 : Upper (D 7) (R 7) [34,65,9,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18061 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 67 13 168 276 48 194 194 450), lower := (rows 35 67 13 168 276 48 64 128 256), losses := [] }

theorem u18061 : Upper (D 7) (R 7) [34,65,9,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18061 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18062 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 168 276 96 210 146 402), lower := (rows 35 67 13 168 276 96 64 128 256), losses := [] }

theorem u18062 : Upper (D 7) (R 7) [34,65,9,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18063 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 13 168 276 160 82 210 338), lower := (rows 35 67 13 168 276 160 64 128 256), losses := [] }

theorem u18063 : Upper (D 7) (R 7) [34,65,9,160,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18064 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 168 336 34 212 148 404), lower := (rows 35 67 13 168 336 34 64 128 256), losses := [] }

theorem u18064 : Upper (D 7) (R 7) [34,65,9,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18065 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 168 336 36 210 146 402), lower := (rows 35 67 13 168 336 36 64 128 256), losses := [] }

theorem u18065 : Upper (D 7) (R 7) [34,65,9,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18065 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18066 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6)], upper := (rows 35 67 13 168 336 48 198 134 390), lower := (rows 35 67 13 168 336 48 64 128 256), losses := [] }

theorem u18066 : Upper (D 7) (R 7) [34,65,9,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18066 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18067 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 13 168 336 160 86 150 278), lower := (rows 35 67 13 168 336 160 64 128 256), losses := [] }

theorem u18067 : Upper (D 7) (R 7) [34,65,9,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18068 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 168 400 34 84 212 340), lower := (rows 35 67 13 168 400 34 64 128 256), losses := [] }

theorem u18068 : Upper (D 7) (R 7) [34,65,9,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18069 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 168 400 36 82 210 338), lower := (rows 35 67 13 168 400 36 64 128 256), losses := [] }

theorem u18069 : Upper (D 7) (R 7) [34,65,9,160,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18069 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18070 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 168 400 48 70 198 326), lower := (rows 35 67 13 168 400 48 64 128 256), losses := [] }

theorem u18070 : Upper (D 7) (R 7) [34,65,9,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18070 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18071 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 168 400 96 86 150 278), lower := (rows 35 67 13 168 400 96 64 128 256), losses := [] }

theorem u18071 : Upper (D 7) (R 7) [34,65,9,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18072 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 13 200 52 34 464 400 400), lower := (rows 35 67 13 200 52 34 64 128 256), losses := [] }

theorem u18072 : Upper (D 7) (R 7) [34,65,9,192,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18073 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 13 200 52 48 450 386 386), lower := (rows 35 67 13 200 52 48 64 128 256), losses := [] }

theorem u18073 : Upper (D 7) (R 7) [34,65,9,192,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18073 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18074 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 67 13 200 52 160 338 402 274), lower := (rows 35 67 13 200 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 66 60 232 52 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 33 65 61 232 52 160 64 160 256) }] }

theorem u18074 : Upper (D 7) (R 7) [34,65,9,192,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18075 : Route 9 := (fun mask => (mask,id))

def c18075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18075 : Upper (D 7) (R 7) [34,65,9,192,36,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,36,256] 13 (by decide) (choices 1) [2,16,128] r18075 c18075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4785
  · exact u4786
  · exact u4787

def b18076 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 200 146 36 368 432 304), lower := (rows 35 67 13 200 146 36 64 128 256), losses := [] }

theorem u18076 : Upper (D 7) (R 7) [34,65,9,192,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18076 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18077 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 13 200 146 48 356 420 292), lower := (rows 35 67 13 200 146 48 64 128 256), losses := [] }

theorem u18077 : Upper (D 7) (R 7) [34,65,9,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18077 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18078 : Route 9 := (fun mask => (mask,id))

def c18078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18078 : Upper (D 7) (R 7) [34,65,9,192,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,130,256] 13 (by decide) (choices 1) [4,16,32] r18078 c18078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4788
  · exact u4789
  · exact u4790

def b18079 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 148 34 368 432 304), lower := (rows 35 67 13 200 148 34 64 128 256), losses := [] }

theorem u18079 : Upper (D 7) (R 7) [34,65,9,192,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18080 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,7),(1,7),(3,0)], upper := (rows 35 67 13 200 148 48 354 418 290), lower := (rows 35 67 13 200 148 48 64 128 256), losses := [] }

theorem u18080 : Upper (D 7) (R 7) [34,65,9,192,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18080 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18081 : Route 9 := (fun mask => (mask,id))

def c18081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18081 : Upper (D 7) (R 7) [34,65,9,192,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,132,256] 13 (by decide) (choices 1) [2,16,32] r18081 c18081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4791
  · exact u4792
  · exact u4793

def b18082 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 176 34 340 404 276), lower := (rows 35 67 13 200 176 34 64 128 256), losses := [] }

theorem u18082 : Upper (D 7) (R 7) [34,65,9,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18083 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 200 176 36 338 402 274), lower := (rows 35 67 13 200 176 36 64 128 256), losses := [] }

theorem u18083 : Upper (D 7) (R 7) [34,65,9,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18083 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18084 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 13 200 176 48 326 390 262), lower := (rows 35 67 13 200 176 48 64 128 256), losses := [] }

theorem u18084 : Upper (D 7) (R 7) [34,65,9,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18084 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18085 : Route 9 := (fun mask => (mask,id))

def c18085 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18085 : Upper (D 7) (R 7) [34,65,9,192,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,160,256] 13 (by decide) (choices 1) [2,4,16] r18085 c18085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4794
  · exact u4795
  · exact u4796

def b18086 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 200 274 36 240 176 432), lower := (rows 35 67 13 200 274 36 64 128 256), losses := [] }

theorem u18086 : Upper (D 7) (R 7) [34,65,9,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18086 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18087 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 13 200 274 48 228 164 420), lower := (rows 35 67 13 200 274 48 64 128 256), losses := [] }

theorem u18087 : Upper (D 7) (R 7) [34,65,9,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18087 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18088 : Route 9 := (fun mask => (mask,id))

def c18088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18088 : Upper (D 7) (R 7) [34,65,9,192,258,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,258,128] 13 (by decide) (choices 1) [4,16,32] r18088 c18088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4797
  · exact u4798
  · exact u4799

def b18089 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 276 34 240 176 432), lower := (rows 35 67 13 200 276 34 64 128 256), losses := [] }

theorem u18089 : Upper (D 7) (R 7) [34,65,9,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18090 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0),(4,0),(4,6)], upper := (rows 35 67 13 200 276 48 226 162 418), lower := (rows 35 67 13 200 276 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 15 20 52 65 129 257), good := (rows 490 458 508 200 316 48 64 128 256) },{ target := 6, region := (rows 1 2 4 8 20 52 0 129 257), good := (rows 419 387 445 136 308 48 0 128 256) }] }

theorem u18090 : Upper (D 7) (R 7) [34,65,9,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18090 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18091 : Route 9 := (fun mask => (mask,id))

def c18091 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18091 : Upper (D 7) (R 7) [34,65,9,192,260,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,260,128] 13 (by decide) (choices 1) [2,16,32] r18091 c18091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4800
  · exact u4801
  · exact u4802

def b18092 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 304 34 212 148 404), lower := (rows 35 67 13 200 304 34 64 128 256), losses := [] }

theorem u18092 : Upper (D 7) (R 7) [34,65,9,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18093 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 200 304 36 210 146 402), lower := (rows 35 67 13 200 304 36 64 128 256), losses := [] }

theorem u18093 : Upper (D 7) (R 7) [34,65,9,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18093 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18094 : PairBound 9 := { available := 134, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 13 200 304 48 198 134 390), lower := (rows 35 67 13 200 304 48 64 128 256), losses := [] }

theorem u18094 : Upper (D 7) (R 7) [34,65,9,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18094 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18095 : Route 9 := (fun mask => (mask,id))

def c18095 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18095 : Upper (D 7) (R 7) [34,65,9,192,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,288,128] 13 (by decide) (choices 1) [2,4,16] r18095 c18095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4803
  · exact u4804
  · exact u4805

def b18096 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 400 34 116 180 308), lower := (rows 35 67 13 200 400 34 64 128 256), losses := [] }

theorem u18096 : Upper (D 7) (R 7) [34,65,9,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18097 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 200 400 36 114 178 306), lower := (rows 35 67 13 200 400 36 64 128 256), losses := [] }

theorem u18097 : Upper (D 7) (R 7) [34,65,9,192,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18097 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18098 : Route 9 := (fun mask => (mask,id))

def c18098 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18098 : Upper (D 7) (R 7) [34,65,9,192,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,384,16] 13 (by decide) (choices 1) [2,4,32] r18098 c18098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4806
  · exact u4807
  · exact u4808

def b18099 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 266 52 48 192 192 448), lower := (rows 35 67 13 266 52 48 64 128 256), losses := [] }

theorem u18099 : Upper (D 7) (R 7) [34,65,9,258,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18099 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18100 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 266 52 96 208 144 400), lower := (rows 35 67 13 266 52 96 64 128 256), losses := [] }

theorem u18100 : Upper (D 7) (R 7) [34,65,9,258,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18101 : Route 9 := (fun mask => (mask,id))

def c18101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18101 : Upper (D 7) (R 7) [34,65,9,258,36,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,36,128] 13 (by decide) (choices 1) [16,128] r18101 c18101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4809
  · exact u4810

def b18102 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,6),(3,6),(4,0)], upper := (rows 35 67 13 266 84 48 224 160 416), lower := (rows 35 67 13 266 84 48 64 128 256), losses := [] }

theorem u18102 : Upper (D 7) (R 7) [34,65,9,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18102 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18103 : Route 9 := (fun mask => (mask,id))

def c18103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u18103 : Upper (D 7) (R 7) [34,65,9,258,68,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,68,128] 13 (by decide) (choices 1) [16,32,128] r18103 c18103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4811
  · exact u4812
  · exact u4813

def b18104 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 35 67 13 266 148 48 224 224 480), lower := (rows 35 67 13 266 148 48 64 128 256), losses := [] }

theorem u18104 : Upper (D 7) (R 7) [34,65,9,258,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18104 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18105 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 266 148 96 240 176 432), lower := (rows 35 67 13 266 148 96 64 128 256), losses := [] }

theorem u18105 : Upper (D 7) (R 7) [34,65,9,258,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18106 : Route 9 := (fun mask => (mask,id))

def c18106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18106 : Upper (D 7) (R 7) [34,65,9,258,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,132,128] 13 (by decide) (choices 1) [16,32] r18106 c18106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4814
  · exact u4815

def b18107 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 266 176 36 208 208 464), lower := (rows 35 67 13 266 176 36 64 128 256), losses := [] }

theorem u18107 : Upper (D 7) (R 7) [34,65,9,258,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18107 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18108 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 13 266 176 48 196 196 452), lower := (rows 35 67 13 266 176 48 64 128 256), losses := [] }

theorem u18108 : Upper (D 7) (R 7) [34,65,9,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18108 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18109 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 266 176 96 212 148 404), lower := (rows 35 67 13 266 176 96 64 128 256), losses := [] }

theorem u18109 : Upper (D 7) (R 7) [34,65,9,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18110 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 266 176 160 84 212 340), lower := (rows 35 67 13 266 176 160 64 128 256), losses := [] }

theorem u18110 : Upper (D 7) (R 7) [34,65,9,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18111 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 266 208 36 240 176 432), lower := (rows 35 67 13 266 208 36 64 128 256), losses := [] }

theorem u18111 : Upper (D 7) (R 7) [34,65,9,258,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18111 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18112 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,6),(3,6),(4,0)], upper := (rows 35 67 13 266 208 48 228 164 420), lower := (rows 35 67 13 266 208 48 64 128 256), losses := [] }

theorem u18112 : Upper (D 7) (R 7) [34,65,9,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18112 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18113 : Route 9 := (fun mask => (mask,id))

def c18113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18113 : Upper (D 7) (R 7) [34,65,9,258,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,258,192,128] 13 (by decide) (choices 1) [4,16,32] r18113 c18113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4816
  · exact u4817
  · exact u4818

def b18114 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 13 268 146 48 224 224 480), lower := (rows 35 67 13 268 146 48 64 128 256), losses := [] }

theorem u18114 : Upper (D 7) (R 7) [34,65,9,260,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18114 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18115 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 268 146 96 240 176 432), lower := (rows 35 67 13 268 146 96 64 128 256), losses := [] }

theorem u18115 : Upper (D 7) (R 7) [34,65,9,260,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18116 : Route 9 := (fun mask => (mask,id))

def c18116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18116 : Upper (D 7) (R 7) [34,65,9,260,130,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,130,128] 13 (by decide) (choices 1) [16,32] r18116 c18116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4819
  · exact u4820

def b18117 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 268 176 34 208 208 464), lower := (rows 35 67 13 268 176 34 64 128 256), losses := [] }

theorem u18117 : Upper (D 7) (R 7) [34,65,9,260,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18118 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 13 268 176 48 194 194 450), lower := (rows 35 67 13 268 176 48 64 128 256), losses := [] }

theorem u18118 : Upper (D 7) (R 7) [34,65,9,260,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18118 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18119 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 268 176 96 210 146 402), lower := (rows 35 67 13 268 176 96 64 128 256), losses := [] }

theorem u18119 : Upper (D 7) (R 7) [34,65,9,260,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18119
end Delivery.IrregularNine14.P07
