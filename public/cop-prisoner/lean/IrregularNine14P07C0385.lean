import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0120
import IrregularNine14P07C0121

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23100 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 2 },{ cop := 0, region := 392, targets := 64 }], pairs := [(0,6),(0,7),(3,1),(3,6)], upper := (rows 37 74 84 265 146 34 225 161 417), lower := (rows 37 74 84 265 146 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 13 16 50 0 133 261), good := (rows 429 42 445 393 178 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 50 64 0 256), good := (rows 37 106 117 265 50 34 64 0 256) }] }

theorem u23100 : Upper (D 7) (R 7) [36,72,80,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23101 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 74 84 265 146 160 99 163 291), lower := (rows 37 74 84 265 146 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 72 117 265 176 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 10 53 265 178 160 0 160 256) }] }

theorem u23101 : Upper (D 7) (R 7) [36,72,80,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23102 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 84 265 176 33 194 130 386), lower := (rows 37 74 84 265 176 33 64 128 256), losses := [] }

theorem u23102 : Upper (D 7) (R 7) [36,72,80,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23103 : Route 9 := (fun mask => (mask,id))

def c23103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23103 : Upper (D 7) (R 7) [36,72,80,257,160,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,257,160,2] 13 (by decide) (choices 1) [1,2,128] r23103 c23103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7254
  · exact u7255
  · exact u7256

def b23104 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 84 265 176 160 67 131 259), lower := (rows 37 74 84 265 176 160 64 128 256), losses := [] }

theorem u23104 : Upper (D 7) (R 7) [36,72,80,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23105 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 84 266 145 33 226 162 418), lower := (rows 37 74 84 266 145 33 64 128 256), losses := [] }

theorem u23105 : Upper (D 7) (R 7) [36,72,80,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23106 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,1),(2,1),(4,1),(4,6)], upper := (rows 37 74 84 266 145 34 225 161 417), lower := (rows 37 74 84 266 145 34 64 128 256), losses := [] }

theorem u23106 : Upper (D 7) (R 7) [36,72,80,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23107 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 74 84 266 145 160 99 163 291), lower := (rows 37 74 84 266 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 72 117 264 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 10 53 266 177 160 0 160 256) }] }

theorem u23107 : Upper (D 7) (R 7) [36,72,80,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23108 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 101, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 84 266 146 33 225 161 417), lower := (rows 37 74 84 266 146 33 64 128 256), losses := [] }

theorem u23108 : Upper (D 7) (R 7) [36,72,80,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23109 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(3,7)], upper := (rows 37 74 84 266 146 160 97 161 289), lower := (rows 37 74 84 266 146 160 64 128 256), losses := [] }

theorem u23109 : Upper (D 7) (R 7) [36,72,80,258,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23110 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 84 266 176 33 195 131 387), lower := (rows 37 74 84 266 176 33 64 128 256), losses := [] }

theorem u23110 : Upper (D 7) (R 7) [36,72,80,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23111 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 74 84 266 176 34 193 129 385), lower := (rows 37 74 84 266 176 34 64 128 256), losses := [] }

theorem u23111 : Upper (D 7) (R 7) [36,72,80,258,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23112 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 84 266 176 160 67 131 259), lower := (rows 37 74 84 266 176 160 64 128 256), losses := [] }

theorem u23112 : Upper (D 7) (R 7) [36,72,80,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23113 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 84 296 19 33 194 130 386), lower := (rows 37 74 84 296 19 33 64 128 256), losses := [] }

theorem u23113 : Upper (D 7) (R 7) [36,72,80,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23114 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 196, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,7)], upper := (rows 37 74 84 296 19 34 193 129 385), lower := (rows 37 74 84 296 19 34 64 128 256), losses := [] }

theorem u23114 : Upper (D 7) (R 7) [36,72,80,288,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23115 : Route 9 := (fun mask => (mask,id))

def c23115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23115 : Upper (D 7) (R 7) [36,72,80,288,3,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,288,3,128] 13 (by decide) (choices 1) [1,2,128] r23115 c23115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7257
  · exact u7258
  · exact u7259

def b23116 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 84 296 145 33 194 130 386), lower := (rows 37 74 84 296 145 33 64 128 256), losses := [] }

theorem u23116 : Upper (D 7) (R 7) [36,72,80,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23117 : Route 9 := (fun mask => (mask,id))

def c23117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23117 : Upper (D 7) (R 7) [36,72,80,288,129,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,288,129,2] 13 (by decide) (choices 1) [1,2,128] r23117 c23117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7260
  · exact u7261
  · exact u7262

def b23118 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 74 84 296 145 160 67 131 259), lower := (rows 37 74 84 296 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 72 117 296 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 10 53 296 177 160 0 160 256) }] }

theorem u23118 : Upper (D 7) (R 7) [36,72,80,288,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23119 : Route 9 := (fun mask => (mask,id))

def c23119 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23119 : Upper (D 7) (R 7) [36,72,80,288,130,1] 13 := by
  apply FastRouting.sound _ _ [36,72,80,288,130,1] 13 (by decide) (choices 1) [1,2,128] r23119 c23119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7263
  · exact u7264
  · exact u7265

def b23120 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 2 },{ cop := 0, region := 392, targets := 64 }], pairs := [(0,6),(0,7),(3,1),(3,6)], upper := (rows 37 74 84 296 146 34 193 129 385), lower := (rows 37 74 84 296 146 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 13 16 50 0 133 261), good := (rows 429 42 445 296 178 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 50 64 0 256), good := (rows 37 106 117 296 50 34 64 0 256) }] }

theorem u23120 : Upper (D 7) (R 7) [36,72,80,288,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23121 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 74 84 296 146 160 67 131 259), lower := (rows 37 74 84 296 146 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 72 117 296 176 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 10 53 296 178 160 0 160 256) }] }

theorem u23121 : Upper (D 7) (R 7) [36,72,80,288,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23122 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 84 392 19 33 226 162 418), lower := (rows 37 74 84 392 19 33 64 128 256), losses := [] }

theorem u23122 : Upper (D 7) (R 7) [36,72,80,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23123 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 392, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(4,7)], upper := (rows 37 74 84 392 19 34 225 161 417), lower := (rows 37 74 84 392 19 34 64 128 256), losses := [] }

theorem u23123 : Upper (D 7) (R 7) [36,72,80,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23124 : Route 9 := (fun mask => (mask,id))

def c23124 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23124 : Upper (D 7) (R 7) [36,72,80,384,3,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384,3,128] 13 (by decide) (choices 1) [1,2,32] r23124 c23124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7266
  · exact u7267
  · exact u7268

def b23125 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 74 84 392 50 33 195 131 387), lower := (rows 37 74 84 392 50 33 64 128 256), losses := [] }

theorem u23125 : Upper (D 7) (R 7) [36,72,80,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23126 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 84 392 50 34 193 129 385), lower := (rows 37 74 84 392 50 34 64 128 256), losses := [] }

theorem u23126 : Upper (D 7) (R 7) [36,72,80,384,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23127 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(3,5)], upper := (rows 37 74 84 392 50 160 67 131 259), lower := (rows 37 74 84 392 50 160 64 128 256), losses := [] }

theorem u23127 : Upper (D 7) (R 7) [36,72,80,384,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23128 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 84 392 145 33 98 162 290), lower := (rows 37 74 84 392 145 33 64 128 256), losses := [] }

theorem u23128 : Upper (D 7) (R 7) [36,72,80,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23129 : Route 9 := (fun mask => (mask,id))

def c23129 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23129 : Upper (D 7) (R 7) [36,72,80,384,129,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384,129,2] 13 (by decide) (choices 1) [1,2,32] r23129 c23129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7269
  · exact u7270
  · exact u7271

def b23130 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 74 84 392 146 33 99 163 291), lower := (rows 37 74 84 392 146 33 64 128 256), losses := [] }

theorem u23130 : Upper (D 7) (R 7) [36,72,80,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23131 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 392, targets := 2 },{ cop := 0, region := 392, targets := 64 }], pairs := [(0,7),(2,7),(3,1),(3,6)], upper := (rows 37 74 84 392 146 34 97 161 289), lower := (rows 37 74 84 392 146 34 64 128 256), losses := [] }

theorem u23131 : Upper (D 7) (R 7) [36,72,80,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23132 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 84 392 176 33 67 131 259), lower := (rows 37 74 84 392 176 33 64 128 256), losses := [] }

theorem u23132 : Upper (D 7) (R 7) [36,72,80,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23133 : Route 9 := (fun mask => (mask,id))

def c23133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23133 : Upper (D 7) (R 7) [36,72,80,384,160,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,384,160,2] 13 (by decide) (choices 1) [1,2] r23133 c23133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7272
  · exact u7273

def b23134 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 133 138 50 33 336 464 336), lower := (rows 37 74 133 138 50 33 64 128 256), losses := [] }

theorem u23134 : Upper (D 7) (R 7) [36,72,129,130,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23135 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 133 138 50 48 321 449 321), lower := (rows 37 74 133 138 50 48 64 128 256), losses := [] }

theorem u23135 : Upper (D 7) (R 7) [36,72,129,130,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23135 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23136 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 133 138 50 96 337 401 273), lower := (rows 37 74 133 138 50 96 64 128 256), losses := [] }

theorem u23136 : Upper (D 7) (R 7) [36,72,129,130,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23137 : Route 9 := (fun mask => (mask,id))

def c23137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23137 : Upper (D 7) (R 7) [36,72,129,130,34,256] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130,34,256] 13 (by decide) (choices 1) [1,16] r23137 c23137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7274
  · exact u7275

def b23138 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 138 112 33 338 402 274), lower := (rows 37 74 133 138 112 33 64 128 256), losses := [] }

theorem u23138 : Upper (D 7) (R 7) [36,72,129,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23139 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,1),(2,1),(4,0),(4,1)], upper := (rows 37 74 133 138 112 34 337 401 273), lower := (rows 37 74 133 138 112 34 64 128 256), losses := [] }

theorem u23139 : Upper (D 7) (R 7) [36,72,129,130,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23140 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 133 138 112 48 323 387 259), lower := (rows 37 74 133 138 112 48 64 128 256), losses := [] }

theorem u23140 : Upper (D 7) (R 7) [36,72,129,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23140 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m23141_1 : Upper (D 7) (R 7) [36,72,129,130,96,256,1] 13 :=
  permutation_upper _ _ _ [36,72,129,130,96,2,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7277

theorem m23141_2 : Upper (D 7) (R 7) [36,72,129,130,96,256,2] 13 :=
  permutation_upper _ _ _ [36,72,129,130,96,1,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7276

theorem m23141_16 : Upper (D 7) (R 7) [36,72,129,130,96,256,16] 13 :=
  permutation_upper _ _ _ [36,72,129,130,96,16,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7278

def r23141 : Route 9 := (fun mask => (mask,id))

def c23141 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23141 : Upper (D 7) (R 7) [36,72,129,130,96,256] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130,96,256] 13 (by decide) (choices 1) [1,2,16] r23141 c23141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m23141_1
  · exact m23141_2
  · exact m23141_16

def b23142 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(4,1)], upper := (rows 37 74 133 138 273 34 112 240 368), lower := (rows 37 74 133 138 273 34 64 128 256), losses := [] }

theorem u23142 : Upper (D 7) (R 7) [36,72,129,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23143 : Route 9 := (fun mask => (mask,id))

def c23143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23143 : Upper (D 7) (R 7) [36,72,129,130,257,16] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130,257,16] 13 (by decide) (choices 1) [2,32] r23143 c23143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7279
  · exact u7280

def b23144 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 133 138 273 96 114 178 306), lower := (rows 37 74 133 138 273 96 64 128 256), losses := [{ target := 1, region := (rows 11 0 12 8 16 98 64 128 256), good := (rows 37 109 133 173 273 96 96 128 256) }] }

theorem u23144 : Upper (D 7) (R 7) [36,72,129,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23145 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 138 304 33 82 210 338), lower := (rows 37 74 133 138 304 33 64 128 256), losses := [] }

theorem u23145 : Upper (D 7) (R 7) [36,72,129,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23146 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(4,1)], upper := (rows 37 74 133 138 304 34 81 209 337), lower := (rows 37 74 133 138 304 34 64 128 256), losses := [] }

theorem u23146 : Upper (D 7) (R 7) [36,72,129,130,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23147 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 74 133 138 304 48 67 195 323), lower := (rows 37 74 133 138 304 48 64 128 256), losses := [] }

theorem u23147 : Upper (D 7) (R 7) [36,72,129,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23147 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23148 : Route 9 := (fun mask => (mask,id))

def c23148 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23148 : Upper (D 7) (R 7) [36,72,129,130,288,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130,288,64] 13 (by decide) (choices 1) [1,2,16] r23148 c23148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7281
  · exact u7282
  · exact u7283

def b23149 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 453, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 133 152 19 34 352 480 352), lower := (rows 37 74 133 152 19 34 64 128 256), losses := [] }

theorem u23149 : Upper (D 7) (R 7) [36,72,129,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23150 : Route 9 := (fun mask => (mask,id))

def c23150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u23150 : Upper (D 7) (R 7) [36,72,129,144,3,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,3,64] 13 (by decide) (choices 1) [2,32,256] r23150 c23150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7284
  · exact u7285
  · exact u7286

def b23151 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 74 133 152 19 288 98 226 354), lower := (rows 37 74 133 152 19 288 64 128 256), losses := [] }

theorem u23151 : Upper (D 7) (R 7) [36,72,129,144,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23151 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23152 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 50 33 322 450 322), lower := (rows 37 74 133 152 50 33 64 128 256), losses := [] }

theorem u23152 : Upper (D 7) (R 7) [36,72,129,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23153 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 74 133 152 50 34 321 449 321), lower := (rows 37 74 133 152 50 34 64 128 256), losses := [] }

theorem u23153 : Upper (D 7) (R 7) [36,72,129,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23154 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 133 152 50 96 323 387 259), lower := (rows 37 74 133 152 50 96 64 128 256), losses := [] }

theorem u23154 : Upper (D 7) (R 7) [36,72,129,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23155 : Route 9 := (fun mask => (mask,id))

def c23155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23155 : Upper (D 7) (R 7) [36,72,129,144,34,256] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,34,256] 13 (by decide) (choices 1) [1,2] r23155 c23155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7287
  · exact u7288

def b23156 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 112 33 322 386 258), lower := (rows 37 74 133 152 112 33 64 128 256), losses := [] }

theorem u23156 : Upper (D 7) (R 7) [36,72,129,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23157 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 48, targets := 129 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,7)], upper := (rows 37 74 133 152 112 34 323 387 259), lower := (rows 37 74 133 152 112 34 64 128 256), losses := [] }

theorem u23157 : Upper (D 7) (R 7) [36,72,129,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23158 : Route 9 := (fun mask => (mask,id))

def c23158 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23158 : Upper (D 7) (R 7) [36,72,129,144,96,256] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,96,256] 13 (by decide) (choices 1) [1,2] r23158 c23158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7289
  · exact u7290

def b23159 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 37 74 133 152 273 34 98 226 354), lower := (rows 37 74 133 152 273 34 64 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 17 42 106 0 298), good := (rows 373 362 21 378 273 354 64 0 256) }] }

theorem u23159 : Upper (D 7) (R 7) [36,72,129,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23159
end Delivery.IrregularNine14.P07
