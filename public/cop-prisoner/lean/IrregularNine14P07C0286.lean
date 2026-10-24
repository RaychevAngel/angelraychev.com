import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0068
import IrregularNine14P07C0069

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17160 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 296 19 96 209 145 401), lower := (rows 13 98 134 296 19 96 64 128 256), losses := [] }

theorem u17160 : Upper (D 7) (R 7) [12,96,130,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17161 : Route 9 := (fun mask => (mask,id))

def c17161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17161 : Upper (D 7) (R 7) [12,96,130,288,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,3,128] 13 (by decide) (choices 1) [1,16] r17161 c17161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4121
  · exact u4122

def r17162 : Route 9 := (fun mask => (mask,id))

def c17162 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17162 : Upper (D 7) (R 7) [12,96,130,288,65,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,65,1] 13 (by decide) (choices 1) [2,16,128] r17162 c17162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4123
  · exact u4124
  · exact u4125

def b17163 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 134 296 81 34 209 145 401), lower := (rows 13 98 134 296 81 34 64 128 256), losses := [] }

theorem u17163 : Upper (D 7) (R 7) [12,96,130,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17164 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 134 296 81 48 195 131 387), lower := (rows 13 98 134 296 81 48 64 128 256), losses := [] }

theorem u17164 : Upper (D 7) (R 7) [12,96,130,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17164 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17165 : Route 9 := (fun mask => (mask,id))

def c17165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17165 : Upper (D 7) (R 7) [12,96,130,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,65,128] 13 (by decide) (choices 1) [1,2,16] r17165 c17165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4126
  · exact u4127
  · exact u4128

def r17166 : Route 9 := (fun mask => (mask,id))

def c17166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17166 : Upper (D 7) (R 7) [12,96,130,288,129,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,129,1] 13 (by decide) (choices 1) [2,16] r17166 c17166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4129
  · exact u4130

def b17167 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,5)], upper := (rows 13 98 134 296 145 34 81 209 337), lower := (rows 13 98 134 296 145 34 64 128 256), losses := [] }

theorem u17167 : Upper (D 7) (R 7) [12,96,130,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17168 : Route 9 := (fun mask => (mask,id))

def c17168 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17168 : Upper (D 7) (R 7) [12,96,130,288,129,16] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,129,16] 13 (by decide) (choices 1) [1,2] r17168 c17168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4131
  · exact u4132

def b17169 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 296 145 96 83 147 275), lower := (rows 13 98 134 296 145 96 64 128 256), losses := [] }

theorem u17169 : Upper (D 7) (R 7) [12,96,130,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17170 : Route 9 := (fun mask => (mask,id))

def c17170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17170 : Upper (D 7) (R 7) [12,96,130,288,192,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,192,1] 13 (by decide) (choices 1) [1,2,16] r17170 c17170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4133
  · exact u4134
  · exact u4135

def b17171 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(2,0),(4,1),(4,5)], upper := (rows 13 98 134 296 208 34 81 145 273), lower := (rows 13 98 134 296 208 34 64 128 256), losses := [] }

theorem u17171 : Upper (D 7) (R 7) [12,96,130,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17172 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 134 296 208 48 67 131 259), lower := (rows 13 98 134 296 208 48 64 128 256), losses := [] }

theorem u17172 : Upper (D 7) (R 7) [12,96,130,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17172 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17173 : Route 9 := (fun mask => (mask,id))

def c17173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17173 : Upper (D 7) (R 7) [12,96,130,384,3,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,384,3,1] 13 (by decide) (choices 1) [16,32] r17173 c17173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4136
  · exact u4137

def b17174 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 4, region := 488, targets := 2 }], pairs := [(1,7),(3,1),(4,7)], upper := (rows 13 98 134 392 19 48 97 225 353), lower := (rows 13 98 134 392 19 48 64 128 256), losses := [] }

theorem u17174 : Upper (D 7) (R 7) [12,96,130,384,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17174 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17175 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 392 19 96 113 177 305), lower := (rows 13 98 134 392 19 96 64 128 256), losses := [] }

theorem u17175 : Upper (D 7) (R 7) [12,96,130,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17176 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 48, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 98 134 392 49 33 82 210 338), lower := (rows 13 98 134 392 49 33 64 128 256), losses := [] }

theorem u17176 : Upper (D 7) (R 7) [12,96,130,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17177 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 4, region := 456, targets := 34 }], pairs := [(1,7),(3,1),(3,5),(4,7)], upper := (rows 13 98 134 392 49 34 81 209 337), lower := (rows 13 98 134 392 49 34 64 128 256), losses := [] }

theorem u17177 : Upper (D 7) (R 7) [12,96,130,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17178 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 134 392 49 48 67 195 323), lower := (rows 13 98 134 392 49 48 64 128 256), losses := [] }

theorem u17178 : Upper (D 7) (R 7) [12,96,130,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17178 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17179 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 392 49 96 83 147 275), lower := (rows 13 98 134 392 49 96 64 128 256), losses := [] }

theorem u17179 : Upper (D 7) (R 7) [12,96,130,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17180 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 148 168 19 33 322 450 322), lower := (rows 13 98 148 168 19 33 64 128 256), losses := [] }

theorem u17180 : Upper (D 7) (R 7) [12,96,144,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17181 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 4, region := 452, targets := 34 }], pairs := [(1,7),(2,1),(2,5),(4,7)], upper := (rows 13 98 148 168 19 34 321 449 321), lower := (rows 13 98 148 168 19 34 64 128 256), losses := [] }

theorem u17181 : Upper (D 7) (R 7) [12,96,144,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17182 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 168 19 96 323 387 259), lower := (rows 13 98 148 168 19 96 64 128 256), losses := [] }

theorem u17182 : Upper (D 7) (R 7) [12,96,144,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17183 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,7),(2,5),(4,7)], upper := (rows 13 98 148 168 19 288 67 195 323), lower := (rows 13 98 148 168 19 288 64 128 256), losses := [] }

theorem u17183 : Upper (D 7) (R 7) [12,96,144,160,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17183 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17184 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 148 168 81 33 322 386 258), lower := (rows 13 98 148 168 81 33 64 128 256), losses := [] }

theorem u17184 : Upper (D 7) (R 7) [12,96,144,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17185 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 148 168 81 34 323 387 259), lower := (rows 13 98 148 168 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 82 4 12 16 118 64 128 256), good := (rows 44 98 190 168 114 34 98 128 256) }] }

theorem u17185 : Upper (D 7) (R 7) [12,96,144,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17186 : Route 9 := (fun mask => (mask,id))

def c17186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17186 : Upper (D 7) (R 7) [12,96,144,160,65,256] 13 := by
  apply FastRouting.sound _ _ [12,96,144,160,65,256] 13 (by decide) (choices 1) [1,2] r17186 c17186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4138
  · exact u4139

def b17187 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 148 168 273 33 66 194 322), lower := (rows 13 98 148 168 273 33 64 128 256), losses := [] }

theorem u17187 : Upper (D 7) (R 7) [12,96,144,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17188 : Route 9 := (fun mask => (mask,id))

def c17188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17188 : Upper (D 7) (R 7) [12,96,144,160,257,2] 13 := by
  apply FastRouting.sound _ _ [12,96,144,160,257,2] 13 (by decide) (choices 1) [1,2] r17188 c17188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4140
  · exact u4141

def b17189 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 168 273 96 67 131 259), lower := (rows 13 98 148 168 273 96 64 128 256), losses := [] }

theorem u17189 : Upper (D 7) (R 7) [12,96,144,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17190 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 148 168 274 33 67 195 323), lower := (rows 13 98 148 168 274 33 64 128 256), losses := [] }

theorem u17190 : Upper (D 7) (R 7) [12,96,144,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17191 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 148 168 274 34 65 193 321), lower := (rows 13 98 148 168 274 34 64 128 256), losses := [{ target := 0, region := (rows 0 66 4 12 16 114 64 128 256), good := (rows 12 98 188 168 306 34 98 128 256) }] }

theorem u17191 : Upper (D 7) (R 7) [12,96,144,160,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17192 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 168 274 96 67 131 259), lower := (rows 13 98 148 168 274 96 64 128 256), losses := [] }

theorem u17192 : Upper (D 7) (R 7) [12,96,144,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17193 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 148 168 336 33 67 131 259), lower := (rows 13 98 148 168 336 33 64 128 256), losses := [] }

theorem u17193 : Upper (D 7) (R 7) [12,96,144,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17194 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 148 168 336 34 67 131 259), lower := (rows 13 98 148 168 336 34 64 128 256), losses := [{ target := 0, region := (rows 0 82 4 12 16 118 64 128 256), good := (rows 44 98 190 168 370 34 98 128 256) }] }

theorem u17194 : Upper (D 7) (R 7) [12,96,144,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17195 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,0)], upper := (rows 13 98 148 265 19 34 224 224 480), lower := (rows 13 98 148 265 19 34 64 128 256), losses := [{ target := 1, region := (rows 21 0 20 24 16 32 98 162 290), good := (rows 13 480 157 265 477 480 64 128 256) }] }

theorem u17195 : Upper (D 7) (R 7) [12,96,144,257,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17196 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 265 19 96 226 162 418), lower := (rows 13 98 148 265 19 96 64 128 256), losses := [] }

theorem u17196 : Upper (D 7) (R 7) [12,96,144,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17197 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 13 98 148 265 19 160 98 226 354), lower := (rows 13 98 148 265 19 160 64 128 256), losses := [{ target := 7, region := (rows 5 34 4 24 16 32 98 0 290), good := (rows 13 354 29 265 347 354 64 0 256) }] }

theorem u17197 : Upper (D 7) (R 7) [12,96,144,257,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17198 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(2,0)], upper := (rows 13 98 148 265 49 34 194 194 450), lower := (rows 13 98 148 265 49 34 64 128 256), losses := [{ target := 5, region := (rows 21 2 20 24 16 0 98 162 290), good := (rows 13 450 157 265 477 450 64 128 256) }] }

theorem u17198 : Upper (D 7) (R 7) [12,96,144,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17199 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 265 49 96 194 130 386), lower := (rows 13 98 148 265 49 96 64 128 256), losses := [] }

theorem u17199 : Upper (D 7) (R 7) [12,96,144,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17200 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 4, region := 330, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 148 265 49 160 66 194 322), lower := (rows 13 98 148 265 49 160 64 128 256), losses := [] }

theorem u17200 : Upper (D 7) (R 7) [12,96,144,257,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17201 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 458, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(1,0),(2,0),(2,1),(3,0)], upper := (rows 13 98 148 266 19 33 224 224 480), lower := (rows 13 98 148 266 19 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 20 58 16 32 98 162 290), good := (rows 12 490 156 458 478 490 64 128 256) }] }

theorem u17201 : Upper (D 7) (R 7) [12,96,144,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17202 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 266 19 96 225 161 417), lower := (rows 13 98 148 266 19 96 64 128 256), losses := [] }

theorem u17202 : Upper (D 7) (R 7) [12,96,144,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17203_1 : Upper (D 7) (R 7) [12,96,144,258,3,128,1] 13 :=
  permutation_upper _ _ _ [12,96,144,258,3,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4142

theorem m17203_32 : Upper (D 7) (R 7) [12,96,144,258,3,128,32] 13 :=
  permutation_upper _ _ _ [12,96,144,258,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4143

def r17203 : Route 9 := (fun mask => (mask,id))

def c17203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17203 : Upper (D 7) (R 7) [12,96,144,258,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,144,258,3,128] 13 (by decide) (choices 1) [1,32] r17203 c17203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17203_1
  · exact m17203_32

def b17204 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 13 98 148 266 49 33 194 194 450), lower := (rows 13 98 148 266 49 33 64 128 256), losses := [] }

theorem u17204 : Upper (D 7) (R 7) [12,96,144,258,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17205 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 13 98 148 266 49 34 193 193 449), lower := (rows 13 98 148 266 49 34 64 128 256), losses := [] }

theorem u17205 : Upper (D 7) (R 7) [12,96,144,258,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17206 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 266 49 96 195 131 387), lower := (rows 13 98 148 266 49 96 64 128 256), losses := [] }

theorem u17206 : Upper (D 7) (R 7) [12,96,144,258,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17207 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 330, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 13 98 148 266 49 160 67 195 323), lower := (rows 13 98 148 266 49 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 164 64 128 256), good := (rows 61 96 180 264 49 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 17 164 0 128 256), good := (rows 61 34 180 266 49 160 0 160 256) }] }

theorem u17207 : Upper (D 7) (R 7) [12,96,144,258,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17208 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 196, targets := 33 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(3,0)], upper := (rows 13 98 148 296 19 33 194 194 450), lower := (rows 13 98 148 296 19 33 64 128 256), losses := [] }

theorem u17208 : Upper (D 7) (R 7) [12,96,144,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17209 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 13 98 148 296 19 34 193 193 449), lower := (rows 13 98 148 296 19 34 64 128 256), losses := [] }

theorem u17209 : Upper (D 7) (R 7) [12,96,144,288,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17210 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 296 19 96 195 131 387), lower := (rows 13 98 148 296 19 96 64 128 256), losses := [] }

theorem u17210 : Upper (D 7) (R 7) [12,96,144,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17211 : Route 9 := (fun mask => (mask,id))

def c17211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17211 : Upper (D 7) (R 7) [12,96,144,288,3,128] 13 := by
  apply FastRouting.sound _ _ [12,96,144,288,3,128] 13 (by decide) (choices 1) [1,2] r17211 c17211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4144
  · exact u4145

def b17212 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 458, targets := 1 },{ cop := 1, region := 392, targets := 64 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(3,6)], upper := (rows 13 98 148 296 81 33 194 130 386), lower := (rows 13 98 148 296 81 33 64 128 256), losses := [] }

theorem u17212 : Upper (D 7) (R 7) [12,96,144,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17213 : Route 9 := (fun mask => (mask,id))

def c17213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17213 : Upper (D 7) (R 7) [12,96,144,288,65,2] 13 := by
  apply FastRouting.sound _ _ [12,96,144,288,65,2] 13 (by decide) (choices 1) [1,2,128] r17213 c17213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4146
  · exact u4147
  · exact u4148

def r17214 : Route 9 := (fun mask => (mask,id))

def c17214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17214 : Upper (D 7) (R 7) [12,96,144,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,144,288,65,128] 13 (by decide) (choices 1) [1,2] r17214 c17214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4149
  · exact u4150

def b17215 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 148 392 19 33 98 226 354), lower := (rows 13 98 148 392 19 33 64 128 256), losses := [] }

theorem u17215 : Upper (D 7) (R 7) [12,96,144,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17216_1 : Upper (D 7) (R 7) [12,96,144,384,3,2,1] 13 :=
  permutation_upper _ _ _ [12,96,144,384,3,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4151

def r17216 : Route 9 := (fun mask => (mask,id))

def c17216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17216 : Upper (D 7) (R 7) [12,96,144,384,3,2] 13 := by
  apply FastRouting.sound _ _ [12,96,144,384,3,2] 13 (by decide) (choices 1) [1,32] r17216 c17216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17216_1
  · exact u4152

def b17217 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 392 19 96 99 163 291), lower := (rows 13 98 148 392 19 96 64 128 256), losses := [] }

theorem u17217 : Upper (D 7) (R 7) [12,96,144,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17218 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 148 392 49 33 66 194 322), lower := (rows 13 98 148 392 49 33 64 128 256), losses := [] }

theorem u17218 : Upper (D 7) (R 7) [12,96,144,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17219 : Route 9 := (fun mask => (mask,id))

def c17219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17219 : Upper (D 7) (R 7) [12,96,144,384,33,2] 13 := by
  apply FastRouting.sound _ _ [12,96,144,384,33,2] 13 (by decide) (choices 1) [1,2] r17219 c17219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4153
  · exact u4154

#print axioms u17219
end Delivery.IrregularNine14.P07
