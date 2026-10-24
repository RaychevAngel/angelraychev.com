import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0165
import IrregularNine14P07C0166

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27120 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 37 322 7 25 146 160 104 232 360), lower := (rows 37 322 7 25 146 160 64 128 256), losses := [] }

theorem u27120 : Upper (D 7) (R 7) [36,320,3,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27121 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 25 152 34 224 224 480), lower := (rows 37 322 7 25 152 34 64 128 256), losses := [] }

theorem u27121 : Upper (D 7) (R 7) [36,320,3,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27122 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 322 7 25 152 96 226 162 418), lower := (rows 37 322 7 25 152 96 64 128 256), losses := [] }

theorem u27122 : Upper (D 7) (R 7) [36,320,3,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27123 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 322 7 25 152 160 98 226 354), lower := (rows 37 322 7 25 152 160 64 128 256), losses := [] }

theorem u27123 : Upper (D 7) (R 7) [36,320,3,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27124 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 25 208 34 232 168 424), lower := (rows 37 322 7 25 208 34 64 128 256), losses := [] }

theorem u27124 : Upper (D 7) (R 7) [36,320,3,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27125 : Route 9 := (fun mask => (mask,id))

def c27125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27125 : Upper (D 7) (R 7) [36,320,3,17,192,8] 13 := by
  apply FastRouting.sound _ _ [36,320,3,17,192,8] 13 (by decide) (choices 1) [2,32,128] r27125 c27125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9928
  · exact u9929
  · exact u9930

def r27126 : Route 9 := (fun mask => (mask,id))

def c27126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27126 : Upper (D 7) (R 7) [36,320,3,17,192,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,17,192,128] 13 (by decide) (choices 1) [2,8,32] r27126 c27126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9931
  · exact u9932
  · exact u9933

def b27127 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 7 26 112 33 200 136 392), lower := (rows 37 322 7 26 112 33 64 128 256), losses := [] }

theorem u27127 : Upper (D 7) (R 7) [36,320,3,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27128 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 7 26 112 40 193 129 385), lower := (rows 37 322 7 26 112 40 64 128 256), losses := [] }

theorem u27128 : Upper (D 7) (R 7) [36,320,3,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27128 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27129 : Route 9 := (fun mask => (mask,id))

def c27129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27129 : Upper (D 7) (R 7) [36,320,3,18,96,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,18,96,128] 13 (by decide) (choices 1) [1,8,128] r27129 c27129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9934
  · exact u9935
  · exact u9936

def b27130 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 7 26 145 40 224 224 480), lower := (rows 37 322 7 26 145 40 64 128 256), losses := [] }

theorem u27130 : Upper (D 7) (R 7) [36,320,3,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27130 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27131 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 322 7 26 145 96 232 168 424), lower := (rows 37 322 7 26 145 96 64 128 256), losses := [] }

theorem u27131 : Upper (D 7) (R 7) [36,320,3,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27132 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 322 7 26 145 160 104 232 360), lower := (rows 37 322 7 26 145 160 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 37 258 7 63 177 160 0 160 256) }] }

theorem u27132 : Upper (D 7) (R 7) [36,320,3,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27133 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 26 152 33 224 224 480), lower := (rows 37 322 7 26 152 33 64 128 256), losses := [] }

theorem u27133 : Upper (D 7) (R 7) [36,320,3,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27134 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 322 7 26 152 96 225 161 417), lower := (rows 37 322 7 26 152 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 21 32 0 129 257), good := (rows 445 258 415 26 152 32 0 128 256) }] }

theorem u27134 : Upper (D 7) (R 7) [36,320,3,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27135 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 322 7 26 152 160 97 225 353), lower := (rows 37 322 7 26 152 160 64 128 256), losses := [] }

theorem u27135 : Upper (D 7) (R 7) [36,320,3,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27136 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 26 176 33 200 200 456), lower := (rows 37 322 7 26 176 33 64 128 256), losses := [] }

theorem u27136 : Upper (D 7) (R 7) [36,320,3,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27137 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 7 26 176 40 193 193 449), lower := (rows 37 322 7 26 176 40 64 128 256), losses := [] }

theorem u27137 : Upper (D 7) (R 7) [36,320,3,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27137 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27138 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 322 7 26 176 96 201 137 393), lower := (rows 37 322 7 26 176 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 352 37 56 176 96 96 128 256) },{ target := 6, region := (rows 1 2 4 12 17 32 0 133 261), good := (rows 445 258 415 26 176 32 0 128 256) }] }

theorem u27138 : Upper (D 7) (R 7) [36,320,3,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27139 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 7 26 176 160 73 201 329), lower := (rows 37 322 7 26 176 160 64 128 256), losses := [] }

theorem u27139 : Upper (D 7) (R 7) [36,320,3,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27140 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 26 208 33 232 168 424), lower := (rows 37 322 7 26 208 33 64 128 256), losses := [] }

theorem u27140 : Upper (D 7) (R 7) [36,320,3,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27141 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 7 26 208 40 225 161 417), lower := (rows 37 322 7 26 208 40 64 128 256), losses := [] }

theorem u27141 : Upper (D 7) (R 7) [36,320,3,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27141 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27142 : Route 9 := (fun mask => (mask,id))

def c27142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27142 : Upper (D 7) (R 7) [36,320,3,18,192,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,18,192,128] 13 (by decide) (choices 1) [1,8,32] r27142 c27142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9937
  · exact u9938
  · exact u9939

def b27143 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 7 56 81 34 200 136 392), lower := (rows 37 322 7 56 81 34 64 128 256), losses := [] }

theorem u27143 : Upper (D 7) (R 7) [36,320,3,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27144 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 7 56 81 40 194 130 386), lower := (rows 37 322 7 56 81 40 64 128 256), losses := [] }

theorem u27144 : Upper (D 7) (R 7) [36,320,3,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27144 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27145 : Route 9 := (fun mask => (mask,id))

def c27145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27145 : Upper (D 7) (R 7) [36,320,3,48,65,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,48,65,128] 13 (by decide) (choices 1) [2,8,128] r27145 c27145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9940
  · exact u9941
  · exact u9942

def b27146 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 56 145 34 200 200 456), lower := (rows 37 322 7 56 145 34 64 128 256), losses := [] }

theorem u27146 : Upper (D 7) (R 7) [36,320,3,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27147 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 7 56 145 40 194 194 450), lower := (rows 37 322 7 56 145 40 64 128 256), losses := [] }

theorem u27147 : Upper (D 7) (R 7) [36,320,3,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27147 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27148 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 322 7 56 145 96 202 138 394), lower := (rows 37 322 7 56 145 96 64 128 256), losses := [] }

theorem u27148 : Upper (D 7) (R 7) [36,320,3,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27149 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 322 7 56 145 160 74 202 330), lower := (rows 37 322 7 56 145 160 64 128 256), losses := [] }

theorem u27149 : Upper (D 7) (R 7) [36,320,3,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27150 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 56 146 33 200 200 456), lower := (rows 37 322 7 56 146 33 64 128 256), losses := [] }

theorem u27150 : Upper (D 7) (R 7) [36,320,3,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27151 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 7 56 146 40 193 193 449), lower := (rows 37 322 7 56 146 40 64 128 256), losses := [] }

theorem u27151 : Upper (D 7) (R 7) [36,320,3,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27151 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27152 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,0)], upper := (rows 37 322 7 56 146 96 201 137 393), lower := (rows 37 322 7 56 146 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 98 64 128 256), good := (rows 36 354 38 56 186 96 96 128 256) },{ target := 1, region := (rows 5 0 4 24 16 98 64 128 256), good := (rows 37 352 37 56 184 96 96 128 256) }] }

theorem u27152 : Upper (D 7) (R 7) [36,320,3,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27153 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 322 7 56 146 160 73 201 329), lower := (rows 37 322 7 56 146 160 64 128 256), losses := [] }

theorem u27153 : Upper (D 7) (R 7) [36,320,3,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27154 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 56 152 33 194 194 450), lower := (rows 37 322 7 56 152 33 64 128 256), losses := [] }

theorem u27154 : Upper (D 7) (R 7) [36,320,3,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27155 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 56 152 34 193 193 449), lower := (rows 37 322 7 56 152 34 64 128 256), losses := [] }

theorem u27155 : Upper (D 7) (R 7) [36,320,3,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27156 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(2,7)], upper := (rows 37 322 7 56 152 96 195 131 387), lower := (rows 37 322 7 56 152 96 64 128 256), losses := [] }

theorem u27156 : Upper (D 7) (R 7) [36,320,3,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27157 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 37 322 7 56 152 160 67 195 323), lower := (rows 37 322 7 56 152 160 64 128 256), losses := [] }

theorem u27157 : Upper (D 7) (R 7) [36,320,3,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27158 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 56 208 33 202 138 394), lower := (rows 37 322 7 56 208 33 64 128 256), losses := [] }

theorem u27158 : Upper (D 7) (R 7) [36,320,3,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27159 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 56 208 34 201 137 393), lower := (rows 37 322 7 56 208 34 64 128 256), losses := [] }

theorem u27159 : Upper (D 7) (R 7) [36,320,3,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27160 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 322 7 56 208 40 195 131 387), lower := (rows 37 322 7 56 208 40 64 128 256), losses := [] }

theorem u27160 : Upper (D 7) (R 7) [36,320,3,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27160 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27161 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 322 7 56 208 160 75 139 267), lower := (rows 37 322 7 56 208 160 64 128 256), losses := [] }

theorem u27161 : Upper (D 7) (R 7) [36,320,3,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27162 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 7 73 146 40 240 176 432), lower := (rows 37 322 7 73 146 40 64 128 256), losses := [] }

theorem u27162 : Upper (D 7) (R 7) [36,320,3,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27162 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27163 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 7 73 146 48 232 168 424), lower := (rows 37 322 7 73 146 48 64 128 256), losses := [] }

theorem u27163 : Upper (D 7) (R 7) [36,320,3,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27163 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27164 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 322 7 73 146 160 120 184 312), lower := (rows 37 322 7 73 146 160 64 128 256), losses := [] }

theorem u27164 : Upper (D 7) (R 7) [36,320,3,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27165 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 73 152 34 240 176 432), lower := (rows 37 322 7 73 152 34 64 128 256), losses := [] }

theorem u27165 : Upper (D 7) (R 7) [36,320,3,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27166 : Route 9 := (fun mask => (mask,id))

def c27166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27166 : Upper (D 7) (R 7) [36,320,3,65,136,16] 13 := by
  apply FastRouting.sound _ _ [36,320,3,65,136,16] 13 (by decide) (choices 1) [2,32,128] r27166 c27166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9943
  · exact u9944
  · exact u9945

def r27167 : Route 9 := (fun mask => (mask,id))

def c27167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27167 : Upper (D 7) (R 7) [36,320,3,65,136,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,65,136,128] 13 (by decide) (choices 1) [2,16,32] r27167 c27167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9946
  · exact u9947
  · exact u9948

def b27168 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 73 176 34 216 152 408), lower := (rows 37 322 7 73 176 34 64 128 256), losses := [] }

theorem u27168 : Upper (D 7) (R 7) [36,320,3,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27169 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 7 73 176 40 210 146 402), lower := (rows 37 322 7 73 176 40 64 128 256), losses := [] }

theorem u27169 : Upper (D 7) (R 7) [36,320,3,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27169 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27170 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 7 73 176 48 202 138 394), lower := (rows 37 322 7 73 176 48 64 128 256), losses := [] }

theorem u27170 : Upper (D 7) (R 7) [36,320,3,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27170 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27171 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 7 73 176 160 90 154 282), lower := (rows 37 322 7 73 176 160 64 128 256), losses := [] }

theorem u27171 : Upper (D 7) (R 7) [36,320,3,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27172 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 88 145 34 232 168 424), lower := (rows 37 322 7 88 145 34 64 128 256), losses := [] }

theorem u27172 : Upper (D 7) (R 7) [36,320,3,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27173 : Route 9 := (fun mask => (mask,id))

def c27173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27173 : Upper (D 7) (R 7) [36,320,3,80,129,8] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80,129,8] 13 (by decide) (choices 1) [2,32,128] r27173 c27173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9949
  · exact u9950
  · exact u9951

def r27174 : Route 9 := (fun mask => (mask,id))

def c27174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27174 : Upper (D 7) (R 7) [36,320,3,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80,129,128] 13 (by decide) (choices 1) [2,8,32] r27174 c27174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9952
  · exact u9953
  · exact u9954

def b27175 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 88 146 33 232 168 424), lower := (rows 37 322 7 88 146 33 64 128 256), losses := [] }

theorem u27175 : Upper (D 7) (R 7) [36,320,3,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27176 : Route 9 := (fun mask => (mask,id))

def c27176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27176 : Upper (D 7) (R 7) [36,320,3,80,130,8] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80,130,8] 13 (by decide) (choices 1) [1,32,128] r27176 c27176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9955
  · exact u9956
  · exact u9957

def r27177 : Route 9 := (fun mask => (mask,id))

def c27177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27177 : Upper (D 7) (R 7) [36,320,3,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80,130,128] 13 (by decide) (choices 1) [1,8,32] r27177 c27177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9958
  · exact u9959
  · exact u9960

def b27178 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 474, targets := 1 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 322 7 88 152 33 226 162 418), lower := (rows 37 322 7 88 152 33 64 128 256), losses := [] }

theorem u27178 : Upper (D 7) (R 7) [36,320,3,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27179 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 37 322 7 88 152 34 225 161 417), lower := (rows 37 322 7 88 152 34 64 128 256), losses := [] }

theorem u27179 : Upper (D 7) (R 7) [36,320,3,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27179
end Delivery.IrregularNine14.P07
