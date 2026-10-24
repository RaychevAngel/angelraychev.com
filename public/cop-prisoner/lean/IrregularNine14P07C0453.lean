import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0166

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27180 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 322 7 88 152 160 99 163 291), lower := (rows 37 322 7 88 152 160 64 128 256), losses := [] }

theorem u27180 : Upper (D 7) (R 7) [36,320,3,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27181 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 88 176 33 202 138 394), lower := (rows 37 322 7 88 176 33 64 128 256), losses := [] }

theorem u27181 : Upper (D 7) (R 7) [36,320,3,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27182 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 88 176 34 201 137 393), lower := (rows 37 322 7 88 176 34 64 128 256), losses := [] }

theorem u27182 : Upper (D 7) (R 7) [36,320,3,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27183 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,6)], upper := (rows 37 322 7 88 176 40 195 131 387), lower := (rows 37 322 7 88 176 40 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 40 0 132 260), good := (rows 437 258 407 56 176 40 0 128 256) }] }

theorem u27183 : Upper (D 7) (R 7) [36,320,3,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27183 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27184 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 7 88 176 160 75 139 267), lower := (rows 37 322 7 88 176 160 64 128 256), losses := [] }

theorem u27184 : Upper (D 7) (R 7) [36,320,3,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27185 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 104 145 34 216 152 408), lower := (rows 37 322 7 104 145 34 64 128 256), losses := [] }

theorem u27185 : Upper (D 7) (R 7) [36,320,3,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27186 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 7 104 145 40 210 146 402), lower := (rows 37 322 7 104 145 40 64 128 256), losses := [] }

theorem u27186 : Upper (D 7) (R 7) [36,320,3,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27186 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27187 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 3, region := 386, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 322 7 104 145 48 202 138 394), lower := (rows 37 322 7 104 145 48 64 128 256), losses := [] }

theorem u27187 : Upper (D 7) (R 7) [36,320,3,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27187 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27188 : Route 9 := (fun mask => (mask,id))

def c27188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27188 : Upper (D 7) (R 7) [36,320,3,96,129,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,96,129,128] 13 (by decide) (choices 1) [2,8,16] r27188 c27188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9961
  · exact u9962
  · exact u9963

def b27189 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 7 104 146 33 216 152 408), lower := (rows 37 322 7 104 146 33 64 128 256), losses := [] }

theorem u27189 : Upper (D 7) (R 7) [36,320,3,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27190 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 7 104 146 40 209 145 401), lower := (rows 37 322 7 104 146 40 64 128 256), losses := [] }

theorem u27190 : Upper (D 7) (R 7) [36,320,3,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27190 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27191 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 7 104 146 48 201 137 393), lower := (rows 37 322 7 104 146 48 64 128 256), losses := [] }

theorem u27191 : Upper (D 7) (R 7) [36,320,3,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27191 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27192 : Route 9 := (fun mask => (mask,id))

def c27192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27192 : Upper (D 7) (R 7) [36,320,3,96,130,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,96,130,128] 13 (by decide) (choices 1) [1,8,16] r27192 c27192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9964
  · exact u9965
  · exact u9966

def b27193 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 7 104 152 33 210 146 402), lower := (rows 37 322 7 104 152 33 64 128 256), losses := [] }

theorem u27193 : Upper (D 7) (R 7) [36,320,3,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27194 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 104 152 34 209 145 401), lower := (rows 37 322 7 104 152 34 64 128 256), losses := [] }

theorem u27194 : Upper (D 7) (R 7) [36,320,3,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27195 : Route 9 := (fun mask => (mask,id))

def c27195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27195 : Upper (D 7) (R 7) [36,320,3,96,136,16] 13 := by
  apply FastRouting.sound _ _ [36,320,3,96,136,16] 13 (by decide) (choices 1) [1,2,128] r27195 c27195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9967
  · exact u9968
  · exact u9969

def r27196 : Route 9 := (fun mask => (mask,id))

def c27196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27196 : Upper (D 7) (R 7) [36,320,3,96,136,128] 13 := by
  apply FastRouting.sound _ _ [36,320,3,96,136,128] 13 (by decide) (choices 1) [1,2,16] r27196 c27196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9970
  · exact u9971
  · exact u9972

def b27197 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 7 137 146 40 112 240 368), lower := (rows 37 322 7 137 146 40 64 128 256), losses := [] }

theorem u27197 : Upper (D 7) (R 7) [36,320,3,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27197 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27198 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 7 137 146 48 104 232 360), lower := (rows 37 322 7 137 146 48 64 128 256), losses := [] }

theorem u27198 : Upper (D 7) (R 7) [36,320,3,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27198 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27199 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 322 7 137 146 96 120 184 312), lower := (rows 37 322 7 137 146 96 64 128 256), losses := [] }

theorem u27199 : Upper (D 7) (R 7) [36,320,3,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27200 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 137 176 34 88 216 344), lower := (rows 37 322 7 137 176 34 64 128 256), losses := [] }

theorem u27200 : Upper (D 7) (R 7) [36,320,3,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27201 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 7 137 176 40 82 210 338), lower := (rows 37 322 7 137 176 40 64 128 256), losses := [] }

theorem u27201 : Upper (D 7) (R 7) [36,320,3,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27201 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27202 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 7 137 176 48 74 202 330), lower := (rows 37 322 7 137 176 48 64 128 256), losses := [] }

theorem u27202 : Upper (D 7) (R 7) [36,320,3,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27202 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27203 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 322 7 137 176 96 90 154 282), lower := (rows 37 322 7 137 176 96 64 128 256), losses := [] }

theorem u27203 : Upper (D 7) (R 7) [36,320,3,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27204 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 137 208 34 120 184 312), lower := (rows 37 322 7 137 208 34 64 128 256), losses := [] }

theorem u27204 : Upper (D 7) (R 7) [36,320,3,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27205 : Route 9 := (fun mask => (mask,id))

def c27205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27205 : Upper (D 7) (R 7) [36,320,3,129,192,8] 13 := by
  apply FastRouting.sound _ _ [36,320,3,129,192,8] 13 (by decide) (choices 1) [2,16,32] r27205 c27205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9973
  · exact u9974
  · exact u9975

def r27206 : Route 9 := (fun mask => (mask,id))

def c27206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27206 : Upper (D 7) (R 7) [36,320,3,129,192,16] 13 := by
  apply FastRouting.sound _ _ [36,320,3,129,192,16] 13 (by decide) (choices 1) [2,8,32] r27206 c27206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9976
  · exact u9977
  · exact u9978

def b27207 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 138 176 33 88 216 344), lower := (rows 37 322 7 138 176 33 64 128 256), losses := [] }

theorem u27207 : Upper (D 7) (R 7) [36,320,3,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27208 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 322 7 138 176 40 81 209 337), lower := (rows 37 322 7 138 176 40 64 128 256), losses := [] }

theorem u27208 : Upper (D 7) (R 7) [36,320,3,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27208 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27209 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 7 138 176 48 73 201 329), lower := (rows 37 322 7 138 176 48 64 128 256), losses := [] }

theorem u27209 : Upper (D 7) (R 7) [36,320,3,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27209 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27210 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,0)], upper := (rows 37 322 7 138 176 96 89 153 281), lower := (rows 37 322 7 138 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 98 64 128 256), good := (rows 36 354 38 186 176 96 96 128 256) },{ target := 1, region := (rows 5 0 4 8 24 98 64 128 256), good := (rows 37 352 37 184 176 96 96 128 256) }] }

theorem u27210 : Upper (D 7) (R 7) [36,320,3,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27211 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 138 208 33 120 184 312), lower := (rows 37 322 7 138 208 33 64 128 256), losses := [] }

theorem u27211 : Upper (D 7) (R 7) [36,320,3,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27212 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 7 138 208 40 113 177 305), lower := (rows 37 322 7 138 208 40 64 128 256), losses := [] }

theorem u27212 : Upper (D 7) (R 7) [36,320,3,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27212 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27213 : Route 9 := (fun mask => (mask,id))

def c27213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27213 : Upper (D 7) (R 7) [36,320,3,130,192,16] 13 := by
  apply FastRouting.sound _ _ [36,320,3,130,192,16] 13 (by decide) (choices 1) [1,8,32] r27213 c27213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9979
  · exact u9980
  · exact u9981

def b27214 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 168 208 33 90 154 282), lower := (rows 37 322 7 168 208 33 64 128 256), losses := [] }

theorem u27214 : Upper (D 7) (R 7) [36,320,3,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27215 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 168 208 34 89 153 281), lower := (rows 37 322 7 168 208 34 64 128 256), losses := [] }

theorem u27215 : Upper (D 7) (R 7) [36,320,3,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27216 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 7 168 208 40 83 147 275), lower := (rows 37 322 7 168 208 40 64 128 256), losses := [] }

theorem u27216 : Upper (D 7) (R 7) [36,320,3,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27216 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27217 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 7 168 208 48 75 139 267), lower := (rows 37 322 7 168 208 48 64 128 256), losses := [] }

theorem u27217 : Upper (D 7) (R 7) [36,320,3,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27217 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27218 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 13 26 112 33 194 130 386), lower := (rows 37 322 13 26 112 33 64 128 256), losses := [] }

theorem u27218 : Upper (D 7) (R 7) [36,320,9,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27219 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 13 26 112 34 193 129 385), lower := (rows 37 322 13 26 112 34 64 128 256), losses := [] }

theorem u27219 : Upper (D 7) (R 7) [36,320,9,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27220 : Route 9 := (fun mask => (mask,id))

def c27220 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27220 : Upper (D 7) (R 7) [36,320,9,18,96,128] 13 := by
  apply FastRouting.sound _ _ [36,320,9,18,96,128] 13 (by decide) (choices 1) [1,2,128] r27220 c27220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9982
  · exact u9983
  · exact u9984

def b27221 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 26 145 34 224 224 480), lower := (rows 37 322 13 26 145 34 64 128 256), losses := [] }

theorem u27221 : Upper (D 7) (R 7) [36,320,9,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27222 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 322 13 26 145 96 226 162 418), lower := (rows 37 322 13 26 145 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 98 64 128 256), good := (rows 37 352 13 61 145 96 96 128 256) }] }

theorem u27222 : Upper (D 7) (R 7) [36,320,9,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27223 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 322 13 26 145 160 98 226 354), lower := (rows 37 322 13 26 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 320 13 61 177 160 64 160 256) }] }

theorem u27223 : Upper (D 7) (R 7) [36,320,9,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27224 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 26 176 33 194 194 450), lower := (rows 37 322 13 26 176 33 64 128 256), losses := [] }

theorem u27224 : Upper (D 7) (R 7) [36,320,9,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27225 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 26 176 34 193 193 449), lower := (rows 37 322 13 26 176 34 64 128 256), losses := [] }

theorem u27225 : Upper (D 7) (R 7) [36,320,9,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27226 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(2,1)], upper := (rows 37 322 13 26 176 96 195 131 387), lower := (rows 37 322 13 26 176 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 98 64 128 256), good := (rows 37 352 13 61 176 96 96 128 256) },{ target := 7, region := (rows 9 2 12 8 16 98 64 0 256), good := (rows 37 354 13 63 48 96 96 0 256) }] }

theorem u27226 : Upper (D 7) (R 7) [36,320,9,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27227 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 13 26 176 160 67 195 323), lower := (rows 37 322 13 26 176 160 64 128 256), losses := [] }

theorem u27227 : Upper (D 7) (R 7) [36,320,9,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27228 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 13 26 208 33 226 162 418), lower := (rows 37 322 13 26 208 33 64 128 256), losses := [] }

theorem u27228 : Upper (D 7) (R 7) [36,320,9,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27229 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 26 208 34 225 161 417), lower := (rows 37 322 13 26 208 34 64 128 256), losses := [] }

theorem u27229 : Upper (D 7) (R 7) [36,320,9,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27230 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(2,6)], upper := (rows 37 322 13 26 208 160 99 163 291), lower := (rows 37 322 13 26 208 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 320 13 61 240 160 64 160 256) }] }

theorem u27230 : Upper (D 7) (R 7) [36,320,9,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27231 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 88 50 33 194 130 386), lower := (rows 37 322 13 88 50 33 64 128 256), losses := [] }

theorem u27231 : Upper (D 7) (R 7) [36,320,9,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27232 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 13 88 50 34 193 129 385), lower := (rows 37 322 13 88 50 34 64 128 256), losses := [] }

theorem u27232 : Upper (D 7) (R 7) [36,320,9,80,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27233 : Route 9 := (fun mask => (mask,id))

def c27233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27233 : Upper (D 7) (R 7) [36,320,9,80,34,128] 13 := by
  apply FastRouting.sound _ _ [36,320,9,80,34,128] 13 (by decide) (choices 1) [1,2,128] r27233 c27233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9985
  · exact u9986
  · exact u9987

def r27234 : Route 9 := (fun mask => (mask,id))

def c27234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27234 : Upper (D 7) (R 7) [36,320,9,80,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,9,80,129,2] 13 (by decide) (choices 1) [2,32,128] r27234 c27234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9988
  · exact u9989
  · exact u9990

def b27235 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 322 13 88 145 160 98 162 290), lower := (rows 37 322 13 88 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 320 13 125 177 160 64 160 256) }] }

theorem u27235 : Upper (D 7) (R 7) [36,320,9,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27236 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 88 146 33 226 162 418), lower := (rows 37 322 13 88 146 33 64 128 256), losses := [] }

theorem u27236 : Upper (D 7) (R 7) [36,320,9,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27237 : PairBound 9 := { available := 161, camps := [], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 88 146 34 225 161 417), lower := (rows 37 322 13 88 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 137 265), good := (rows 421 290 397 445 178 34 0 128 256) },{ target := 7, region := (rows 9 2 12 8 16 50 64 0 256), good := (rows 37 354 13 125 50 34 64 0 256) }] }

theorem u27237 : Upper (D 7) (R 7) [36,320,9,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27238 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(2,1)], upper := (rows 37 322 13 88 146 160 99 163 291), lower := (rows 37 322 13 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 320 13 125 176 160 64 160 256) },{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 37 258 13 61 178 160 0 160 256) }] }

theorem u27238 : Upper (D 7) (R 7) [36,320,9,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27239 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 88 176 33 194 130 386), lower := (rows 37 322 13 88 176 33 64 128 256), losses := [] }

theorem u27239 : Upper (D 7) (R 7) [36,320,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27239
end Delivery.IrregularNine14.P07
