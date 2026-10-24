import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0010

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8160 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 261 138 208 40 80 131 259), lower := (rows 37 98 261 138 208 40 80 128 256), losses := [] }

theorem u8160 : Upper (D 7) (R 7) [36,96,257,130,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8160 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8161 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 262 11 81 160 72 144 400), lower := (rows 37 98 262 11 81 160 72 128 256), losses := [] }

theorem u8161 : Upper (D 7) (R 7) [36,96,258,3,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8161 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8162 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 262 11 81 160 80 136 392), lower := (rows 37 98 262 11 81 160 80 128 256), losses := [] }

theorem u8162 : Upper (D 7) (R 7) [36,96,258,3,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8162 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8163 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 262 11 81 160 192 152 280), lower := (rows 37 98 262 11 81 160 192 128 256), losses := [] }

theorem u8163 : Upper (D 7) (R 7) [36,96,258,3,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8164 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,7)], upper := (rows 37 98 262 11 88 160 65 144 400), lower := (rows 37 98 262 11 88 160 65 128 256), losses := [] }

theorem u8164 : Upper (D 7) (R 7) [36,96,258,3,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8165 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 262 11 88 160 80 129 385), lower := (rows 37 98 262 11 88 160 80 128 256), losses := [] }

theorem u8165 : Upper (D 7) (R 7) [36,96,258,3,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8165 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8166 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 262 11 88 160 192 145 273), lower := (rows 37 98 262 11 88 160 192 128 256), losses := [] }

theorem u8166 : Upper (D 7) (R 7) [36,96,258,3,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8167 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 262 11 145 160 72 208 336), lower := (rows 37 98 262 11 145 160 72 128 256), losses := [] }

theorem u8167 : Upper (D 7) (R 7) [36,96,258,3,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8167 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8168 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 262 11 145 160 80 200 328), lower := (rows 37 98 262 11 145 160 80 128 256), losses := [] }

theorem u8168 : Upper (D 7) (R 7) [36,96,258,3,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8168 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8169 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 262 11 152 160 65 208 336), lower := (rows 37 98 262 11 152 160 65 128 256), losses := [] }

theorem u8169 : Upper (D 7) (R 7) [36,96,258,3,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8170 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 262 11 152 160 80 193 321), lower := (rows 37 98 262 11 152 160 80 128 256), losses := [] }

theorem u8170 : Upper (D 7) (R 7) [36,96,258,3,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8170 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8171 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,7)], upper := (rows 37 98 262 25 26 160 65 192 448), lower := (rows 37 98 262 25 26 160 65 128 256), losses := [] }

theorem u8171 : Upper (D 7) (R 7) [36,96,258,17,10,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8172 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 262 25 26 160 192 193 321), lower := (rows 37 98 262 25 26 160 192 128 256), losses := [] }

theorem u8172 : Upper (D 7) (R 7) [36,96,258,17,10,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8173 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 37 98 262 25 88 160 65 130 386), lower := (rows 37 98 262 25 88 160 65 128 256), losses := [] }

theorem u8173 : Upper (D 7) (R 7) [36,96,258,17,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8174 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 262 25 88 160 66 129 385), lower := (rows 37 98 262 25 88 160 66 128 256), losses := [] }

theorem u8174 : Upper (D 7) (R 7) [36,96,258,17,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8175 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 262 25 88 160 192 131 259), lower := (rows 37 98 262 25 88 160 192 128 256), losses := [] }

theorem u8175 : Upper (D 7) (R 7) [36,96,258,17,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8176 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 262 25 146 33 72 192 448), lower := (rows 37 98 262 25 146 33 72 128 256), losses := [] }

theorem u8176 : Upper (D 7) (R 7) [36,96,258,17,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8176 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8177 : Route 9 := (fun mask => (mask,id))

def c8177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8177 : Upper (D 7) (R 7) [36,96,258,17,130,1,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,130,1,128] 13 (by decide) (choices 1) [8,64] r8177 c8177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u652
  · exact u653

def b8178 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 262 25 146 40 65 192 448), lower := (rows 37 98 262 25 146 40 65 128 256), losses := [] }

theorem u8178 : Upper (D 7) (R 7) [36,96,258,17,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8178 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8179 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 262 25 146 40 192 193 321), lower := (rows 37 98 262 25 146 40 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 40 208 128 256), good := (rows 36 98 262 122 210 42 192 192 256) }] }

theorem u8179 : Upper (D 7) (R 7) [36,96,258,17,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8179 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8180 : Route 9 := (fun mask => (mask,id))

def c8180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8180 : Upper (D 7) (R 7) [36,96,258,17,130,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,130,128,1] 13 (by decide) (choices 1) [8,64] r8180 c8180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u654
  · exact u655

def b8181 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 262 25 146 160 72 193 321), lower := (rows 37 98 262 25 146 160 72 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 72 128 256), good := (rows 36 98 262 122 178 160 74 160 256) }] }

theorem u8181 : Upper (D 7) (R 7) [36,96,258,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8181 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8182 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 262 25 152 160 65 194 322), lower := (rows 37 98 262 25 152 160 65 128 256), losses := [] }

theorem u8182 : Upper (D 7) (R 7) [36,96,258,17,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8183 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 262 25 152 160 66 193 321), lower := (rows 37 98 262 25 152 160 66 128 256), losses := [] }

theorem u8183 : Upper (D 7) (R 7) [36,96,258,17,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8184 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 98 262 25 208 33 66 136 392), lower := (rows 37 98 262 25 208 33 66 128 256), losses := [] }

theorem u8184 : Upper (D 7) (R 7) [36,96,258,17,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8185 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 262 25 208 33 72 130 386), lower := (rows 37 98 262 25 208 33 72 128 256), losses := [] }

theorem u8185 : Upper (D 7) (R 7) [36,96,258,17,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8185 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8186 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 262 25 208 33 192 138 266), lower := (rows 37 98 262 25 208 33 192 128 256), losses := [] }

theorem u8186 : Upper (D 7) (R 7) [36,96,258,17,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8187 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 262 25 208 40 65 130 386), lower := (rows 37 98 262 25 208 40 65 128 256), losses := [] }

theorem u8187 : Upper (D 7) (R 7) [36,96,258,17,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8187 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8188 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 262 25 208 40 66 129 385), lower := (rows 37 98 262 25 208 40 66 128 256), losses := [] }

theorem u8188 : Upper (D 7) (R 7) [36,96,258,17,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8188 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8189 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 262 25 208 40 192 131 259), lower := (rows 37 98 262 25 208 40 192 128 256), losses := [] }

theorem u8189 : Upper (D 7) (R 7) [36,96,258,17,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8189 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8190 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 37 98 262 25 208 160 65 138 266), lower := (rows 37 98 262 25 208 160 65 128 256), losses := [{ target := 0, region := (rows 0 18 12 8 16 184 64 136 264), good := (rows 36 98 262 446 242 160 64 160 256) },{ target := 7, region := (rows 1 3 12 8 16 32 73 0 264), good := (rows 103 98 262 351 80 32 67 0 256) }] }

theorem u8190 : Upper (D 7) (R 7) [36,96,258,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8191 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,5),(4,0)], upper := (rows 37 98 262 25 208 160 66 137 265), lower := (rows 37 98 262 25 208 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 70 137 265), good := (rows 477 66 326 409 208 128 66 128 256) }] }

theorem u8191 : Upper (D 7) (R 7) [36,96,258,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8192 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 64 },{ cop := 1, region := 261, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 98 262 25 208 160 72 131 259), lower := (rows 37 98 262 25 208 160 72 128 256), losses := [] }

theorem u8192 : Upper (D 7) (R 7) [36,96,258,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8192 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8193 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,7)], upper := (rows 37 98 262 26 81 160 65 136 392), lower := (rows 37 98 262 26 81 160 65 128 256), losses := [] }

theorem u8193 : Upper (D 7) (R 7) [36,96,258,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8194 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 262 26 81 160 72 129 385), lower := (rows 37 98 262 26 81 160 72 128 256), losses := [] }

theorem u8194 : Upper (D 7) (R 7) [36,96,258,18,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8194 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8195 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 262 26 81 160 192 137 265), lower := (rows 37 98 262 26 81 160 192 128 256), losses := [] }

theorem u8195 : Upper (D 7) (R 7) [36,96,258,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8196 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(2,5),(2,7),(3,7)], upper := (rows 37 98 262 26 145 160 65 200 328), lower := (rows 37 98 262 26 145 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 81 136 264), good := (rows 69 66 262 478 209 128 65 128 256) },{ target := 7, region := (rows 1 3 28 24 16 32 81 0 280), good := (rows 103 98 262 350 351 32 67 0 256) }] }

theorem u8196 : Upper (D 7) (R 7) [36,96,258,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8197 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 261, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 262 26 145 160 72 193 321), lower := (rows 37 98 262 26 145 160 72 128 256), losses := [] }

theorem u8197 : Upper (D 7) (R 7) [36,96,258,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8197 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8198 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 2 }], pairs := [(1,7),(3,7),(4,1)], upper := (rows 37 98 262 73 145 48 66 136 392), lower := (rows 37 98 262 73 145 48 66 128 256), losses := [] }

theorem u8198 : Upper (D 7) (R 7) [36,96,258,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8198 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8199 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 262 73 145 48 72 130 386), lower := (rows 37 98 262 73 145 48 72 128 256), losses := [] }

theorem u8199 : Upper (D 7) (R 7) [36,96,258,65,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8199 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8200 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 262 73 145 48 192 138 266), lower := (rows 37 98 262 73 145 48 192 128 256), losses := [] }

theorem u8200 : Upper (D 7) (R 7) [36,96,258,65,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8200 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8201 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 66 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 37 98 262 73 145 160 66 152 280), lower := (rows 37 98 262 73 145 160 66 128 256), losses := [] }

theorem u8201 : Upper (D 7) (R 7) [36,96,258,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8202 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 262 73 145 160 72 146 274), lower := (rows 37 98 262 73 145 160 72 128 256), losses := [] }

theorem u8202 : Upper (D 7) (R 7) [36,96,258,65,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8202 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8203 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 262 73 145 160 80 138 266), lower := (rows 37 98 262 73 145 160 80 128 256), losses := [] }

theorem u8203 : Upper (D 7) (R 7) [36,96,258,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8203 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8204 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 262 73 146 48 65 136 392), lower := (rows 37 98 262 73 146 48 65 128 256), losses := [] }

theorem u8204 : Upper (D 7) (R 7) [36,96,258,65,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8204 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8205 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 262 73 146 48 72 129 385), lower := (rows 37 98 262 73 146 48 72 128 256), losses := [] }

theorem u8205 : Upper (D 7) (R 7) [36,96,258,65,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8205 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8206 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 262 73 146 48 192 137 265), lower := (rows 37 98 262 73 146 48 192 128 256), losses := [] }

theorem u8206 : Upper (D 7) (R 7) [36,96,258,65,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8206 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8207 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 98 262 73 146 160 65 152 280), lower := (rows 37 98 262 73 146 160 65 128 256), losses := [] }

theorem u8207 : Upper (D 7) (R 7) [36,96,258,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8208 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 262 73 146 160 72 145 273), lower := (rows 37 98 262 73 146 160 72 128 256), losses := [] }

theorem u8208 : Upper (D 7) (R 7) [36,96,258,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8208 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8209 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 262 73 146 160 80 137 265), lower := (rows 37 98 262 73 146 160 80 128 256), losses := [] }

theorem u8209 : Upper (D 7) (R 7) [36,96,258,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8209 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8210 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 262 73 152 48 65 130 386), lower := (rows 37 98 262 73 152 48 65 128 256), losses := [] }

theorem u8210 : Upper (D 7) (R 7) [36,96,258,65,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8210 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8211 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,7),(3,7)], upper := (rows 37 98 262 73 152 48 66 129 385), lower := (rows 37 98 262 73 152 48 66 128 256), losses := [] }

theorem u8211 : Upper (D 7) (R 7) [36,96,258,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8211 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8212 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 262 73 152 48 192 131 259), lower := (rows 37 98 262 73 152 48 192 128 256), losses := [] }

theorem u8212 : Upper (D 7) (R 7) [36,96,258,65,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8212 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8213 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 98 262 73 152 160 65 146 274), lower := (rows 37 98 262 73 152 160 65 128 256), losses := [] }

theorem u8213 : Upper (D 7) (R 7) [36,96,258,65,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8214 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 66 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 37 98 262 73 152 160 66 145 273), lower := (rows 37 98 262 73 152 160 66 128 256), losses := [] }

theorem u8214 : Upper (D 7) (R 7) [36,96,258,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8215 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 262 73 152 160 80 131 259), lower := (rows 37 98 262 73 152 160 80 128 256), losses := [] }

theorem u8215 : Upper (D 7) (R 7) [36,96,258,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8215 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8216 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 160 }], pairs := [(1,0),(2,0),(3,5),(3,7)], upper := (rows 37 98 262 88 145 160 65 138 266), lower := (rows 37 98 262 88 145 160 65 128 256), losses := [] }

theorem u8216 : Upper (D 7) (R 7) [36,96,258,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8217 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(3,5)], upper := (rows 37 98 262 88 145 160 66 137 265), lower := (rows 37 98 262 88 145 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 70 145 273), good := (rows 477 66 326 472 409 128 66 128 256) }] }

theorem u8217 : Upper (D 7) (R 7) [36,96,258,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8218 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 262 88 145 160 72 131 259), lower := (rows 37 98 262 88 145 160 72 128 256), losses := [] }

theorem u8218 : Upper (D 7) (R 7) [36,96,258,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8218 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8219 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 262 88 146 33 65 136 392), lower := (rows 37 98 262 88 146 33 65 128 256), losses := [] }

theorem u8219 : Upper (D 7) (R 7) [36,96,258,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8219
end Delivery.IrregularNine14.P07
